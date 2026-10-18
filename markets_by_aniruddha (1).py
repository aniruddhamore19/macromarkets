"""
Markets By Aniruddha
====================
Live markets terminal as a local app (no Excel needed).

Run from Anaconda PowerShell:
    conda activate base
    python markets_by_aniruddha.py

Refresh rates: prices 5s | news 10s | OI/PCR 5s | FII/DII 60s | calendar actuals 5m (full rebuild 1h)
"""
from __future__ import annotations

import functools
import hmac
import json
import logging
import math
import os
import struct
import subprocess
import threading
import time
import warnings
import webbrowser
import zlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timedelta, timezone
from typing import Any

import pandas as pd
import requests
import yfinance as yf
from bs4 import BeautifulSoup
from flask import Flask, Response, redirect, request
from tradingview_screener import Query, col

warnings.filterwarnings("ignore")

APP_NAME = "Markets By Aniruddha"
# Hosting platforms (Render, Railway, ...) set PORT automatically -> app runs in "hosted" mode:
# listens publicly, no desktop window. On your own PC it behaves exactly as before.
# Hosted = any cloud platform (PORT/RENDER env set) or any non-Windows machine. Your Windows PC stays local.
HOSTED = bool(os.environ.get("PORT") or os.environ.get("RENDER")) or os.name != "nt"
HOST = "0.0.0.0" if HOSTED else "127.0.0.1"
PORT = int(os.environ.get("PORT") or (10000 if HOSTED else 8765))
ACCESS_CODE = os.environ.get("ACCESS_CODE", "")  # set this when hosting so only your friends get in
IST = timedelta(hours=5, minutes=30)

INTERVALS = {"prices": 5, "news": 10, "oi": 5, "fii": 60, "calendar": 300}
CALENDAR_FULL_EVERY = 3600

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "en-US,en;q=0.9",
    "Accept": "application/json, text/plain, */*",
}

MONTH_NUM_TO_CODE = {1: "F", 2: "G", 3: "H", 4: "J", 5: "K", 6: "M",
                     7: "N", 8: "Q", 9: "U", 10: "V", 11: "X", 12: "Z"}
MARKET_QUERY_GROUPS = ("futures", "india", "forex", "cfd")

# yfinance ^TNX already reports the yield in percent, so no scaling.
PRICE_STATIC_FALLBACKS = {
    "DXY": {"yf_symbol": "DX-Y.NYB", "scale": 1.0},
    "US10Y": {"yf_symbol": "^TNX", "scale": 1.0},
}


def _utcnow() -> datetime:
    return datetime.now(timezone.utc).replace(tzinfo=None)


def _now() -> datetime:
    """Current IST time (cloud servers run in UTC, so never rely on the machine's local clock)."""
    return _utcnow() + IST


def to_naive(dt: Any) -> datetime:
    if isinstance(dt, datetime):
        if dt.tzinfo is not None:
            dt = dt.astimezone(timezone.utc).replace(tzinfo=None)
        return dt
    return _utcnow()


def parse_pub_date(s: str) -> datetime:
    for fmt in ("%a, %d %b %Y %H:%M:%S %Z", "%a, %d %b %Y %H:%M:%S %z",
                "%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%M:%S"):
        try:
            return to_naive(datetime.strptime((s or "").strip(), fmt))
        except Exception:
            continue
    return _utcnow()


def to_float(value: Any) -> float | None:
    try:
        text = str(value).replace(",", "").replace("₹", "").strip()
        if text in ("", "-", "N/A", "None"):
            return None
        return float(text)
    except Exception:
        return None


# ───────────────────────────── PRICES ─────────────────────────────
ALL_M = list(range(1, 13))


def _c(label, root, hint, months, offset):
    return {"label": label, "kind": "contract", "root": root, "exchange_hint": hint,
            "valid_months": months, "offset": offset}


WATCHLIST_CONFIG = [
    _c("COMEX Gold Near", "GC", "COMEX", ALL_M, 0),
    _c("COMEX Gold Far", "GC", "COMEX", ALL_M, 1),
    _c("COMEX Silver Near", "SI", "COMEX", ALL_M, 0),
    _c("COMEX Silver Far", "SI", "COMEX", ALL_M, 1),
    _c("LME Copper Near", "CA", "LME", ALL_M, 0),
    _c("LME Copper Far", "CA", "LME", ALL_M, 1),
    _c("MCX Gold Near", "GOLD", "MCX", [2, 4, 6, 8, 10, 12], 0),
    _c("MCX Gold Far", "GOLD", "MCX", [2, 4, 6, 8, 10, 12], 1),
    _c("MCX Silver Near", "SILVER", "MCX", [3, 5, 7, 9, 12], 0),
    _c("MCX Silver Far", "SILVER", "MCX", [3, 5, 7, 9, 12], 1),
    _c("MCX Copper Near", "COPPER", "MCX", ALL_M, 0),
    _c("MCX Copper Far", "COPPER", "MCX", ALL_M, 1),
    _c("USDINR Near", "USDINR", ("MSEI", "NSE"), ALL_M, 0),
    _c("USDINR Far", "USDINR", ("MSEI", "NSE"), ALL_M, 1),
    {"label": "Dollar Index", "kind": "static", "symbol": "DXY", "exchange_hint": "TVC"},
    {"label": "US 10Y Yield", "kind": "static", "symbol": "US10Y", "exchange_hint": "TVC"},
]


def generate_contract_symbols(root: str, valid_months: list[int], years_forward: int = 2) -> list[str]:
    today = _now()
    out: list[str] = []
    for year in range(today.year, today.year + years_forward + 1):
        for month in valid_months:
            if year == today.year and month < today.month:
                continue
            out.append(f"{root}{MONTH_NUM_TO_CODE[month]}{year}")
    return out


def build_watchlist_specs() -> list[dict[str, Any]]:
    specs = []
    for config in WATCHLIST_CONFIG:
        spec = dict(config)
        if spec["kind"] == "contract":
            generated = generate_contract_symbols(spec["root"], spec["valid_months"], 2)
            offset = int(spec["offset"])
            spec["candidates"] = generated[offset:offset + 4]
        else:
            spec["candidates"] = [spec["symbol"]]
        specs.append(spec)
    return specs


def fetch_yfinance_snapshot(yf_symbol: str, scale: float = 1.0) -> tuple[float, float | None]:
    ticker = yf.Ticker(yf_symbol)
    price = None
    change_pct = None
    try:
        fast = getattr(ticker, "fast_info", None)
        if fast:
            price = fast.get("lastPrice") or fast.get("last_price")
            prev = fast.get("previousClose") or fast.get("previous_close")
            if price is not None and prev not in (None, 0):
                change_pct = (float(price) - float(prev)) / float(prev) * 100.0
    except Exception:
        pass
    if price is None:
        hist = ticker.history(period="2d", interval="1d")
        if hist.empty:
            raise ValueError(f"No yfinance data for {yf_symbol}")
        price = hist["Close"].iloc[-1]
        if len(hist) >= 2 and hist["Close"].iloc[-2] not in (None, 0):
            change_pct = (float(price) - float(hist["Close"].iloc[-2])) / float(hist["Close"].iloc[-2]) * 100.0
    return round(float(price) * scale, 4), (round(float(change_pct), 4) if change_pct is not None else None)


def fetch_tradingview_rows(symbols: list[str]) -> pd.DataFrame:
    data = (Query().set_markets(*MARKET_QUERY_GROUPS)
            .select("name", "description", "close", "change", "exchange")
            .where(col("name").isin(symbols)).get_scanner_data())
    return data[1].copy()


def filter_exchange_matches(raw_df: pd.DataFrame, hint: Any) -> pd.DataFrame:
    if raw_df.empty or not hint:
        return raw_df
    hints = hint if isinstance(hint, (list, tuple, set)) else [hint]
    mask = pd.Series(False, index=raw_df.index)
    for h in hints:
        mask = mask | raw_df["exchange"].astype(str).str.contains(str(h), case=False, na=False)
    return raw_df[mask]


def _row_from_match(spec, row: pd.Series, fallback: str) -> dict[str, Any]:
    return {"Watchlist": spec["label"], "Ticker": row.get("name", fallback),
            "Description": row.get("description", spec["label"]), "Price": row.get("close"),
            "Chg %": row.get("change"), "Exchange": row.get("exchange", spec.get("exchange_hint", "")),
            "Timestamp": _now().strftime("%H:%M:%S"), "Status": "OK"}


def _missing_row(spec) -> dict[str, Any]:
    hint = spec.get("exchange_hint", "")
    return {"Watchlist": spec["label"], "Ticker": spec["candidates"][0], "Description": spec["label"],
            "Price": None, "Chg %": None, "Exchange": hint if isinstance(hint, str) else "/".join(hint),
            "Timestamp": _now().strftime("%H:%M:%S"), "Status": "Missing"}


def resolve_static_row(raw_df: pd.DataFrame, spec) -> dict[str, Any]:
    filtered = filter_exchange_matches(raw_df, spec.get("exchange_hint"))
    for cand in spec["candidates"]:
        match = filtered[filtered["name"] == cand] if not filtered.empty else pd.DataFrame()
        if not match.empty:
            return _row_from_match(spec, match.iloc[0], cand)
    fb = PRICE_STATIC_FALLBACKS.get(spec.get("symbol", ""))
    if fb:
        try:
            price, chg = fetch_yfinance_snapshot(fb["yf_symbol"], fb["scale"])
            return {"Watchlist": spec["label"], "Ticker": spec["symbol"], "Description": spec["label"],
                    "Price": price, "Chg %": chg, "Exchange": "yfinance",
                    "Timestamp": _now().strftime("%H:%M:%S"), "Status": "OK"}
        except Exception:
            pass
    return _missing_row(spec)


def contract_group_key(spec) -> tuple:
    hint = spec.get("exchange_hint")
    hint = tuple(str(i) for i in hint) if isinstance(hint, (list, tuple, set)) else (str(hint),)
    return (spec.get("root"), tuple(spec.get("valid_months", [])), hint)


def resolve_contract_group(raw_df: pd.DataFrame, specs) -> dict[str, dict[str, Any]]:
    anchor = specs[0]
    full = generate_contract_symbols(str(anchor["root"]), list(anchor["valid_months"]), 2)
    filtered = filter_exchange_matches(raw_df, anchor.get("exchange_hint"))
    available, seen = [], set()
    for cand in full:
        match = filtered[filtered["name"] == cand] if not filtered.empty else pd.DataFrame()
        if match.empty or cand in seen:
            continue
        seen.add(cand)
        available.append((cand, match.iloc[0]))
    out = {}
    for spec in sorted(specs, key=lambda s: int(s.get("offset", 0))):
        off = int(spec.get("offset", 0))
        out[spec["label"]] = (_row_from_match(spec, available[off][1], available[off][0])
                              if off < len(available) else _missing_row(spec))
    return out


def prices_job() -> list[dict[str, Any]]:
    specs = build_watchlist_specs()
    symbols = sorted({s for spec in specs for s in spec["candidates"]})
    raw_df, tv_error = pd.DataFrame(), ""
    try:
        raw_df = fetch_tradingview_rows(symbols)
    except Exception as exc:
        tv_error = f"TradingView: {exc}"
    resolved: dict[str, dict[str, Any]] = {}
    groups: dict[tuple, list] = {}
    for spec in specs:
        if spec["kind"] == "contract":
            groups.setdefault(contract_group_key(spec), []).append(spec)
        else:
            resolved[spec["label"]] = resolve_static_row(raw_df, spec)
    for grp in groups.values():
        resolved.update(resolve_contract_group(raw_df, grp))
    rows = [resolved.get(s["label"], _missing_row(s)) for s in specs]
    if all(r["Status"] != "OK" for r in rows):
        raise RuntimeError(tv_error or "No prices returned")
    return rows


# ───────────────────────────── NEWS ─────────────────────────────
BREAKING_KEYWORDS = [
    "rate cut", "rate hike", "emergency", "war", "attack", "sanctions", "opec cut", "opec hike",
    "fed pivot", "rbi rate", "surprise", "shock", "crash", "collapse", "default", "ban", "nuclear",
    "ceasefire", "escalat", "missile", "explosion", "tariff hike", "gold record", "silver record",
    "crude spike", "oil ban",
]
NEWS_FEEDS = [
    ("TOI", "https://timesofindia.indiatimes.com/rssfeeds/1898055.cms"),
    ("Mint", "https://www.livemint.com/rss/markets"),
    ("Mint", "https://www.livemint.com/rss/economy"),
    ("Reuters", "https://feeds.reuters.com/reuters/businessNews"),
    ("Reuters", "https://feeds.reuters.com/reuters/companyNews"),
    ("Guardian", "https://www.theguardian.com/business/rss"),
    ("GNews", "https://news.google.com/rss/search?q=MCX+gold+silver+copper+USDINR+DXY+US10Y&hl=en-IN&gl=IN&ceid=IN:en"),
]
COMMODITY_KW = ["gold", "silver", "copper", "mcx", "comex", "lme", "usdinr", "rupee", "dollar", "dxy",
                "us 10y", "treasury", "yield", "rbi", "fed", "fomc", "inflation", "cpi", "rate",
                "bullion", "metal", "tariff", "trade"]

_news_store: list[dict[str, Any]] = []
_seen_headlines: set[str] = set()


def fetch_feed_items(source: str, url: str) -> list[dict[str, Any]]:
    items = []
    try:
        resp = requests.get(url, headers=HEADERS, timeout=5)
        soup = BeautifulSoup(resp.content, "xml")
        for item in soup.find_all("item"):
            title = item.find("title")
            headline = (title.text if title else "").strip()
            if not headline or not any(k in headline.lower() for k in COMMODITY_KW):
                continue
            link_tag = item.find("link")
            link = link_tag.get_text().strip() if link_tag else ""
            pub = item.find("pubDate")
            dt_obj = parse_pub_date(pub.text if pub else "")
            brk = any(k in headline.lower() for k in BREAKING_KEYWORDS)
            items.append({"Source": source, "Headline": headline, "Link": link, "dt_obj": dt_obj,
                          "Breaking": "BREAKING" if brk else ""})
    except Exception:
        return []
    return items


def news_job() -> list[dict[str, Any]]:
    with ThreadPoolExecutor(max_workers=6) as ex:
        futures = [ex.submit(fetch_feed_items, s, u) for s, u in NEWS_FEEDS]
        for fut in as_completed(futures):
            try:
                for entry in fut.result():
                    key = entry["Headline"][:120]
                    if key not in _seen_headlines:
                        _seen_headlines.add(key)
                        _news_store.append(entry)
            except Exception:
                continue
    _news_store.sort(key=lambda e: e["dt_obj"], reverse=True)
    del _news_store[300:]
    if not _news_store:
        raise RuntimeError("No headlines fetched")
    return [{"Time": (e["dt_obj"] + IST).strftime("%d-%m-%Y %H:%M"), "Source": e["Source"],
             "Breaking": e["Breaking"], "Headline": e["Headline"], "Link": e["Link"]}
            for e in _news_store[:250]]


# ───────────────────────────── FII / DII ─────────────────────────────
def _make_nse_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({**HEADERS, "Referer": "https://www.nseindia.com/", "Origin": "https://www.nseindia.com"})
    try:
        s.get("https://www.nseindia.com", timeout=12)
        time.sleep(1.0)
        s.get("https://www.nseindia.com/market-data/live-equity-market", timeout=10)
        time.sleep(0.5)
    except Exception:
        pass
    return s


def _fetch_nse_fii(session: requests.Session) -> list[dict[str, Any]]:
    resp = session.get("https://www.nseindia.com/api/fiidiiTradeReact",
                       headers={**HEADERS, "Referer": "https://www.nseindia.com/"}, timeout=15)
    resp.raise_for_status()
    payload = resp.json()
    if not isinstance(payload, list) or not payload:
        raise ValueError("NSE FII API returned empty data")
    return [{"Date": e.get("date", ""), "Category": e.get("category", ""), "Buy (Cr)": e.get("buyValue", 0),
             "Sell (Cr)": e.get("sellValue", 0), "Net (Cr)": e.get("netValue", 0)} for e in payload]


def _fetch_moneycontrol_fii() -> list[dict[str, Any]]:
    resp = requests.get("https://www.moneycontrol.com/stocks/marketstats/fii_dii_activity/index.php",
                        headers=HEADERS, timeout=12)
    soup = BeautifulSoup(resp.content, "html.parser")
    table = soup.find("table", {"class": "tbldata14"})
    rows = []
    if not table:
        return rows
    for tr in table.find_all("tr")[1:15]:
        cells = [td.get_text(strip=True) for td in tr.find_all("td")]
        if len(cells) >= 5:
            rows.append({"Date": cells[0], "Category": cells[1], "Buy (Cr)": cells[2],
                         "Sell (Cr)": cells[3], "Net (Cr)": cells[4]})
    return rows


def fii_job() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    try:
        rows = _fetch_nse_fii(_make_nse_session())
    except Exception:
        try:
            rows = _fetch_moneycontrol_fii()
        except Exception:
            rows = []
    if not rows:
        raise RuntimeError("NSE and MoneyControl unavailable")
    for r in rows:
        for k in ("Buy (Cr)", "Sell (Cr)", "Net (Cr)"):
            v = to_float(r[k])
            r[k] = v if v is not None else r[k]
    return rows


# ───────────────────────────── ECO CALENDAR ─────────────────────────────
CAL_KW = ["gdp", "cpi", "inflation", "interest rate", "fed", "fomc", "rbi", "mpc", "non-farm", "nfp",
          "unemployment", "jobless", "pmi", "retail sales", "industrial production", "trade balance",
          "pce", "adp", "housing", "consumer confidence", "manufacturing", "services", "central bank",
          "monetary policy", "repo rate", "payroll", "jobs", "employment", "michigan", "philadelphia",
          "building permits", "wpi", "iip", "core", "balance of trade", "current account", "budget", "nonfarm"]
_calendar_cache: dict[str, list[dict[str, Any]]] = {"last": [], "this": [], "next": []}


def _cal_ok(text: str) -> bool:
    return any(k in text.lower() for k in CAL_KW)


def get_week_bounds():
    today = _now().date()
    monday = today - timedelta(days=today.weekday())
    return (monday - timedelta(days=7), monday - timedelta(days=1), monday,
            monday + timedelta(days=6), monday + timedelta(days=7), monday + timedelta(days=13))


def _fetch_ff(suffix: str) -> list[dict[str, Any]]:
    try:
        resp = requests.get(f"https://nfs.faireconomy.media/ff_calendar_{suffix}.json",
                            headers={"User-Agent": "Mozilla/5.0"}, timeout=12)
        resp.raise_for_status()
        events = []
        for e in resp.json():
            title, country, impact = (e.get("title") or "").strip(), (e.get("country") or "").strip(), (e.get("impact") or "").strip()
            if country not in ("USD", "INR") or impact not in ("High", "Medium"):
                continue
            try:
                dt_obj = to_naive(datetime.fromisoformat(e.get("date", "")))
            except Exception:
                dt_obj = _utcnow()
            try:
                t_str = datetime.strptime((e.get("time") or "").strip(), "%I:%M%p").strftime("%H:%M") + " EST"
            except Exception:
                t_str = e.get("time") or "All Day"
            events.append({"Date": dt_obj.strftime("%d-%m-%Y"), "Time": t_str, "Country": country,
                           "Event": title, "Impact": "HIGH" if impact == "High" else "MEDIUM",
                           "Previous": (e.get("previous") or "-").strip() or "-",
                           "Forecast": (e.get("estimate") or "-").strip() or "-",
                           "Actual": (e.get("actual") or "-").strip() or "-",
                           "Link": "https://www.forexfactory.com/calendar", "_dt": dt_obj})
        return events
    except Exception:
        return []


def _fetch_investing_range(d_from: date, d_to: date) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    try:
        resp = requests.post(
            "https://in.investing.com/economic-calendar/Service/getCalendarFilteredData",
            headers={**HEADERS, "X-Requested-With": "XMLHttpRequest",
                     "Referer": "https://in.investing.com/economic-calendar/"},
            data={"country[]": ["5", "72"], "importance[]": ["2", "3"], "timeZone": "20",
                  "currentTab": "custom", "limit_from": "0",
                  "dateFrom": d_from.strftime("%Y-%m-%d"), "dateTo": d_to.strftime("%Y-%m-%d")},
            timeout=15)
        soup = BeautifulSoup(resp.json().get("data", ""), "html.parser")
        for row in soup.find_all("tr", class_="js-event-item"):
            try:
                dt_obj = to_naive(datetime.strptime(row.get("data-event-datetime", ""), "%Y/%m/%d %H:%M:%S"))
                name_td = row.find("td", class_="event")
                name = name_td.get_text(strip=True) if name_td else ""
                if not name or not _cal_ok(name):
                    continue
                impact = "HIGH" if len(row.find_all("i", class_="grayFullBullishIcon")) >= 3 else "MEDIUM"
                actual = forecast = previous = "-"
                country = ""
                for td in row.find_all("td"):
                    cls = " ".join(td.get("class", []))
                    val = td.get_text(strip=True) or "-"
                    if "actual" in cls:
                        actual = val
                    if "forecast" in cls:
                        forecast = val
                    if "prev" in cls:
                        previous = val
                    if "flagCur" in cls and td.get_text(strip=True):
                        country = td.get_text(strip=True)
                if not country:
                    low = name.lower()
                    country = "INR" if any(t in low for t in ["india", "rbi", "wpi", "iip", "rupee"]) else "USD"
                a = name_td.find("a") if name_td else None
                link = ("https://in.investing.com" + a["href"]) if a and a.get("href") else "https://in.investing.com/economic-calendar/"
                events.append({"Date": dt_obj.strftime("%d-%m-%Y"), "Time": dt_obj.strftime("%H:%M") + " IST",
                               "Country": country, "Event": name, "Impact": impact, "Previous": previous,
                               "Forecast": forecast, "Actual": actual, "Link": link, "_dt": dt_obj})
            except Exception:
                continue
    except Exception:
        return events
    return events


def _bucket(events, start: date, end: date):
    seen, out = set(), []
    for e in events:
        key = f"{e['Date']}_{e['Event'][:30]}"
        if start <= e["_dt"].date() <= end and key not in seen:
            seen.add(key)
            out.append(e)
    out.sort(key=lambda i: i["_dt"])
    return out


def _merge_events(*groups):
    merged = [e for g in groups for e in g]
    seen: dict[str, dict[str, Any]] = {}
    for e in sorted(merged, key=lambda i: i.get("_dt", _utcnow())):
        key = f"{e.get('Date', '')}_{str(e.get('Event', ''))[:40]}"
        cur = seen.get(key)
        if cur is None or (cur.get("Actual", "-") in ("-", "", "N/A") and e.get("Actual", "-") not in ("-", "", "N/A")):
            seen[key] = e
    return sorted(seen.values(), key=lambda i: i.get("_dt", _utcnow()))


def _has_pending(bucket: str) -> bool:
    now = _utcnow()
    return any(e.get("Actual", "-") in ("-", "", "N/A") and e["_dt"] < now for e in _calendar_cache.get(bucket, []))


def fetch_economic_calendar(actuals_only: bool = False):
    global _calendar_cache
    lw0, lw1, tw0, tw1, nw0, nw1 = get_week_bounds()
    if not actuals_only:
        ff_this, ff_next = _fetch_ff("thisweek"), _fetch_ff("nextweek")
        inv_last, inv_this, inv_next = (_fetch_investing_range(lw0, lw1), _fetch_investing_range(tw0, tw1),
                                        _fetch_investing_range(nw0, nw1))
        this_ev = _merge_events(_bucket(ff_this, tw0, tw1), _bucket(inv_this, tw0, tw1))
        next_ev = _merge_events(_bucket(ff_next, nw0, nw1), _bucket(inv_next, nw0, nw1))
        if not next_ev:
            next_ev = _merge_events(_bucket(ff_this, nw0, nw1), _bucket(inv_next, nw0, nw1))
        _calendar_cache = {"last": _bucket(inv_last, lw0, lw1), "this": this_ev, "next": next_ev}
        return _calendar_cache

    need_last, need_this = _has_pending("last"), _has_pending("this")
    if not (need_last or need_this):
        return _calendar_cache
    fresh = _fetch_investing_range(lw0, tw1)
    ff_this = _bucket(_fetch_ff("thisweek"), tw0, tw1)

    def overlay(base, updates):
        umap = {i["Event"][:35]: i for i in updates if i.get("Actual", "-") not in ("-", "", "N/A")}
        for e in base:
            k = e["Event"][:35]
            if e.get("Actual", "-") in ("-", "", "N/A") and k in umap:
                e["Actual"] = umap[k]["Actual"]
                e["Previous"] = umap[k].get("Previous", e["Previous"])
        return base

    if need_last:
        _calendar_cache["last"] = overlay(_calendar_cache["last"], _bucket(fresh, lw0, lw1))
    if need_this:
        _calendar_cache["this"] = overlay(overlay(_calendar_cache["this"], _bucket(fresh, tw0, tw1)), ff_this)
    return _calendar_cache


_cal_last_full = [0.0]


def calendar_job():
    full = time.time() - _cal_last_full[0] >= CALENDAR_FULL_EVERY
    data = fetch_economic_calendar(actuals_only=not full)
    if not any(data.values()):
        raise RuntimeError("Calendar sources returned no events")
    if full:
        _cal_last_full[0] = time.time()
    return data


# ───────────────────────────── OI / PCR ─────────────────────────────
def _calc_oi(call_oi, put_oi, label, source):
    total_calls, total_puts = sum(call_oi.values()), sum(put_oi.values())
    pcr = round(total_puts / total_calls, 2) if total_calls else 0
    strikes = sorted(set(call_oi) | set(put_oi))
    pain = {s: sum(max(0, s - k) * v for k, v in call_oi.items()) + sum(max(0, k - s) * v for k, v in put_oi.items())
            for s in strikes}
    max_pain = min(pain, key=pain.get) if pain else "N/A"
    bias = "Bullish" if pcr > 1.2 else "Bearish" if pcr < 0.8 else "Neutral"
    rows = [{"type": "summary", "label": f"{label} [{source}]", "total_call_oi": total_calls,
             "total_put_oi": total_puts, "pcr": pcr, "max_pain": max_pain, "sentiment": bias}]
    top = sorted(strikes, key=lambda s: call_oi.get(s, 0) + put_oi.get(s, 0), reverse=True)[:8]
    for s in sorted(top):
        rows.append({"type": "strike", "strike": s, "call_oi": call_oi.get(s, 0), "put_oi": put_oi.get(s, 0),
                     "pcr": round(put_oi.get(s, 0) / max(call_oi.get(s, 1), 1), 2),
                     "max_pain": "MAX PAIN" if s == max_pain else ""})
    return rows


def _mcx_opstra(symbol: str):
    resp = requests.get(f"https://opstra.definedge.com/api/openinterest/optionchain/{symbol}",
                        headers={"User-Agent": "Mozilla/5.0", "Referer": "https://opstra.definedge.com",
                                 "Accept": "application/json"}, timeout=12)
    payload = resp.json()
    call_oi, put_oi = {}, {}
    for r in payload.get("data", payload.get("records", [])):
        strike = r.get("strike_price", r.get("strikePrice", 0))
        call_oi[strike] = r.get("call_oi", r.get("CE", {}).get("openInterest", 0))
        put_oi[strike] = r.get("put_oi", r.get("PE", {}).get("openInterest", 0))
    if not call_oi and not put_oi:
        raise ValueError("Empty Opstra response")
    return call_oi, put_oi


def _mcx_nse(symbol: str):
    s = requests.Session()
    s.get("https://www.nseindia.com", headers=HEADERS, timeout=10)
    time.sleep(1)
    resp = s.get(f"https://www.nseindia.com/api/option-chain-commodities?symbol={symbol}",
                 headers={**HEADERS, "Referer": "https://www.nseindia.com/market-data/option-chain",
                          "X-Requested-With": "XMLHttpRequest"}, timeout=15)
    resp.raise_for_status()
    records = resp.json().get("records", {}).get("data", [])
    if not records:
        raise ValueError("NSE commodity option chain empty")
    call_oi, put_oi = {}, {}
    for r in records:
        strike = r.get("strikePrice", 0)
        if "CE" in r:
            call_oi[strike] = r["CE"].get("openInterest", 0)
        if "PE" in r:
            put_oi[strike] = r["PE"].get("openInterest", 0)
    return call_oi, put_oi


def _unavailable(label: str, msg: str = "OI unavailable"):
    return {"type": "summary", "label": f"{label} [Unavailable]", "total_call_oi": "N/A",
            "total_put_oi": "N/A", "pcr": "N/A", "max_pain": "N/A", "sentiment": msg}


def fetch_mcx_oi():
    results = []
    for nse_sym, opstra_sym, label in [("GOLDM", "GOLD", "Gold"), ("SILVERM", "SILVER", "Silver"),
                                       ("COPPER", "COPPER", "Copper")]:
        done = False
        for fn, src, arg in [(_mcx_opstra, "Opstra", opstra_sym), (_mcx_nse, "NSE", nse_sym)]:
            try:
                call_oi, put_oi = fn(arg)
                results += _calc_oi(call_oi, put_oi, label, src)
                done = True
                break
            except Exception:
                continue
        if not done:
            results.append(_unavailable(label))
    return results


def fetch_comex_oi():
    results = []
    for symbol, label in [("GC=F", "COMEX Gold"), ("SI=F", "COMEX Silver")]:
        try:
            t = yf.Ticker(symbol)
            expiries = t.options
            if not expiries:
                raise ValueError(f"No options chain for {symbol}")
            chain = t.option_chain(expiries[0])
            if chain.calls.empty and chain.puts.empty:
                raise ValueError("Empty option chain")
            call_oi = dict(zip(chain.calls["strike"].tolist(), chain.calls["openInterest"].fillna(0).astype(int).tolist()))
            put_oi = dict(zip(chain.puts["strike"].tolist(), chain.puts["openInterest"].fillna(0).astype(int).tolist()))
            results += _calc_oi(call_oi, put_oi, label, f"yfinance/{expiries[0]}")
        except Exception as exc:
            results.append(_unavailable(label, str(exc)[:55]))
    return results


def oi_job():
    return ([{"type": "header", "label": "MCX OI / PCR"}] + fetch_mcx_oi()
            + [{"type": "header", "label": "COMEX OI / PCR"}] + fetch_comex_oi())


# ───────────────────────────── STATE + WORKERS ─────────────────────────────
JOBS = {"prices": prices_job, "news": news_job, "fii": fii_job, "calendar": calendar_job, "oi": oi_job}
LOCK = threading.Lock()
VERSION = [0]
STATE: dict[str, dict[str, Any]] = {
    k: {"data": None, "updated": None, "updated_ts": None, "ok": None, "error": ""} for k in JOBS
}


def clean(o: Any) -> Any:
    if isinstance(o, dict):
        return {str(k): clean(v) for k, v in o.items() if not str(k).startswith("_") and k != "dt_obj"}
    if isinstance(o, (list, tuple)):
        return [clean(v) for v in o]
    if hasattr(o, "item") and not isinstance(o, (str, bytes)):
        try:
            o = o.item()
        except Exception:
            pass
    if isinstance(o, float):
        return None if (math.isnan(o) or math.isinf(o)) else o
    if o is None or isinstance(o, (bool, int, str)):
        return o
    return str(o)


def worker(name: str) -> None:
    fn, interval = JOBS[name], INTERVALS[name]
    while True:
        t0 = time.time()
        try:
            data = clean(fn())
            with LOCK:
                STATE[name].update(data=data, updated=_now().strftime("%H:%M:%S"),
                                   updated_ts=time.time(), ok=True, error="")
                VERSION[0] += 1
        except Exception as exc:
            with LOCK:
                STATE[name].update(ok=False, error=str(exc)[:200])
                VERSION[0] += 1
        time.sleep(max(0.5, interval - (time.time() - t0)))


# ───────────────────────────── WEB APP ─────────────────────────────
app = Flask(__name__)
logging.getLogger("werkzeug").setLevel(logging.ERROR)


@app.route("/")
def index():
    return Response(PAGE, mimetype="text/html")


@app.route("/api/state")
def api_state():
    since = request.args.get("v", type=int, default=-1)
    with LOCK:
        if since == VERSION[0]:
            body = json.dumps({"v": VERSION[0], "same": True})
        else:
            body = json.dumps({"v": VERSION[0], "intervals": INTERVALS, "modules": STATE})
    return Response(body, mimetype="application/json", headers={"Cache-Control": "no-store"})


# ── access code (only active when ACCESS_CODE is set) ──
OPEN_PATHS = {"/login", "/healthz", "/manifest.webmanifest", "/icon-192.png", "/icon-512.png"}
LOGIN_PAGE = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Markets By Aniruddha</title>
<style>body{margin:0;min-height:100vh;display:grid;place-items:center;background:#090c11;color:#e7eaf0;font:15px "Segoe UI",system-ui,sans-serif}
form{width:min(340px,86vw);background:#0f141b;border:1px solid #212a36;border-radius:12px;padding:26px}
h1{margin:0 0 4px;font-size:15px;letter-spacing:.16em}small{display:block;color:#ffb000;letter-spacing:.24em;font-size:10px;margin-bottom:20px}
input{width:100%;padding:11px;border-radius:7px;border:1px solid #212a36;background:#151b25;color:#e7eaf0;font:inherit;margin-bottom:12px}
button{width:100%;padding:11px;border:0;border-radius:7px;background:#ffb000;color:#111;font:700 14px inherit;cursor:pointer}
p{color:#ff5d6c;margin:0 0 10px;min-height:1em;font-size:13px}</style></head><body>
<form method="post"><h1>MARKETS</h1><small>BY ANIRUDDHA</small><p>%MSG%</p>
<input type="password" name="code" placeholder="Access code" autofocus autocomplete="current-password"><button>Enter</button></form></body></html>"""


def _token() -> str:
    return hmac.new(ACCESS_CODE.encode(), b"mba-session", "sha256").hexdigest()


def _same(a: str, b: str) -> bool:
    return hmac.compare_digest(a.encode(), b.encode())


@app.before_request
def gate():
    if not ACCESS_CODE or request.path in OPEN_PATHS or _same(request.cookies.get("mba", ""), _token()):
        return None
    if request.path.startswith("/api/"):
        return Response("locked", 401)
    return redirect("/login")


@app.route("/login", methods=["GET", "POST"])
def login():
    bad = False
    if ACCESS_CODE and request.method == "POST":
        if _same(request.form.get("code", ""), ACCESS_CODE):
            resp = redirect("/")
            resp.set_cookie("mba", _token(), max_age=60 * 60 * 24 * 365, httponly=True, samesite="Lax",
                            secure=request.headers.get("X-Forwarded-Proto") == "https")
            return resp
        time.sleep(1)  # slow down guessing
        bad = True
    return Response(LOGIN_PAGE.replace("%MSG%", "Wrong code" if bad else ""), mimetype="text/html")


@app.route("/healthz")
def healthz():
    return Response("ok", mimetype="text/plain")


# ── installable web-app bits (so friends can "Install app" / "Add to Home screen") ──
@app.route("/manifest.webmanifest")
def manifest():
    icons = [{"src": f"/icon-{s}.png", "sizes": f"{s}x{s}", "type": "image/png", "purpose": "any maskable"}
             for s in (192, 512)]
    body = json.dumps({"name": APP_NAME, "short_name": "Markets", "start_url": "/", "scope": "/",
                       "display": "standalone", "background_color": "#090c11", "theme_color": "#090c11",
                       "icons": icons})
    return Response(body, mimetype="application/manifest+json")


GLYPH = ["X...X", "XX.XX", "X.X.X", "X...X", "X...X"]  # blocky "M"


def _chunk(tag: bytes, data: bytes) -> bytes:
    return struct.pack(">I", len(data)) + tag + data + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)


@functools.lru_cache(maxsize=4)
def make_icon(size: int) -> bytes:
    cell = size // 9
    off = (size - 5 * cell) // 2
    amber, dark = bytes((255, 176, 0)), bytes((17, 17, 17))
    raw = bytearray()
    for y in range(size):
        raw.append(0)
        gy = (y - off) // cell if y >= off else -1
        for x in range(size):
            gx = (x - off) // cell if x >= off else -1
            raw += dark if (0 <= gy < 5 and 0 <= gx < 5 and GLYPH[gy][gx] == "X") else amber
    return (b"\x89PNG\r\n\x1a\n" + _chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 2, 0, 0, 0))
            + _chunk(b"IDAT", zlib.compress(bytes(raw), 9)) + _chunk(b"IEND", b""))


@app.route("/icon-<int:size>.png")
def icon(size: int):
    if size not in (192, 512):
        return Response(status=404)
    return Response(make_icon(size), mimetype="image/png", headers={"Cache-Control": "public, max-age=86400"})


PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="theme-color" content="#090c11">
<link rel="manifest" href="/manifest.webmanifest">
<link rel="apple-touch-icon" href="/icon-192.png">
<title>Markets By Aniruddha</title>
<style>
:root{--bg:#090c11;--panel:#0f141b;--panel2:#151b25;--line:#212a36;--text:#e7eaf0;--muted:#7f8a9a;--amber:#ffb000;--up:#2ee59d;--down:#ff5d6c;--warn:#ffd166;--mono:ui-monospace,"Cascadia Mono",Consolas,monospace}
*{box-sizing:border-box}
html,body{margin:0;height:100%;background:var(--bg);color:var(--text);font:14px/1.45 "Segoe UI",system-ui,sans-serif}
body{display:flex;flex-direction:column}
header{display:flex;align-items:center;gap:22px;padding:10px 18px;border-bottom:1px solid var(--line);background:var(--panel)}
.brand{display:flex;align-items:center;gap:11px;white-space:nowrap}
.logo{width:32px;height:32px;border-radius:8px;background:var(--amber);color:#111;font-weight:800;display:grid;place-items:center;font-size:18px}
.brand b{display:block;letter-spacing:.16em;font-size:14px;line-height:1.1}
.brand small{display:block;color:var(--amber);letter-spacing:.24em;font-size:10px;font-weight:600}
#strip{flex:1;display:flex;gap:6px;overflow-x:auto;scrollbar-width:none}
.chip{padding:3px 12px;border-left:2px solid var(--line);white-space:nowrap;min-width:108px}
.chip span{display:block;color:var(--muted);font-size:10px;letter-spacing:.08em}
.chip b{font-family:var(--mono);font-size:14px;margin-right:6px}
.chip em{font-style:normal;font-family:var(--mono);font-size:11px}
#clock{font-family:var(--mono);color:var(--amber);text-align:right;white-space:nowrap;font-size:15px}
#clock small{display:block;color:var(--muted);font-size:10px}
nav{display:flex;gap:2px;padding:0 14px;background:var(--panel);border-bottom:1px solid var(--line)}
nav button{background:none;border:0;color:var(--muted);padding:11px 18px;font:600 13px inherit;cursor:pointer;border-bottom:2px solid transparent;display:flex;align-items:center;gap:8px}
nav button:hover{color:var(--text)}nav button.on{color:var(--amber);border-bottom-color:var(--amber)}
.dot{width:7px;height:7px;border-radius:50%;display:inline-block;background:var(--muted)}
.dot.ok{background:var(--up)}.dot.stale{background:var(--warn)}.dot.load{background:var(--muted);animation:pl 1s infinite}
@keyframes pl{50%{opacity:.25}}
main{flex:1;overflow:auto;padding:14px 18px}
section[hidden]{display:none}
table{width:100%;border-collapse:collapse}
th{position:sticky;top:-14px;background:var(--panel2);color:var(--muted);font-size:11px;letter-spacing:.09em;text-transform:uppercase;padding:9px 10px;border-bottom:1px solid var(--line);z-index:1}
td{padding:7px 10px;border-bottom:1px solid var(--line);text-align:center}
td.l,th.l{text-align:left}td.b{font-weight:600}
tr:hover td{background:rgba(255,255,255,.025)}
.mono{font-family:var(--mono);font-variant-numeric:tabular-nums}.muted{color:var(--muted)}
.cu{background:rgba(46,229,157,.12);color:var(--up)}.cd{background:rgba(255,93,108,.12);color:var(--down)}.cn{background:rgba(255,209,102,.1);color:var(--warn)}
.up{color:var(--up)}.dn{color:var(--down)}.wn{color:var(--warn)}
@keyframes fu{from{background:rgba(46,229,157,.6)}}@keyframes fd{from{background:rgba(255,93,108,.6)}}
.fu{animation:fu 1.3s ease-out}.fd{animation:fd 1.3s ease-out}
.badge{display:inline-block;padding:2px 9px;border-radius:4px;font-size:11px;font-weight:700;letter-spacing:.04em}
.b-brk{background:#c62828;color:#fff}.b-high{background:rgba(255,93,108,.18);color:var(--down)}.b-med{background:rgba(255,209,102,.16);color:var(--warn)}
.b-up{background:rgba(46,229,157,.16);color:var(--up)}
.st.ok{color:var(--up)}.st.bad{color:var(--down)}
.bar{display:flex;gap:10px;align-items:center;margin-bottom:12px;flex-wrap:wrap}
input[type=text],select{background:var(--panel2);border:1px solid var(--line);color:var(--text);padding:7px 11px;border-radius:6px;font:inherit}
input[type=text]{width:260px}
label{color:var(--muted);display:flex;gap:6px;align-items:center;cursor:pointer}
.seg{display:flex;border:1px solid var(--line);border-radius:7px;overflow:hidden}
.seg button{background:var(--panel2);border:0;color:var(--muted);padding:7px 16px;font:600 13px inherit;cursor:pointer}
.seg button.on{background:var(--amber);color:#111}.seg small{opacity:.7;margin-left:4px}
a{color:#6db3ff;text-decoration:none}a:hover{text-decoration:underline}
tr.new td{animation:fu 3s ease-out}
tr.day td{background:var(--panel2);color:var(--amber);font-weight:700;text-align:left;letter-spacing:.06em}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(340px,1fr));gap:12px;margin-bottom:16px}
.card{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:14px 16px}
.card .ch{display:flex;justify-content:space-between;align-items:center;font-weight:700;margin-bottom:10px}
.big{font:700 28px var(--mono);margin:4px 0 8px}.big small{font-size:13px;color:var(--muted)}
.kv{display:grid;grid-template-columns:auto 1fr auto 1fr;gap:4px 10px;color:var(--muted)}.kv b{color:var(--text);font-family:var(--mono)}
.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-bottom:10px}
.stats span{display:block;color:var(--muted);font-size:10px;letter-spacing:.08em;text-transform:uppercase}.stats b{font:600 15px var(--mono)}
h3{margin:14px 0 10px;color:var(--amber);letter-spacing:.12em;font-size:12px;text-transform:uppercase}
.warnbar{background:rgba(255,209,102,.1);border:1px solid rgba(255,209,102,.35);color:var(--warn);padding:7px 12px;border-radius:6px;margin-bottom:12px;font-size:13px}
.empty{padding:60px 20px;text-align:center;color:var(--muted)}
footer{display:flex;gap:18px;align-items:center;padding:7px 18px;border-top:1px solid var(--line);background:var(--panel);font-size:12px;color:var(--muted);flex-wrap:wrap}
footer b{color:var(--text);font-family:var(--mono);font-weight:500}footer .sp{flex:1}
@media(max-width:760px){
header{flex-wrap:wrap;gap:8px;padding:8px 12px}#clock{display:none}#strip{order:3;flex-basis:100%}
nav{overflow-x:auto;padding:0 4px;scrollbar-width:none}nav button{padding:10px 12px;white-space:nowrap}
main{padding:10px}table{min-width:620px}#newsBody table{min-width:0}#newsBody td.mono{white-space:nowrap}
td,th{padding:6px 8px}th{top:-10px}input[type=text]{width:100%}.grid{grid-template-columns:1fr}
.stats{grid-template-columns:repeat(2,1fr)}footer{padding:7px 12px;gap:10px}}
</style></head><body>
<header>
  <div class="brand"><div class="logo">M</div><div><b>MARKETS</b><small>BY ANIRUDDHA</small></div></div>
  <div id="strip"></div>
  <div id="clock"></div>
</header>
<nav id="nav"></nav>
<main>
  <div id="bn"></div>
  <section id="s-prices" hidden></section>
  <section id="s-news" hidden>
    <div class="bar"><input type="text" id="nq" placeholder="Search headlines…"><select id="nsrc"><option value="">All sources</option></select>
    <label><input type="checkbox" id="nbrk"> Breaking only</label><span id="ncount" class="muted"></span></div>
    <div id="newsBody"></div>
  </section>
  <section id="s-fii" hidden></section>
  <section id="s-calendar" hidden>
    <div class="bar"><div class="seg" id="cseg"></div></div><div id="calBody"></div>
  </section>
  <section id="s-oi" hidden></section>
</main>
<footer id="foot"></footer>
<script>
const MODS=[["prices","Prices"],["news","News"],["fii","FII / DII"],["calendar","Eco Calendar"],["oi","OI / PCR"]];
const STRIP=[["COMEX Gold Near","COMEX GOLD"],["MCX Gold Near","MCX GOLD"],["COMEX Silver Near","COMEX SILVER"],["MCX Silver Near","MCX SILVER"],["LME Copper Near","LME COPPER"],["USDINR Near","USDINR"],["Dollar Index","DXY"],["US 10Y Yield","US 10Y"]];
let S={},INT={},version=-1,online=false,rendered={},tab=(location.hash||"#prices").slice(1),calSel="this";
let NEWS=[],FRESH=new Set(),seenNews=new Set(),newsFirst=true;const lastPx={};
const $=s=>document.querySelector(s);
const esc=v=>String(v??"").replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const num=(v,d=2)=>{const n=parseFloat(v);return isFinite(n)?n.toFixed(d):"–"};
const grp=v=>{const n=Number(v);return isFinite(n)&&v!==""&&v!==null?n.toLocaleString("en-IN"):esc(v??"–")};
const sgn=n=>n>0?"up":n<0?"dn":"";
const ivl=s=>s<60?s+"s":Math.round(s/60)+"m";
const msg=m=>`<div class="empty">${m.ok===false?"Data source unavailable right now — retrying automatically.<br><small>"+esc(m.error)+"</small>":"Loading…"}</div>`;
const pn=x=>{const n=parseFloat(String(x).replace(/[%KMBT,]/g,""));return isFinite(n)?n:null};

function buildNav(){
  $("#nav").innerHTML=MODS.map(([k,l])=>`<button data-k="${k}"><i class="dot load" id="d-${k}"></i>${l}</button>`).join("");
  $("#nav").onclick=e=>{const b=e.target.closest("button");if(b)setTab(b.dataset.k)};
  setTab(MODS.some(m=>m[0]===tab)?tab:"prices");
}
function setTab(k){tab=k;try{location.hash=k}catch(e){}
  document.querySelectorAll("#nav button").forEach(b=>b.classList.toggle("on",b.dataset.k===k));
  document.querySelectorAll("main section").forEach(s=>s.hidden=s.id!=="s-"+k);renderStatus();}

function renderPrices(m){
  const rows=m.data;if(!rows){$("#s-prices").innerHTML=msg(m);return}
  const by={};rows.forEach(r=>by[r.Watchlist]=r);
  $("#strip").innerHTML=STRIP.map(([k,n])=>{const r=by[k];if(!r)return"";const c=r["Chg %"];
    return `<div class="chip"><span>${n}</span><b>${num(r.Price)}</b><em class="${sgn(c)}">${c>0?"▲":c<0?"▼":""} ${num(c)}%</em></div>`}).join("");
  const body=rows.map(r=>{const k=r.Watchlist,px=r.Price,ch=r["Chg %"],prev=lastPx[k];
    const fl=(prev!=null&&px!=null&&px!==prev)?(px>prev?"fu":"fd"):"";lastPx[k]=px;
    const c=ch>0?"cu":ch<0?"cd":"cn";
    return `<tr><td class="l b">${esc(k)}</td><td class="mono">${esc(r.Ticker)}</td><td class="l">${esc(r.Description)}</td>
    <td class="mono ${c} ${fl}">${num(px)}</td><td class="mono ${c}">${ch>0?"▲ ":ch<0?"▼ ":""}${num(ch)}</td>
    <td>${esc(r.Exchange)}</td><td class="mono muted">${esc(r.Timestamp)}</td><td class="st ${r.Status==="OK"?"ok":"bad"}">${esc(r.Status)}</td></tr>`}).join("");
  $("#s-prices").innerHTML=`<table><thead><tr><th class="l">Watchlist</th><th>Ticker</th><th class="l">Description</th><th>Price</th><th>Chg %</th><th>Exchange</th><th>Updated</th><th>Status</th></tr></thead><tbody>${body}</tbody></table>`;
}

function renderNews(m){
  const items=m.data;if(!items){$("#newsBody").innerHTML=msg(m);return}
  const sel=$("#nsrc"),cur=sel.value,srcs=[...new Set(items.map(i=>i.Source))].sort();
  if(sel.options.length-1!==srcs.length){sel.innerHTML='<option value="">All sources</option>'+srcs.map(s=>`<option>${esc(s)}</option>`).join("");sel.value=cur}
  FRESH=new Set();if(!newsFirst)items.forEach(i=>{if(!seenNews.has(i.Headline))FRESH.add(i.Headline)});
  items.forEach(i=>seenNews.add(i.Headline));newsFirst=false;NEWS=items;drawNews();
}
function drawNews(){
  const q=$("#nq").value.toLowerCase(),src=$("#nsrc").value,br=$("#nbrk").checked;
  const list=NEWS.filter(i=>(!src||i.Source===src)&&(!br||i.Breaking)&&(!q||i.Headline.toLowerCase().includes(q)));
  $("#ncount").textContent=list.length+" headlines · times in IST";
  if(!list.length){$("#newsBody").innerHTML='<div class="empty">No matching headlines</div>';return}
  $("#newsBody").innerHTML=`<table><thead><tr><th>Time</th><th>Source</th><th></th><th class="l">Headline</th></tr></thead><tbody>`+list.map(i=>{
    const h=/^https?:/.test(i.Link)?`<a href="${esc(i.Link)}" target="_blank" rel="noopener">${esc(i.Headline)}</a>`:esc(i.Headline);
    return `<tr class="${FRESH.has(i.Headline)?"new":""}"><td class="mono muted">${esc(i.Time)}</td><td>${esc(i.Source)}</td><td>${i.Breaking?'<span class="badge b-brk">BREAKING</span>':""}</td><td class="l">${h}</td></tr>`}).join("")+"</tbody></table>";
}

function renderFii(m){
  const rows=m.data;if(!rows){$("#s-fii").innerHTML=msg(m);return}
  const cards=rows.map(r=>{const n=r["Net (Cr)"];
    return `<div class="card"><div class="muted">${esc(r.Category)} · ${esc(r.Date)}</div><div class="big ${sgn(n)}">${n>0?"+":""}${num(n)} <small>Cr net</small></div>
    <div class="kv"><span>Buy</span><b>${num(r["Buy (Cr)"])}</b><span>Sell</span><b>${num(r["Sell (Cr)"])}</b></div></div>`}).join("");
  const tr=rows.map(r=>{const n=r["Net (Cr)"];return `<tr><td>${esc(r.Date)}</td><td>${esc(r.Category)}</td><td class="mono">${num(r["Buy (Cr)"])}</td><td class="mono">${num(r["Sell (Cr)"])}</td><td class="mono ${n>0?"cu":n<0?"cd":"cn"}">${num(n)}</td></tr>`}).join("");
  $("#s-fii").innerHTML=`<div class="grid">${cards}</div><table><thead><tr><th>Date</th><th>Category</th><th>Buy (Cr)</th><th>Sell (Cr)</th><th>Net (Cr)</th></tr></thead><tbody>${tr}</tbody></table>`;
}

const CALN={last:"Last Week",this:"This Week",next:"Next Week"};
function actCls(a,f){if(["-","","N/A","TBD",null,undefined].includes(a))return"";const x=pn(a),y=pn(f);if(x==null||y==null)return"";return x>y?"cu":x<y?"cd":""}
function renderCal(m){
  const d=m.data;if(!d){$("#calBody").innerHTML=msg(m);return}
  $("#cseg").innerHTML=Object.keys(CALN).map(k=>`<button data-k="${k}" class="${k===calSel?"on":""}">${CALN[k]}<small>${(d[k]||[]).length}</small></button>`).join("");
  const ev=d[calSel]||[];if(!ev.length){$("#calBody").innerHTML='<div class="empty">No events this period</div>';return}
  let prev="",rows="";
  ev.forEach(e=>{if(e.Date!==prev){prev=e.Date;rows+=`<tr class="day"><td colspan="8">${esc(e.Date)}</td></tr>`}
    rows+=`<tr><td class="mono">${esc(e.Time)}</td><td>${esc(e.Country)}</td><td class="l">${esc(e.Event)}</td>
    <td><span class="badge ${e.Impact==="HIGH"?"b-high":"b-med"}">${esc(e.Impact)}</span></td><td class="mono">${esc(e.Previous)}</td><td class="mono">${esc(e.Forecast)}</td>
    <td class="mono ${actCls(e.Actual,e.Forecast)}">${esc(e.Actual)}</td><td>${/^https?:/.test(e.Link)?`<a href="${esc(e.Link)}" target="_blank" rel="noopener">Link</a>`:""}</td></tr>`});
  $("#calBody").innerHTML=`<table><thead><tr><th>Time</th><th>Country</th><th class="l">Event</th><th>Impact</th><th>Previous</th><th>Forecast</th><th>Actual</th><th>Link</th></tr></thead><tbody>${rows}</tbody></table>`;
}

function renderOi(m){
  const rows=m.data;if(!rows){$("#s-oi").innerHTML=msg(m);return}
  let html="",card=null;
  const flush=()=>{if(!card)return;const s=card.s,p=parseFloat(s.pcr),pc=isFinite(p)?(p>1.2?"up":p<0.8?"dn":"wn"):"wn";
    const bc=s.sentiment==="Bullish"?"b-up":s.sentiment==="Bearish"?"b-high":"b-med";
    html+=`<div class="card"><div class="ch"><span>${esc(s.label)}</span><span class="badge ${bc}">${esc(s.sentiment)}</span></div>
    <div class="stats"><div><span>PCR</span><b class="${pc}">${esc(s.pcr)}</b></div><div><span>Max Pain</span><b>${esc(s.max_pain)}</b></div><div><span>Call OI</span><b>${grp(s.total_call_oi)}</b></div><div><span>Put OI</span><b>${grp(s.total_put_oi)}</b></div></div>`;
    if(card.k.length)html+=`<table><thead><tr><th>Strike</th><th>Call OI</th><th>Put OI</th><th>PCR</th><th></th></tr></thead><tbody>`+card.k.map(k=>`<tr class="${k.max_pain?"":""}"><td class="mono">${esc(k.strike)}</td><td class="mono">${grp(k.call_oi)}</td><td class="mono">${grp(k.put_oi)}</td><td class="mono">${num(k.pcr)}</td><td>${k.max_pain?'<span class="badge b-med">MAX PAIN</span>':""}</td></tr>`).join("")+"</tbody></table>";
    html+="</div>";card=null};
  const open=()=>{html+='<div class="grid">'},close=()=>{html+="</div>"};let inGrid=false;
  rows.forEach(r=>{
    if(r.type==="header"){flush();if(inGrid)close();html+=`<h3>${esc(r.label)}</h3>`;open();inGrid=true}
    else if(r.type==="summary"){flush();if(!inGrid){open();inGrid=true}card={s:r,k:[]}}
    else if(r.type==="strike"&&card)card.k.push(r)});
  flush();if(inGrid)close();$("#s-oi").innerHTML=html;
}

const RENDER={prices:renderPrices,news:renderNews,fii:renderFii,calendar:renderCal,oi:renderOi};
function renderStatus(){
  const now=Date.now()/1000;let foot="",banner="";
  MODS.forEach(([k,l])=>{const m=S[k];if(!m)return;
    const age=m.updated_ts?now-m.updated_ts:null,stale=m.ok===false||(age!=null&&age>3*(INT[k]||60)+30);
    const cls=(m.ok===null&&!m.data)?"load":stale?"stale":"ok",d=$("#d-"+k);if(d)d.className="dot "+cls;
    foot+=`<span><i class="dot ${cls}"></i> ${l} <b>${m.updated||"—"}</b> <small>/${ivl(INT[k]||0)}</small></span>`;
    if(k===tab&&m.ok===false&&m.data)banner=`<div class="warnbar">Source issue — showing last good data from ${esc(m.updated)}. ${esc(m.error)}</div>`;});
  $("#bn").innerHTML=banner;
  $("#foot").innerHTML=foot+`<span class="sp"></span><span><i class="dot ${online?"ok":"stale"}"></i> ${online?"LIVE":"APP OFFLINE — reconnecting…"}</span>`;
}
async function poll(){
  try{const r=await fetch("/api/state?v="+version,{cache:"no-store"});
    if(r.status===401){location.href="/login";return}
    const j=await r.json();online=true;
    if(!j.same){version=j.v;INT=j.intervals;S=j.modules;
      for(const k in RENDER){const m=S[k],sig=m.updated_ts+"|"+m.ok;if(rendered[k]!==sig){rendered[k]=sig;RENDER[k](m)}}}
  }catch(e){online=false}
  renderStatus();setTimeout(poll,1500);
}
$("#nq").oninput=drawNews;$("#nsrc").onchange=drawNews;$("#nbrk").onchange=drawNews;
$("#cseg").onclick=e=>{const b=e.target.closest("button");if(b&&S.calendar){calSel=b.dataset.k;renderCal(S.calendar)}};
setInterval(()=>{const d=new Date();$("#clock").innerHTML=d.toLocaleTimeString("en-GB")+"<small>"+d.toLocaleDateString("en-GB",{weekday:"short",day:"2-digit",month:"short",year:"numeric"})+"</small>"},1000);
buildNav();poll();
</script></body></html>"""


# ───────────────────────────── LAUNCH ─────────────────────────────
def open_window(url: str) -> None:
    candidates = [
        r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
        r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
        r"C:\Program Files\Google\Chrome\Application\chrome.exe",
        r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
    ]
    for exe in candidates:
        if os.path.exists(exe):
            subprocess.Popen([exe, f"--app={url}", "--window-size=1500,900"])
            return
    webbrowser.open(url)


def main() -> None:
    for name in JOBS:
        threading.Thread(target=worker, args=(name,), daemon=True).start()
    if HOSTED:
        print(f"{APP_NAME} [build 18Oct-B] hosted mode on port {PORT} | access code: {'ON' if ACCESS_CODE else 'OFF (anyone with the link can view!)'}")
        try:
            from waitress import serve
        except ImportError:
            serve = None
        if serve:
            serve(app, host=HOST, port=PORT, threads=8)
        else:
            app.run(host=HOST, port=PORT, threaded=True, use_reloader=False)
        return
    url = f"http://{HOST}:{PORT}"
    print(f"{APP_NAME} running at {url}  (Ctrl+C to stop)")
    if os.environ.get("MBA_NO_WINDOW") != "1":
        threading.Timer(1.5, open_window, args=(url,)).start()
    app.run(host=HOST, port=PORT, threaded=True, use_reloader=False)


if __name__ == "__main__":
    main()
