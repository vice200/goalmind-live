# live_all_in_one.py
from __future__ import annotations

import os
import time
import math
import json
import sqlite3
import threading
import unicodedata
import re
from pathlib import Path as _Path
from datetime import datetime, timedelta
from typing import Any, Dict, Optional, List, Tuple
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests
import pandas as pd
import streamlit as st

# Optional UI auto refresh
try:
    from streamlit_autorefresh import st_autorefresh
except Exception:
    st_autorefresh = None

# tomllib (Py 3.11+)
try:
    import tomllib
except Exception:
    tomllib = None

# Optional Stripe
try:
    import stripe
except Exception:
    stripe = None

# =========================================================
# CONFIG
# =========================================================
BASE_URL = "https://v3.football.api-sports.io"
SQLITE_PATH = "live_store.sqlite"

# Keep your schema version (do NOT bump unless changing existing columns)
SCHEMA_VERSION = 20

# How often poller calls real API
POLL_SECONDS = 60  # 5 minutes
POLL_SECONDS = max(int(POLL_SECONDS), 60)  # hard floor: never below 300s (API friendly)

# How often UI refreshes (no API calls, just redraw)
UI_REFRESH_MS = 30 * 1000  # 30 sec

MAX_WORKERS = 8
MAX_FIXTURES_PROCESS = 120
HISTORY_KEEP_HOURS = 24

# Model parameters
PICK_MARGIN = 1.15
BLEND_ACTIVE = 0.65
BLEND_MOMENTUM = 0.35
GOALSOON_K = 0.55           # calibrated to ~10-min horizon (see K_PER_MIN below)
TRAILING_BONUS = 0.10

# Odds / Value params
ODDS_ENABLED = True
ODDS_TOP_FIXTURES = 60      # how many fixtures to compute/store odds for (sorted by threat)
ODDS_MINUTES = 10
K_PER_MIN = GOALSOON_K / float(ODDS_MINUTES)  # per-minute hazard scale

# ===== Tracking (signals proof) =====
SIGNAL_MIN_GOALSOON = 0.62          # only log signals with gs >= this
SIGNAL_TIERS = {"MED", "STRONG"}    # which tiers to log
SIGNAL_COOLDOWN_BUCKET_MIN = 5      # dedupe by 5-min bucket
SIGNAL_HORIZON_MIN = 10             # "goal in next X min"
SETTLE_BUFFER_MIN = 6              # tolerance due to polling interval

# ===== Paywall =====
PAYWALL_DEFAULT = False
DEMO_ROWS = 5

# =========================================================
# TARGET LEAGUES (robust matching)
# =========================================================
TARGET_LEAGUES: List[Dict[str, str]] = [
    # ENGLAND
    {"country": "England", "name": "Premier League"},
    {"country": "England", "name": "Championship"},
    {"country": "England", "name": "League One"},
    {"country": "England", "name": "League Two"},
    {"country": "England", "name": "National League"},
    {"country": "England", "name": "National League - North"},
    {"country": "England", "name": "National League - South"},

    # SCOTLAND
    {"country": "Scotland", "name": "Premiership"},
    {"country": "Scotland", "name": "Championship"},
    {"country": "Scotland", "name": "League One"},
    {"country": "Scotland", "name": "League Two"},
    {"country": "Scotland", "name": "Highland League"},
    {"country": "Scotland", "name": "Lowland League"},
    {"country": "Scotland", "name": "Scottish Premiership"},
    {"country": "Scotland", "name": "Scottish Championship"},

    # SPAIN
    {"country": "Spain", "name": "La Liga"},
    {"country": "Spain", "name": "LaLiga"},
    {"country": "Spain", "name": "Segunda Division"},

    # FRANCE
    {"country": "France", "name": "Ligue 1"},
    {"country": "France", "name": "Ligue 2"},

    # ITALY
    {"country": "Italy", "name": "Serie A"},
    {"country": "Italy", "name": "Serie B"},

    # GERMANY
    {"country": "Germany", "name": "Bundesliga"},
    {"country": "Germany", "name": "2. Bundesliga"},
    {"country": "Germany", "name": "Bundesliga 2"},

    # BELGIUM
    {"country": "Belgium", "name": "Jupiler Pro League"},
    {"country": "Belgium", "name": "Challenger Pro League"},

    # NETHERLANDS
    {"country": "Netherlands", "name": "Eredivisie"},
    {"country": "Netherlands", "name": "Eerste Divisie"},

    # PORTUGAL
    {"country": "Portugal", "name": "Primeira Liga"},
    {"country": "Portugal", "name": "Liga Portugal 2"},
    {"country": "Portugal", "name": "Liga Portugal"},

    # GREECE
    {"country": "Greece", "name": "Super League"},
    {"country": "Greece", "name": "Super League 2"},

    # TURKEY / TÜRKİYE
    {"country": "Turkey", "name": "Süper Lig"},
    {"country": "Turkey", "name": "TFF 1. Lig"},
    {"country": "Türkiye", "name": "Süper Lig"},
    {"country": "Türkiye", "name": "TFF 1. Lig"},

    # EXTRA leagues (best-effort name matching)
    {"country": "Brazil", "name": "Serie A"},
    {"country": "Brazil", "name": "Serie B"},
    {"country": "Argentina", "name": "Liga Profesional Argentina"},
    {"country": "Argentina", "name": "Primera Division"},
    {"country": "Germany", "name": "3. Liga"},
    {"country": "Croatia", "name": "1. HNL"},
    {"country": "Croatia", "name": "HNL"},
    {"country": "Poland", "name": "Ekstraklasa"},
    {"country": "Switzerland", "name": "Super League"},
    {"country": "Austria", "name": "Bundesliga"},
    {"country": "Japan", "name": "J1 League"},
    {"country": "South-Korea", "name": "K League 1"},
    {"country": "Korea Republic", "name": "K League 1"},
    {"country": "China", "name": "Super League"},
    {"country": "USA", "name": "Major League Soccer"},
    {"country": "United States", "name": "Major League Soccer"},
]


def _norm(s: str) -> str:
    s = (s or "").strip().casefold()
    s = "".join(ch for ch in unicodedata.normalize("NFKD", s) if not unicodedata.combining(ch))
    s = re.sub(r"\s+", " ", s).strip()
    return s


TARGET_KEYS = {(_norm(x["country"]), _norm(x["name"])) for x in TARGET_LEAGUES}
TARGET_COUNTRIES = {_norm(x["country"]) for x in TARGET_LEAGUES}

COUNTRY_NAME_PATTERNS: Dict[str, List[str]] = {
    "england": ["premier league", "championship", "league one", "league two", "national league"],
    "scotland": ["premiership", "championship", "league one", "league two", "highland", "lowland", "scottish"],
    "spain": ["la liga", "laliga", "segunda"],
    "france": ["ligue 1", "ligue 2"],
    "italy": ["serie a", "serie b"],
    "belgium": ["jupiler", "challenger"],
    "netherlands": ["eredivisie", "eerste divisie"],
    "portugal": ["primeira", "liga portugal"],
    "greece": ["super league"],
    "turkey": ["super lig", "tff 1"],
    "turkiye": ["super lig", "tff 1"],

    "brazil": ["serie a", "serie b"],
    "argentina": ["liga profesional", "primera division"],
    "germany": ["3. liga", "3 liga", "dritte liga"],
    "croatia": ["hnl", "1. hnl", "prva"],
    "poland": ["ekstraklasa"],
    "switzerland": ["super league"],
    "austria": ["bundesliga"],
    "japan": ["j1"],
    "korea republic": ["k league 1"],
    "south-korea": ["k league 1"],
    "china": ["super league"],
    "usa": ["major league soccer", "mls"],
    "united states": ["major league soccer", "mls"],
}


def is_target_fixture(fx: Dict[str, Any]) -> bool:
    lg = fx.get("league") or {}
    country = _norm(str(lg.get("country") or ""))
    name = _norm(str(lg.get("name") or ""))

    if (country, name) in TARGET_KEYS:
        return True

    if country == "england" and "national league" in name:
        return True
    if country == "scotland" and ("highland" in name or "lowland" in name):
        return True
    if country == "scotland" and name.startswith("scottish "):
        return True

    pats = COUNTRY_NAME_PATTERNS.get(country) or []
    return any(p in name for p in pats)


def country_fallback_fixture(fx: Dict[str, Any]) -> bool:
    lg = fx.get("league") or {}
    country = _norm(str(lg.get("country") or ""))
    return country in TARGET_COUNTRIES


# =========================================================
# SECRETS HELPERS (API key + Stripe config)
# =========================================================
def _read_secrets_toml() -> Dict[str, Any]:
    p = _Path(".streamlit") / "secrets.toml"
    if p.exists() and tomllib:
        try:
            return tomllib.loads(p.read_text(encoding="utf-8")) or {}
        except Exception:
            return {}
    return {}


def secret_get(key: str, default: Any = "") -> Any:
    v = os.getenv(key)
    if v is not None and str(v).strip() != "":
        return v
    try:
        if key in st.secrets:
            return st.secrets.get(key)
    except Exception:
        pass
    data = _read_secrets_toml()
    if isinstance(data, dict) and key in data:
        return data.get(key, default)
    return default


def secret_get_nested(section: str, key: str, default: Any = "") -> Any:
    try:
        if section in st.secrets and key in st.secrets[section]:
            return st.secrets[section].get(key, default)
    except Exception:
        pass
    data = _read_secrets_toml()
    if isinstance(data, dict):
        sec = data.get(section)
        if isinstance(sec, dict) and key in sec:
            return sec.get(key, default)
    return default


def load_api_key() -> str:
    k = (os.getenv("API_FOOTBALL_KEY") or "").strip()
    if k:
        return k
    p = _Path(".streamlit") / "secrets.toml"
    if p.exists() and tomllib:
        try:
            data = tomllib.loads(p.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                v = data.get("API_FOOTBALL_KEY")
                if isinstance(v, str) and v.strip():
                    return v.strip()
        except Exception:
            pass
    return ""


def paywall_enabled() -> bool:
    v = secret_get("PAYWALL_ENABLED", PAYWALL_DEFAULT)
    if isinstance(v, bool):
        return v
    return str(v).strip().lower() in {"1", "true", "yes", "y", "on"}


def stripe_cfg() -> Dict[str, str]:
    return {
        "secret_key": str(secret_get_nested("stripe", "SECRET_KEY", "") or "").strip(),
        "price_id": str(secret_get_nested("stripe", "PRICE_ID", "") or "").strip(),
        "success_url": str(secret_get_nested("stripe", "SUCCESS_URL", "") or "").strip(),
        "cancel_url": str(secret_get_nested("stripe", "CANCEL_URL", "") or "").strip(),
        "return_url": str(secret_get_nested("stripe", "RETURN_URL", "") or "").strip(),
        "admin_bypass": str(secret_get_nested("stripe", "ADMIN_BYPASS_CODE", "") or "").strip(),
    }


# =========================================================
# API Client
# =========================================================
class ApiFootballClient:
    """Thread-safe: no shared requests.Session across threads."""
    def __init__(self, base_url: str, api_key: Optional[str] = None, timeout: int = 30):
        self.base_url = base_url.rstrip("/")
        self.api_key = (api_key or load_api_key()).strip()
        if not self.api_key:
            raise RuntimeError("Missing API key. Add API_FOOTBALL_KEY to .streamlit/secrets.toml")
        self.timeout = timeout
        self.headers = {"x-apisports-key": self.api_key}

    def get(self, path: str, params: Optional[Dict[str, Any]] = None, retries: int = 3) -> Dict[str, Any]:
        url = f"{self.base_url}{path}"
        last_err = None
        for i in range(retries):
            try:
                r = requests.get(url, params=params or {}, headers=self.headers, timeout=self.timeout)
                if r.status_code == 429:
                    time.sleep(2.0 + i * 2.0)
                    continue
                r.raise_for_status()
                return r.json()
            except Exception as e:
                last_err = e
                time.sleep(1.0 + i * 1.5)
        raise RuntimeError(f"API GET failed: {url} :: {last_err}")


# =========================================================
# STAT PARSING
# =========================================================
def _to_float(v: Any) -> float:
    if v is None:
        return 0.0
    if isinstance(v, str):
        s = v.strip()
        if not s:
            return 0.0
        s = s.replace("%", "").strip().replace(",", ".")
        try:
            return float(s)
        except Exception:
            return 0.0
    try:
        return float(v)
    except Exception:
        return 0.0


def _to_int(v: Any) -> int:
    return int(round(_to_float(v), 0))


def _norm_key(k: str) -> str:
    k = (k or "").strip().casefold()
    k = "".join(ch for ch in unicodedata.normalize("NFKD", k) if not unicodedata.combining(ch))
    k = re.sub(r"[^a-z0-9]+", "", k)
    return k


def stats_list_to_maps(stats_list: Optional[List[dict]]) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    orig: Dict[str, Any] = {}
    norm: Dict[str, Any] = {}
    for x in stats_list or []:
        t = (x.get("type") or "").strip()
        v = x.get("value")
        if not t:
            continue
        orig[t] = v
        norm[_norm_key(t)] = v
    return orig, norm


def stat_get_int(norm: Dict[str, Any], *keys: str) -> int:
    for k in keys:
        nk = _norm_key(k)
        if nk in norm:
            return _to_int(norm[nk])
    return 0


def stat_get_pct(norm: Dict[str, Any], *keys: str) -> float:
    for k in keys:
        nk = _norm_key(k)
        if nk in norm:
            return float(_to_float(norm[nk]))
    return 0.0


def stat_get_xg(norm: Dict[str, Any]) -> float:
    for nk, v in norm.items():
        if "expected" in nk and "goal" in nk:
            return float(_to_float(v))
        if nk == "xg":
            return float(_to_float(v))
    return 0.0


# =========================================================
# MODEL
# =========================================================
def compute_strength(min_span: int,
                     tot: int, sot: int, soff: int,
                     inside: int, outside: int, blocked: int,
                     corners: int, offsides: int, fouls: int,
                     xg: float, poss_pct: float, pass_acc_pct: float,
                     red: int) -> float:
    m = max(int(min_span or 0), 1)
    core = (
        1.10 * sot +
        0.55 * inside +
        0.25 * tot +
        0.20 * corners +
        0.18 * soff +
        0.14 * blocked +
        0.05 * outside
    ) / m
    flow = (0.03 * offsides / m) - (0.01 * fouls / m)
    xg_boost = 1.40 * float(xg) / max(m / 45.0, 0.5)
    control = 0.0030 * poss_pct + 0.0015 * pass_acc_pct
    card_pen = 0.60 if red >= 1 else 1.00
    return float(max(0.0, (core + flow + xg_boost + control) * card_pen))


def likely_side(h: float, a: float) -> str:
    if h > a * PICK_MARGIN:
        return "HOME"
    if a > h * PICK_MARGIN:
        return "AWAY"
    return "NONE"


def goalsoon(total_strength: float) -> float:
    # Interpreted as ~probability of ANY goal in next ODDS_MINUTES
    s = 1.0 - math.exp(-GOALSOON_K * max(total_strength, 0.0))
    return float(max(0.0, min(1.0, s)))


def trailing_bonus(score_home: int, score_away: int) -> Tuple[float, float]:
    if score_home < score_away:
        return (TRAILING_BONUS, 0.0)
    if score_away < score_home:
        return (0.0, TRAILING_BONUS)
    return (0.0, 0.0)


def tier_from(gs: float, edge_abs: float, pick: str) -> str:
    if pick in {"HOME", "AWAY"} and gs >= 0.78 and edge_abs >= 0.15:
        return "STRONG"
    if pick in {"HOME", "AWAY"} and gs >= 0.62 and edge_abs >= 0.10:
        return "MED"
    return "WATCH"


# =========================================================
# SQLITE (LOCK-SAFE)
# =========================================================
_DB_INIT_LOCK = threading.Lock()


def _table_cols(con: sqlite3.Connection, table: str) -> set:
    """Return a set of column names for a table (empty if table missing)."""
    try:
        rows = con.execute(f"PRAGMA table_info({table});").fetchall()
        return {str(r[1]) for r in rows}
    except Exception:
        return set()


def _schema_compatible(con: sqlite3.Connection) -> bool:
    """Quick sanity check.

    Users often switch between versions of this file without deleting
    `live_store.sqlite`. If SCHEMA_VERSION accidentally stays the same,
    Streamlit will keep the old tables and you'll see errors like:
    - "no such column: sot_home"
    - "...has no column named ts_utc"

    This check forces a reset when critical columns are missing.
    """
    checks = [
        ("poller_status", "last_run_utc"),
        ("live_current", "sot_home"),
        ("live_history", "sot_home"),
        ("ht_snapshot", "ts_utc"),
    ]
    for tbl, col in checks:
        cols = _table_cols(con, tbl)
        if not cols or col not in cols:
            return False
    return True


def _connect_rw() -> sqlite3.Connection:
    con = sqlite3.connect(SQLITE_PATH, timeout=60, check_same_thread=False, isolation_level=None)
    con.execute("PRAGMA busy_timeout=60000;")
    try:
        con.execute("PRAGMA journal_mode=WAL;")
    except sqlite3.OperationalError:
        pass
    try:
        con.execute("PRAGMA synchronous=NORMAL;")
    except sqlite3.OperationalError:
        pass
    return con


def _connect_ro() -> sqlite3.Connection:
    if _Path(SQLITE_PATH).exists():
        con = sqlite3.connect(f"file:{SQLITE_PATH}?mode=ro", uri=True, timeout=60,
                              check_same_thread=False, isolation_level=None)
    else:
        con = sqlite3.connect(SQLITE_PATH, timeout=60, check_same_thread=False, isolation_level=None)
    con.execute("PRAGMA busy_timeout=60000;")
    return con


def _exec_retry(con: sqlite3.Connection, sql: str, params: tuple = (), attempts: int = 30) -> None:
    for i in range(attempts):
        try:
            con.execute(sql, params)
            return
        except sqlite3.OperationalError as e:
            if "locked" in str(e).lower():
                time.sleep(0.12 + i * 0.08)
                continue
            raise
    con.execute(sql, params)



def _table_columns(con: sqlite3.Connection, table: str) -> set:
    try:
        rows = con.execute(f"PRAGMA table_info({table});").fetchall()
        # PRAGMA table_info columns: cid, name, type, notnull, dflt_value, pk
        return {r[1] for r in rows}
    except Exception:
        return set()


def _ensure_table_columns(con: sqlite3.Connection, table: str, cols: Dict[str, str]) -> None:
    """Best-effort in-place migration for older SQLite files (adds missing columns)."""
    existing = _table_columns(con, table)
    for name, sqltype in (cols or {}).items():
        if name in existing:
            continue
        try:
            _exec_retry(con, f"ALTER TABLE {table} ADD COLUMN {name} {sqltype};")
        except Exception:
            # If another thread/process already migrated it, ignore
            pass


def db_init_once() -> None:
    with _DB_INIT_LOCK:
        con = _connect_rw()

        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS schema_meta (
            id INTEGER PRIMARY KEY CHECK (id=1),
            version INTEGER NOT NULL
        );
        """)

        row = con.execute("SELECT version FROM schema_meta WHERE id=1;").fetchone()
        current_ver = int(row[0]) if row else None

        # Reset when schema version differs OR when DB is missing critical columns.
        # This prevents "no such column" errors when users switch file versions.
        if current_ver != int(SCHEMA_VERSION) or (current_ver is not None and not _schema_compatible(con)):
            _exec_retry(con, "DROP TABLE IF EXISTS live_current;")
            _exec_retry(con, "DROP TABLE IF EXISTS live_history;")
            _exec_retry(con, "DROP TABLE IF EXISTS ht_snapshot;")
            _exec_retry(con, "DROP TABLE IF EXISTS poller_status;")
            _exec_retry(con, "DELETE FROM schema_meta;")
            _exec_retry(con, "INSERT INTO schema_meta (id, version) VALUES (1, ?);", (int(SCHEMA_VERSION),))

        # Core tables
        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS live_current (
            fixture_id INTEGER PRIMARY KEY,
            ts_utc TEXT NOT NULL,

            league_id INTEGER,
            league TEXT,
            league_country TEXT,

            status TEXT,
            minute INTEGER,
            home TEXT,
            away TEXT,
            score_home INTEGER,
            score_away INTEGER,

            totshots_home INTEGER,
            sot_home INTEGER,
            soff_home INTEGER,
            blocked_home INTEGER,
            inside_home INTEGER,
            outside_home INTEGER,
            corners_home INTEGER,
            offsides_home INTEGER,
            fouls_home INTEGER,
            yel_home INTEGER,
            red_home INTEGER,
            saves_home INTEGER,
            poss_home REAL,
            passes_home INTEGER,
            passes_acc_home INTEGER,
            passpct_home REAL,
            xg_home REAL,

            totshots_away INTEGER,
            sot_away INTEGER,
            soff_away INTEGER,
            blocked_away INTEGER,
            inside_away INTEGER,
            outside_away INTEGER,
            corners_away INTEGER,
            offsides_away INTEGER,
            fouls_away INTEGER,
            yel_away INTEGER,
            red_away INTEGER,
            saves_away INTEGER,
            poss_away REAL,
            passes_away INTEGER,
            passes_acc_away INTEGER,
            passpct_away REAL,
            xg_away REAL,

            active_half TEXT,
            active_pick TEXT,
            active_goalsoon REAL,
            active_strength_home REAL,
            active_strength_away REAL,
            active_edge REAL,
            tier TEXT,

            pick_1h TEXT,
            goalsoon_1h REAL,
            strength_1h_home REAL,
            strength_1h_away REAL,

            pick_2h TEXT,
            goalsoon_2h REAL,
            strength_2h_home REAL,
            strength_2h_away REAL,

            momentum_home REAL,
            momentum_away REAL,

            stats_json_home TEXT,
            stats_json_away TEXT
        );
        """)

        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS live_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts_utc TEXT NOT NULL,
            fixture_id INTEGER,
            league_id INTEGER,
            status TEXT,
            minute INTEGER,

            score_home INTEGER,
            score_away INTEGER,

            totshots_home INTEGER,
            sot_home INTEGER,
            soff_home INTEGER,
            blocked_home INTEGER,
            inside_home INTEGER,
            outside_home INTEGER,
            corners_home INTEGER,
            offsides_home INTEGER,
            fouls_home INTEGER,
            yel_home INTEGER,
            red_home INTEGER,
            xg_home REAL,

            totshots_away INTEGER,
            sot_away INTEGER,
            soff_away INTEGER,
            blocked_away INTEGER,
            inside_away INTEGER,
            outside_away INTEGER,
            corners_away INTEGER,
            offsides_away INTEGER,
            fouls_away INTEGER,
            yel_away INTEGER,
            red_away INTEGER,
            xg_away REAL
        );
        """)

        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS ht_snapshot (
            fixture_id INTEGER PRIMARY KEY,
            ts_utc TEXT NOT NULL,
            minute INTEGER NOT NULL,

            totshots_home INTEGER,
            sot_home INTEGER,
            soff_home INTEGER,
            blocked_home INTEGER,
            inside_home INTEGER,
            outside_home INTEGER,
            corners_home INTEGER,
            offsides_home INTEGER,
            fouls_home INTEGER,
            yel_home INTEGER,
            red_home INTEGER,
            xg_home REAL,

            totshots_away INTEGER,
            sot_away INTEGER,
            soff_away INTEGER,
            blocked_away INTEGER,
            inside_away INTEGER,
            outside_away INTEGER,
            corners_away INTEGER,
            offsides_away INTEGER,
            fouls_away INTEGER,
            yel_away INTEGER,
            red_away INTEGER,
            xg_away REAL
        );
        """)

        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS poller_status (
            id INTEGER PRIMARY KEY CHECK (id = 1),
            last_run_utc TEXT,
            last_error TEXT,
            rows INTEGER,
            stats_calls INTEGER,
            live_all INTEGER,
            matched_live INTEGER,
            odds_ok INTEGER,
            events_ok INTEGER
        );
        """)
        # In-place migrate older DBs that already have poller_status without newer columns
        _ensure_table_columns(con, "poller_status", {
            "last_run_utc": "TEXT",
            "last_error": "TEXT",
            "rows": "INTEGER",
            "stats_calls": "INTEGER",
            "live_all": "INTEGER",
            "matched_live": "INTEGER",
            "odds_ok": "INTEGER DEFAULT 0",
            "events_ok": "INTEGER DEFAULT 0",
        })

        _exec_retry(con, """
            INSERT OR IGNORE INTO poller_status
            (id, last_run_utc, last_error, rows, stats_calls, live_all, matched_live, odds_ok, events_ok)
            VALUES (1, NULL, '', 0, 0, 0, 0, 0, 0);
        """)

        # ===== Tracking tables (signals) =====
        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS signals (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts_utc TEXT NOT NULL,

            fixture_id INTEGER NOT NULL,
            league_id INTEGER,
            league TEXT,
            league_country TEXT,

            minute INTEGER,
            active_half TEXT,

            home TEXT,
            away TEXT,
            score_home INTEGER,
            score_away INTEGER,

            pick TEXT,
            tier TEXT,
            goalsoon REAL,
            edge REAL,
            strength_home REAL,
            strength_away REAL,

            bucket5 INTEGER,
            horizon_min INTEGER,

            settled INTEGER DEFAULT 0,
            settled_ts_utc TEXT,
            window_end_minute INTEGER,
            window_score_home INTEGER,
            window_score_away INTEGER,
            pick_goal INTEGER,
            any_goal INTEGER
        );
        """)

        _exec_retry(con, """
        CREATE UNIQUE INDEX IF NOT EXISTS idx_signals_dedupe
        ON signals (fixture_id, active_half, pick, bucket5);
        """)

        # ===== Paywall DB =====
        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS subscribers (
            email TEXT PRIMARY KEY,
            stripe_customer_id TEXT,
            stripe_subscription_id TEXT,
            sub_status TEXT,
            last_check_utc TEXT
        );
        """)

        # ===== Odds cache (best odds + raw JSON) =====
        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS odds_current (
            fixture_id INTEGER PRIMARY KEY,
            ts_utc TEXT NOT NULL,
            odds_goal10_yes REAL,
            odds_goal10_no REAL,
            odds_next10_home REAL,
            odds_next10_away REAL,
            odds_next10_nogoal REAL,
            odds_btts_yes REAL,
            odds_btts_no REAL,
            odds_over25 REAL,
            odds_under25 REAL,
            odds_json TEXT
        );
        """)

        # ===== Events cache (for timeline + proof) =====
        _exec_retry(con, """
        CREATE TABLE IF NOT EXISTS events_cache (
            fixture_id INTEGER PRIMARY KEY,
            ts_utc TEXT NOT NULL,
            minute INTEGER,
            events_json TEXT
        );
        """)

        con.close()


def db_connect_writer() -> sqlite3.Connection:
    return _connect_rw()


def db_connect_reader() -> sqlite3.Connection:
    return _connect_ro()


def db_set_status(con: sqlite3.Connection, last_run_utc: str, last_error: str,
                  rows: int, stats_calls: int, live_all: int, matched_live: int,
                  odds_ok: int, events_ok: int) -> None:
    _exec_retry(con, """
    UPDATE poller_status
    SET last_run_utc = ?, last_error = ?, rows = ?, stats_calls = ?, live_all = ?, matched_live = ?, odds_ok=?, events_ok=?
    WHERE id = 1;
    """, (last_run_utc, (last_error or "")[:1000], int(rows), int(stats_calls), int(live_all), int(matched_live),
          int(odds_ok), int(events_ok)))


def db_replace_live_current(con: sqlite3.Connection, rows: List[Dict[str, Any]]) -> None:
    _exec_retry(con, "BEGIN IMMEDIATE;")
    try:
        _exec_retry(con, "DELETE FROM live_current;")
        if rows:
            con.executemany("""
                INSERT INTO live_current (
                    fixture_id, ts_utc,
                    league_id, league, league_country,
                    status, minute, home, away, score_home, score_away,

                    totshots_home, sot_home, soff_home, blocked_home, inside_home, outside_home, corners_home, offsides_home, fouls_home, yel_home, red_home, saves_home,
                    poss_home, passes_home, passes_acc_home, passpct_home, xg_home,

                    totshots_away, sot_away, soff_away, blocked_away, inside_away, outside_away, corners_away, offsides_away, fouls_away, yel_away, red_away, saves_away,
                    poss_away, passes_away, passes_acc_away, passpct_away, xg_away,

                    active_half, active_pick, active_goalsoon, active_strength_home, active_strength_away, active_edge, tier,

                    pick_1h, goalsoon_1h, strength_1h_home, strength_1h_away,
                    pick_2h, goalsoon_2h, strength_2h_home, strength_2h_away,

                    momentum_home, momentum_away,

                    stats_json_home, stats_json_away
                ) VALUES (
                    :fixture_id, :ts_utc,
                    :league_id, :league, :league_country,
                    :status, :minute, :home, :away, :score_home, :score_away,

                    :totshots_home, :sot_home, :soff_home, :blocked_home, :inside_home, :outside_home, :corners_home, :offsides_home, :fouls_home, :yel_home, :red_home, :saves_home,
                    :poss_home, :passes_home, :passes_acc_home, :passpct_home, :xg_home,

                    :totshots_away, :sot_away, :soff_away, :blocked_away, :inside_away, :outside_away, :corners_away, :offsides_away, :fouls_away, :yel_away, :red_away, :saves_away,
                    :poss_away, :passes_away, :passes_acc_away, :passpct_away, :xg_away,

                    :active_half, :active_pick, :active_goalsoon, :active_strength_home, :active_strength_away, :active_edge, :tier,

                    :pick_1h, :goalsoon_1h, :strength_1h_home, :strength_1h_away,
                    :pick_2h, :goalsoon_2h, :strength_2h_home, :strength_2h_away,

                    :momentum_home, :momentum_away,

                    :stats_json_home, :stats_json_away
                );
            """, rows)
        _exec_retry(con, "COMMIT;")
    except Exception:
        _exec_retry(con, "ROLLBACK;")
        raise


def db_append_history(con: sqlite3.Connection, rows: List[Dict[str, Any]]) -> None:
    if not rows:
        return
    _exec_retry(con, "BEGIN IMMEDIATE;")
    try:
        con.executemany("""
            INSERT INTO live_history (
                ts_utc, fixture_id, league_id, status, minute,
                score_home, score_away,

                totshots_home, sot_home, soff_home, blocked_home, inside_home, outside_home, corners_home, offsides_home, fouls_home, yel_home, red_home, xg_home,
                totshots_away, sot_away, soff_away, blocked_away, inside_away, outside_away, corners_away, offsides_away, fouls_away, yel_away, red_away, xg_away
            ) VALUES (
                :ts_utc, :fixture_id, :league_id, :status, :minute,
                :score_home, :score_away,

                :totshots_home, :sot_home, :soff_home, :blocked_home, :inside_home, :outside_home, :corners_home, :offsides_home, :fouls_home, :yel_home, :red_home, :xg_home,
                :totshots_away, :sot_away, :soff_away, :blocked_away, :inside_away, :outside_away, :corners_away, :offsides_away, :fouls_away, :yel_away, :red_away, :xg_away
            );
        """, rows)
        _exec_retry(con, "COMMIT;")
    except Exception:
        _exec_retry(con, "ROLLBACK;")
        raise


def db_prune_history(con: sqlite3.Connection, keep_hours: int) -> None:
    cutoff = (datetime.utcnow() - timedelta(hours=keep_hours)).isoformat(timespec="seconds")
    _exec_retry(con, "BEGIN IMMEDIATE;")
    try:
        _exec_retry(con, "DELETE FROM live_history WHERE ts_utc < ?;", (cutoff,))
        _exec_retry(con, "COMMIT;")
    except Exception:
        _exec_retry(con, "ROLLBACK;")
        raise


def db_read_current() -> pd.DataFrame:
    con = db_connect_reader()
    try:
        df = pd.read_sql_query("SELECT * FROM live_current;", con)
    finally:
        con.close()
    return df


def db_read_odds_current() -> pd.DataFrame:
    con = db_connect_reader()
    try:
        df = pd.read_sql_query("SELECT * FROM odds_current;", con)
    finally:
        con.close()
    return df


def db_read_status() -> Dict[str, Any]:
    con = db_connect_reader()
    try:
        row = con.execute(
            "SELECT last_run_utc, last_error, rows, stats_calls, live_all, matched_live, odds_ok, events_ok FROM poller_status WHERE id=1;"
        ).fetchone()
    finally:
        con.close()
    if not row:
        return {"last_run_utc": None, "last_error": "", "rows": 0, "stats_calls": 0, "live_all": 0, "matched_live": 0, "odds_ok": 0, "events_ok": 0}
    return {
        "last_run_utc": row[0],
        "last_error": row[1] or "",
        "rows": row[2] or 0,
        "stats_calls": row[3] or 0,
        "live_all": row[4] or 0,
        "matched_live": row[5] or 0,
        "odds_ok": row[6] or 0,
        "events_ok": row[7] or 0,
    }


# =========================================================
# TRACKING DB functions (signals)
# =========================================================
def db_insert_signals(con: sqlite3.Connection, rows: List[Dict[str, Any]], horizon_min: int) -> int:
    added = 0
    for r in rows:
        pick = str(r.get("active_pick") or "").upper()
        tier = str(r.get("tier") or "")
        gs = float(r.get("active_goalsoon") or 0.0)
        minute = int(r.get("minute") or 0)
        half = str(r.get("active_half") or "")

        if pick not in {"HOME", "AWAY"}:
            continue
        if tier not in SIGNAL_TIERS:
            continue
        if gs < float(SIGNAL_MIN_GOALSOON):
            continue

        bucket5 = int(minute // SIGNAL_COOLDOWN_BUCKET_MIN)

        payload = (
            datetime.utcnow().isoformat(timespec="seconds"),
            int(r.get("fixture_id")),
            int(r.get("league_id") or 0),
            str(r.get("league") or ""),
            str(r.get("league_country") or ""),
            minute,
            half,
            str(r.get("home") or ""),
            str(r.get("away") or ""),
            int(r.get("score_home") or 0),
            int(r.get("score_away") or 0),
            pick,
            tier,
            float(r.get("active_goalsoon") or 0.0),
            float(r.get("active_edge") or 0.0),
            float(r.get("active_strength_home") or 0.0),
            float(r.get("active_strength_away") or 0.0),
            bucket5,
            int(horizon_min),
        )

        try:
            con.execute("""
                INSERT OR IGNORE INTO signals (
                    ts_utc,
                    fixture_id, league_id, league, league_country,
                    minute, active_half,
                    home, away, score_home, score_away,
                    pick, tier, goalsoon, edge, strength_home, strength_away,
                    bucket5, horizon_min
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?);
            """, payload)
            if con.total_changes > 0:
                added += 1
        except Exception:
            continue

    return added


def db_settle_signals_from_history(con: sqlite3.Connection, limit: int = 200) -> int:
    now = datetime.utcnow()
    cutoff = (now - timedelta(minutes=SIGNAL_HORIZON_MIN + 2)).isoformat(timespec="seconds")
    buf = int(SETTLE_BUFFER_MIN)

    to_settle = con.execute("""
        SELECT id, fixture_id, minute, score_home, score_away, pick, horizon_min
        FROM signals
        WHERE settled=0 AND ts_utc <= ?
        ORDER BY id ASC
        LIMIT ?;
    """, (cutoff, int(limit))).fetchall()

    settled = 0

    for sid, fid, smin, sh0, sa0, pick, horizon in to_settle:
        smin = int(smin or 0)
        horizon = int(horizon or SIGNAL_HORIZON_MIN)
        end_min = smin + horizon + buf

        hist = con.execute("""
            SELECT minute, score_home, score_away
            FROM live_history
            WHERE fixture_id=? AND minute > ? AND minute <= ?
            ORDER BY id ASC;
        """, (int(fid), int(smin), int(end_min))).fetchall()

        if not hist:
            continue

        pick_goal = 0
        any_goal = 0
        wmin = None
        wsh = int(sh0 or 0)
        wsa = int(sa0 or 0)

        for m, sh, sa in hist:
            sh = int(sh or 0)
            sa = int(sa or 0)
            if sh != int(sh0 or 0) or sa != int(sa0 or 0):
                any_goal = 1
                wmin = int(m or 0)
                wsh = sh
                wsa = sa
                dh = sh - int(sh0 or 0)
                da = sa - int(sa0 or 0)
                if str(pick).upper() == "HOME" and dh > 0:
                    pick_goal = 1
                if str(pick).upper() == "AWAY" and da > 0:
                    pick_goal = 1
                break

        if wmin is None:
            last_m, last_sh, last_sa = hist[-1]
            wmin = int(last_m or 0)
            wsh = int(last_sh or 0)
            wsa = int(last_sa or 0)

        try:
            con.execute("""
                UPDATE signals
                SET settled=1,
                    settled_ts_utc=?,
                    window_end_minute=?,
                    window_score_home=?,
                    window_score_away=?,
                    pick_goal=?,
                    any_goal=?
                WHERE id=?;
            """, (
                datetime.utcnow().isoformat(timespec="seconds"),
                int(wmin),
                int(wsh),
                int(wsa),
                int(pick_goal),
                int(any_goal),
                int(sid),
            ))
            settled += 1
        except Exception:
            continue

    return settled


def db_read_signals(last_hours: int = 48) -> pd.DataFrame:
    con = db_connect_reader()
    try:
        cutoff = (datetime.utcnow() - timedelta(hours=int(last_hours))).isoformat(timespec="seconds")
        df = pd.read_sql_query(
            "SELECT * FROM signals WHERE ts_utc >= ? ORDER BY id DESC;",
            con,
            params=(cutoff,)
        )
    finally:
        con.close()
    return df


# =========================================================
# PAYWALL DB (subscribers)
# =========================================================
def db_upsert_subscriber(email: str, customer_id: str, subscription_id: str, sub_status: str) -> None:
    con = db_connect_writer()
    try:
        _exec_retry(con, "BEGIN IMMEDIATE;")
        con.execute("""
            INSERT INTO subscribers (email, stripe_customer_id, stripe_subscription_id, sub_status, last_check_utc)
            VALUES (?, ?, ?, ?, ?)
            ON CONFLICT(email) DO UPDATE SET
                stripe_customer_id=excluded.stripe_customer_id,
                stripe_subscription_id=excluded.stripe_subscription_id,
                sub_status=excluded.sub_status,
                last_check_utc=excluded.last_check_utc;
        """, (email.lower().strip(), customer_id, subscription_id, sub_status,
              datetime.utcnow().isoformat(timespec="seconds")))
        _exec_retry(con, "COMMIT;")
    except Exception:
        _exec_retry(con, "ROLLBACK;")
        raise
    finally:
        con.close()


def db_get_subscriber(email: str) -> Optional[Dict[str, Any]]:
    con = db_connect_reader()
    try:
        row = con.execute("""
            SELECT email, stripe_customer_id, stripe_subscription_id, sub_status, last_check_utc
            FROM subscribers WHERE email=?;
        """, (email.lower().strip(),)).fetchone()
    finally:
        con.close()
    if not row:
        return None
    return {
        "email": row[0], "customer_id": row[1], "subscription_id": row[2],
        "status": row[3], "last_check_utc": row[4]
    }


def stripe_check_subscription(email: str) -> bool:
    if stripe is None:
        return False
    cfg = stripe_cfg()
    if not cfg["secret_key"]:
        return False

    sub = db_get_subscriber(email)
    if not sub or not sub.get("subscription_id"):
        return False

    stripe.api_key = cfg["secret_key"]
    try:
        s = stripe.Subscription.retrieve(sub["subscription_id"])
        status = (s.get("status") or "").lower()
        db_upsert_subscriber(email, sub.get("customer_id") or "", sub["subscription_id"], status)
        return status in {"active", "trialing"}
    except Exception:
        return False


def stripe_handle_return(session_id: str) -> Optional[str]:
    if stripe is None:
        return None
    cfg = stripe_cfg()
    if not (cfg["secret_key"] and session_id):
        return None

    stripe.api_key = cfg["secret_key"]
    try:
        sess = stripe.checkout.Session.retrieve(session_id, expand=["subscription", "customer"])
        email = (sess.get("customer_details") or {}).get("email") or sess.get("customer_email") or ""
        cust = sess.get("customer")
        sub = sess.get("subscription")

        cust_id = cust.get("id") if isinstance(cust, dict) else str(cust or "")
        if isinstance(sub, dict):
            sub_id = sub.get("id") or ""
            status = (sub.get("status") or "").lower()
        else:
            sub_id = str(sub or "")
            status = ""

        if email and sub_id:
            db_upsert_subscriber(email, cust_id, sub_id, status or "active")
            return email
    except Exception:
        return None
    return None


def stripe_create_checkout(email: str) -> Optional[str]:
    if stripe is None:
        return None
    cfg = stripe_cfg()
    if not (cfg["secret_key"] and cfg["price_id"] and cfg["success_url"] and cfg["cancel_url"]):
        return None

    stripe.api_key = cfg["secret_key"]
    try:
        sess = stripe.checkout.Session.create(
            mode="subscription",
            customer_email=email,
            line_items=[{"price": cfg["price_id"], "quantity": 1}],
            success_url=cfg["success_url"],
            cancel_url=cfg["cancel_url"],
            allow_promotion_codes=True,
        )
        return sess.url
    except Exception:
        return None


def stripe_create_portal(email: str) -> Optional[str]:
    if stripe is None:
        return None
    cfg = stripe_cfg()
    if not cfg["secret_key"]:
        return None
    sub = db_get_subscriber(email)
    if not sub or not sub.get("customer_id"):
        return None

    stripe.api_key = cfg["secret_key"]
    try:
        portal = stripe.billing_portal.Session.create(
            customer=sub["customer_id"],
            return_url=cfg["return_url"] or "/",
        )
        return portal.url
    except Exception:
        return None


# =========================================================
# ODDS + EVENTS: API CALLS
# =========================================================
def fetch_live_fixtures(client: ApiFootballClient) -> List[Dict[str, Any]]:
    data = client.get("/fixtures", params={"live": "all"})
    return data.get("response", []) or []


def fetch_fixture_stats(client: ApiFootballClient, fixture_id: int) -> List[Dict[str, Any]]:
    data = client.get("/fixtures/statistics", params={"fixture": fixture_id})
    return data.get("response", []) or []


def fetch_live_odds_all(client: ApiFootballClient) -> List[Dict[str, Any]]:
    # API-Football odds live is plan-dependent; we fail-soft.
    try:
        data = client.get("/odds/live", params={})
        return data.get("response", []) or []
    except Exception:
        # fallback attempt
        try:
            data = client.get("/odds/live", params={"live": "all"})
            return data.get("response", []) or []
        except Exception:
            return []


def fetch_fixture_events(client: ApiFootballClient, fixture_id: int) -> List[Dict[str, Any]]:
    data = client.get("/fixtures/events", params={"fixture": int(fixture_id)})
    return data.get("response", []) or []


# =========================================================
# ODDS PARSING (best odds per market)
# =========================================================
def _norm_txt(s: str) -> str:
    s = (s or "").strip().casefold()
    s = "".join(ch for ch in unicodedata.normalize("NFKD", s) if not unicodedata.combining(ch))
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _odd_to_float(v: Any) -> Optional[float]:
    if v is None:
        return None
    if isinstance(v, (int, float)):
        return float(v)
    if isinstance(v, str):
        s = v.strip().replace(",", ".")
        try:
            return float(s)
        except Exception:
            return None
    return None


def _best_update(best: Dict[str, float], key: str, odd: Optional[float]) -> None:
    if odd is None or odd <= 1.0:
        return
    cur = best.get(key)
    if cur is None or odd > cur:
        best[key] = float(odd)


def _handicap_to_float(v: Any) -> Optional[float]:
    if v is None:
        return None
    if isinstance(v, (int, float)):
        return float(v)
    if isinstance(v, str):
        s = v.strip().replace(",", ".")
        if not s:
            return None
        try:
            return float(s)
        except Exception:
            return None
    return None


def _extract_line_from_label(label_norm: str) -> Optional[float]:
    # tries to find something like 2.5 in "Over 2.5", "Goals/Over  0.5", etc.
    m = re.search(r"(\d+(?:\.\d+)?)", label_norm)
    if not m:
        return None
    try:
        return float(m.group(1))
    except Exception:
        return None


def parse_best_odds_for_fixture(odds_item: Dict[str, Any], home: str, away: str) -> Dict[str, Any]:
    """
    API-Football /odds/live format:
      item["odds"] = [ { "name": "...", "values": [ {value, odd, handicap, suspended}, ... ] }, ... ]

    Returns best odds for:
      - odds_goal10_yes/no       (Next 10 Minutes Total -> Goals/Over 0.5 / Goals/Under 0.5)
      - odds_next10_home/away/nogoal  (Next goal market proxy: Next Goal / Next Team to Score / 1st goal)
      - odds_btts_yes/no         (Both Teams to Score)
      - odds_over25/under25      (Over/Under Line OR Match Goals with handicap 2.5)
    """
    best: Dict[str, float] = {}

    home_n = _norm_txt(home)
    away_n = _norm_txt(away)

    markets = odds_item.get("odds") or []

    # --- fallback: old structure (just in case some endpoints return bookmakers/bets) ---
    if not markets and (odds_item.get("bookmakers") or []):
        # keep your old logic if you want, but most likely not needed for /odds/live
        markets = []

    for m in markets:
        mname_raw = str(m.get("name") or "")
        mname = _norm_txt(mname_raw)

        vals = m.get("values") or []
        for v in vals:
            # skip suspended
            if v.get("suspended") is True:
                continue

            label_raw = str(v.get("value") or "")
            label = _norm_txt(label_raw)

            odd = _odd_to_float(v.get("odd") or v.get("odds") or v.get("Odd") or v.get("ODD"))
            if odd is None or odd <= 1.0:
                continue

            hcap = _handicap_to_float(v.get("handicap"))

            # =========================
            # 1) GOAL IN NEXT 10 MIN (YES/NO)
            # market: "Next 10 Minutes Total"
            # values: "Goals/Over  0.5" / "Goals/Under  0.5"
            # =========================
            if "next 10" in mname and "minute" in mname and "total" in mname:
                # only goals (ignore corners/cards inside this same market)
                if "goals" in label and "0.5" in label:
                    if "over" in label:
                        _best_update(best, "odds_goal10_yes", odd)
                    elif "under" in label:
                        _best_update(best, "odds_goal10_no", odd)

            # =========================
            # 2) BTTS
            # market: "Both Teams to Score"
            # values: Yes / No
            # =========================
            if "both teams" in mname and "score" in mname:
                if label in {"yes", "y"}:
                    _best_update(best, "odds_btts_yes", odd)
                elif label in {"no", "n"}:
                    _best_update(best, "odds_btts_no", odd)

            # =========================
            # 3) OVER/UNDER 2.5 (FT totals)
            # markets you showed: "Over/Under Line" and "Match Goals"
            # values: Over/Under with handicap=2.5 (or label contains 2.5)
            # =========================
            is_ou_market = (
                ("over/under" in mname)
                or ("match goals" in mname)
                or ("total goals" in mname)
                or ("over under" in mname)
            )
            if is_ou_market:
                line = hcap if hcap is not None else _extract_line_from_label(label)
                if line is not None and abs(line - 2.5) < 1e-6:
                    if "over" in label:
                        _best_update(best, "odds_over25", odd)
                    elif "under" in label:
                        _best_update(best, "odds_under25", odd)

            # =========================
            # 4) NEXT GOAL (proxy for your "pick next10" odds columns)
            # markets: "Next Goal", "Next Team to Score", "Which team will score the 1st goal?"
            # values: Home/Away/No Goal (or team names)
            # =========================
            is_next_goal_market = (
                ("next goal" in mname)
                or ("next team" in mname and "score" in mname)
                or ("which team will score" in mname and "1st goal" in mname)
                or (mname == "which team will score the 1st goal?")
            )
            if is_next_goal_market:
                # match by generic labels
                if label in {"home", "1"} or (home_n and home_n in label):
                    _best_update(best, "odds_next10_home", odd)
                elif label in {"away", "2"} or (away_n and away_n in label):
                    _best_update(best, "odds_next10_away", odd)
                elif "no goal" in label or label in {"none", "no", "draw"}:
                    _best_update(best, "odds_next10_nogoal", odd)

    return best


def odds_list_to_map(resp_list: List[Dict[str, Any]]) -> Dict[int, Dict[str, Any]]:
    out: Dict[int, Dict[str, Any]] = {}
    for item in resp_list or []:
        fx = item.get("fixture") or {}
        fid = fx.get("id") or item.get("fixture_id")
        try:
            fid_i = int(fid)
        except Exception:
            continue
        out[fid_i] = item
    return out


def db_replace_odds_current(con: sqlite3.Connection, rows: List[Dict[str, Any]]) -> None:
    _exec_retry(con, "BEGIN IMMEDIATE;")
    try:
        _exec_retry(con, "DELETE FROM odds_current;")
        if rows:
            con.executemany("""
                INSERT INTO odds_current (
                    fixture_id, ts_utc,
                    odds_goal10_yes, odds_goal10_no,
                    odds_next10_home, odds_next10_away, odds_next10_nogoal,
                    odds_btts_yes, odds_btts_no,
                    odds_over25, odds_under25,
                    odds_json
                ) VALUES (
                    :fixture_id, :ts_utc,
                    :odds_goal10_yes, :odds_goal10_no,
                    :odds_next10_home, :odds_next10_away, :odds_next10_nogoal,
                    :odds_btts_yes, :odds_btts_no,
                    :odds_over25, :odds_under25,
                    :odds_json
                );
            """, rows)
        _exec_retry(con, "COMMIT;")
    except Exception:
        _exec_retry(con, "ROLLBACK;")
        raise


# =========================================================
# EVENTS CACHE DB
# =========================================================
def db_upsert_events(con: sqlite3.Connection, fixture_id: int, minute: int, events: List[Dict[str, Any]]) -> None:
    payload = (
        int(fixture_id),
        datetime.utcnow().isoformat(timespec="seconds"),
        int(minute or 0),
        json.dumps(events or [], ensure_ascii=False),
    )
    _exec_retry(con, "BEGIN IMMEDIATE;")
    try:
        con.execute("""
            INSERT INTO events_cache (fixture_id, ts_utc, minute, events_json)
            VALUES (?, ?, ?, ?)
            ON CONFLICT(fixture_id) DO UPDATE SET
                ts_utc=excluded.ts_utc,
                minute=excluded.minute,
                events_json=excluded.events_json;
        """, payload)
        _exec_retry(con, "COMMIT;")
    except Exception:
        _exec_retry(con, "ROLLBACK;")
        raise


def db_read_events(fixture_id: int) -> List[Dict[str, Any]]:
    con = db_connect_reader()
    try:
        row = con.execute("SELECT events_json FROM events_cache WHERE fixture_id=?;", (int(fixture_id),)).fetchone()
    finally:
        con.close()
    if not row or not row[0]:
        return []
    try:
        return json.loads(row[0])
    except Exception:
        return []


# =========================================================
# HT snapshot + previous history
# =========================================================
def ensure_ht_snapshot(con: sqlite3.Connection, base: Dict[str, Any]) -> None:
    fid = int(base["fixture_id"])
    minute = int(base.get("minute") or 0)
    status = (base.get("status") or "").upper()

    if minute < 45:
        return
    if status not in {"HT", "2H", "ET"}:
        return

    exists = con.execute("SELECT 1 FROM ht_snapshot WHERE fixture_id=?;", (fid,)).fetchone()
    if exists:
        return

    ts_utc = datetime.utcnow().isoformat(timespec="seconds")
    _exec_retry(con, "BEGIN IMMEDIATE;")
    try:
        con.execute("""
            INSERT INTO ht_snapshot (
                fixture_id, ts_utc, minute,
                totshots_home, sot_home, soff_home, blocked_home, inside_home, outside_home, corners_home, offsides_home, fouls_home, yel_home, red_home, xg_home,
                totshots_away, sot_away, soff_away, blocked_away, inside_away, outside_away, corners_away, offsides_away, fouls_away, yel_away, red_away, xg_away
            ) VALUES (
                ?, ?, ?,
                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?
            );
        """, (
            fid, ts_utc, 45,
            int(base.get("totshots_home") or 0),
            int(base.get("sot_home") or 0),
            int(base.get("soff_home") or 0),
            int(base.get("blocked_home") or 0),
            int(base.get("inside_home") or 0),
            int(base.get("outside_home") or 0),
            int(base.get("corners_home") or 0),
            int(base.get("offsides_home") or 0),
            int(base.get("fouls_home") or 0),
            int(base.get("yel_home") or 0),
            int(base.get("red_home") or 0),
            float(base.get("xg_home") or 0.0),

            int(base.get("totshots_away") or 0),
            int(base.get("sot_away") or 0),
            int(base.get("soff_away") or 0),
            int(base.get("blocked_away") or 0),
            int(base.get("inside_away") or 0),
            int(base.get("outside_away") or 0),
            int(base.get("corners_away") or 0),
            int(base.get("offsides_away") or 0),
            int(base.get("fouls_away") or 0),
            int(base.get("yel_away") or 0),
            int(base.get("red_away") or 0),
            float(base.get("xg_away") or 0.0),
        ))
        _exec_retry(con, "COMMIT;")
    except Exception:
        _exec_retry(con, "ROLLBACK;")
        raise


def load_ht_snapshot(con: sqlite3.Connection, fid: int) -> Optional[Dict[str, Any]]:
    row = con.execute("SELECT * FROM ht_snapshot WHERE fixture_id=?;", (int(fid),)).fetchone()
    if not row:
        return None
    cols = [x[1] for x in con.execute("PRAGMA table_info(ht_snapshot);").fetchall()]
    return dict(zip(cols, row))


def load_prev_history(con: sqlite3.Connection, fid: int) -> Optional[Dict[str, Any]]:
    row = con.execute("""
        SELECT minute,
               totshots_home, sot_home, soff_home, blocked_home, inside_home, outside_home, corners_home, offsides_home, fouls_home, yel_home, red_home, xg_home,
               totshots_away, sot_away, soff_away, blocked_away, inside_away, outside_away, corners_away, offsides_away, fouls_away, yel_away, red_away, xg_away
        FROM live_history
        WHERE fixture_id=?
        ORDER BY id DESC
        LIMIT 1;
    """, (int(fid),)).fetchone()
    if not row:
        return None

    keys = [
        "minute",
        "totshots_home", "sot_home", "soff_home", "blocked_home", "inside_home", "outside_home", "corners_home", "offsides_home",
        "fouls_home", "yel_home", "red_home", "xg_home",
        "totshots_away", "sot_away", "soff_away", "blocked_away", "inside_away", "outside_away", "corners_away", "offsides_away",
        "fouls_away", "yel_away", "red_away", "xg_away",
    ]
    out: Dict[str, Any] = {}
    for k, v in zip(keys, row):
        out[k] = float(v) if isinstance(v, float) else int(v or 0)
    return out


# =========================================================
# BUILD BASE ROW
# =========================================================
def build_base_row(client: ApiFootballClient, fx: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    lg = fx.get("league", {}) or {}
    fixture = fx.get("fixture", {}) or {}
    teams = fx.get("teams", {}) or {}
    goals = fx.get("goals", {}) or {}

    fixture_id = fixture.get("id")
    if fixture_id is None:
        return None

    status = (fixture.get("status") or {}).get("short") or ""
    minute = (fixture.get("status") or {}).get("elapsed") or 0

    home_obj = teams.get("home") or {}
    away_obj = teams.get("away") or {}
    home = home_obj.get("name") or ""
    away = away_obj.get("name") or ""
    home_id = home_obj.get("id")
    away_id = away_obj.get("id")

    score_home = _to_int(goals.get("home"))
    score_away = _to_int(goals.get("away"))

    h_orig, a_orig = {}, {}
    h_norm, a_norm = {}, {}

    try:
        stats_resp = fetch_fixture_stats(client, int(fixture_id))
    except Exception:
        stats_resp = []

    if stats_resp:
        for blk in stats_resp:
            tid = (blk.get("team") or {}).get("id")
            orig, norm = stats_list_to_maps(blk.get("statistics"))
            if tid == home_id:
                h_orig, h_norm = orig, norm
            elif tid == away_id:
                a_orig, a_norm = orig, norm

        if (not h_norm or not a_norm) and len(stats_resp) >= 2:
            orig1, norm1 = stats_list_to_maps(stats_resp[0].get("statistics"))
            orig2, norm2 = stats_list_to_maps(stats_resp[1].get("statistics"))
            if not h_norm:
                h_orig, h_norm = orig1, norm1
            if not a_norm:
                a_orig, a_norm = orig2, norm2

    def extract_team(norm: Dict[str, Any]) -> Dict[str, Any]:
        xg = stat_get_xg(norm) if norm else 0.0
        return {
            "totshots": stat_get_int(norm, "Total Shots"),
            "sot": stat_get_int(norm, "Shots on Goal"),
            "soff": stat_get_int(norm, "Shots off Goal"),
            "blocked": stat_get_int(norm, "Blocked Shots"),
            "inside": stat_get_int(norm, "Shots insidebox", "Shots inside box"),
            "outside": stat_get_int(norm, "Shots outsidebox", "Shots outside box"),
            "corners": stat_get_int(norm, "Corner Kicks"),
            "offsides": stat_get_int(norm, "Offsides"),
            "fouls": stat_get_int(norm, "Fouls"),
            "yel": stat_get_int(norm, "Yellow Cards"),
            "red": stat_get_int(norm, "Red Cards"),
            "saves": stat_get_int(norm, "Goalkeeper Saves"),
            "poss": stat_get_pct(norm, "Ball Possession"),
            "passes": stat_get_int(norm, "Total passes", "Total Passes"),
            "passes_acc": stat_get_int(norm, "Passes accurate", "Passes Accurate"),
            "passpct": stat_get_pct(norm, "Passes %"),
            "xg": float(xg),
        }

    H = extract_team(h_norm)
    A = extract_team(a_norm)
    ts_utc = datetime.utcnow().isoformat(timespec="seconds")

    row: Dict[str, Any] = {
        "fixture_id": int(fixture_id),
        "ts_utc": ts_utc,

        "league_id": int(lg.get("id") or 0) if lg.get("id") is not None else None,
        "league": str(lg.get("name") or ""),
        "league_country": str(lg.get("country") or ""),

        "status": status,
        "minute": int(minute or 0),
        "home": home,
        "away": away,
        "score_home": score_home,
        "score_away": score_away,

        "totshots_home": int(H["totshots"]),
        "sot_home": int(H["sot"]),
        "soff_home": int(H["soff"]),
        "blocked_home": int(H["blocked"]),
        "inside_home": int(H["inside"]),
        "outside_home": int(H["outside"]),
        "corners_home": int(H["corners"]),
        "offsides_home": int(H["offsides"]),
        "fouls_home": int(H["fouls"]),
        "yel_home": int(H["yel"]),
        "red_home": int(H["red"]),
        "saves_home": int(H["saves"]),
        "poss_home": float(H["poss"]),
        "passes_home": int(H["passes"]),
        "passes_acc_home": int(H["passes_acc"]),
        "passpct_home": float(H["passpct"]),
        "xg_home": float(H["xg"]),

        "totshots_away": int(A["totshots"]),
        "sot_away": int(A["sot"]),
        "soff_away": int(A["soff"]),
        "blocked_away": int(A["blocked"]),
        "inside_away": int(A["inside"]),
        "outside_away": int(A["outside"]),
        "corners_away": int(A["corners"]),
        "offsides_away": int(A["offsides"]),
        "fouls_away": int(A["fouls"]),
        "yel_away": int(A["yel"]),
        "red_away": int(A["red"]),
        "saves_away": int(A["saves"]),
        "poss_away": float(A["poss"]),
        "passes_away": int(A["passes"]),
        "passes_acc_away": int(A["passes_acc"]),
        "passpct_away": float(A["passpct"]),
        "xg_away": float(A["xg"]),

        # defaults computed
        "active_half": "1H",
        "active_pick": "NONE",
        "active_goalsoon": 0.0,
        "active_strength_home": 0.0,
        "active_strength_away": 0.0,
        "active_edge": 0.0,
        "tier": "WATCH",

        "pick_1h": "NONE",
        "goalsoon_1h": 0.0,
        "strength_1h_home": 0.0,
        "strength_1h_away": 0.0,

        "pick_2h": "NONE",
        "goalsoon_2h": 0.0,
        "strength_2h_home": 0.0,
        "strength_2h_away": 0.0,

        "momentum_home": 0.0,
        "momentum_away": 0.0,

        "stats_json_home": json.dumps(h_orig, ensure_ascii=False),
        "stats_json_away": json.dumps(a_orig, ensure_ascii=False),
    }
    return row


# =========================================================
# ENRICH (1H/2H + momentum + tier)
# =========================================================
def enrich_strengths(con: sqlite3.Connection, base: Dict[str, Any]) -> Dict[str, Any]:
    fid = int(base["fixture_id"])
    minute = int(base.get("minute") or 0)
    status = (base.get("status") or "").upper()

    score_home = int(base.get("score_home") or 0)
    score_away = int(base.get("score_away") or 0)

    H = {
        "tot": int(base.get("totshots_home") or 0),
        "sot": int(base.get("sot_home") or 0),
        "soff": int(base.get("soff_home") or 0),
        "blocked": int(base.get("blocked_home") or 0),
        "inside": int(base.get("inside_home") or 0),
        "outside": int(base.get("outside_home") or 0),
        "corners": int(base.get("corners_home") or 0),
        "offsides": int(base.get("offsides_home") or 0),
        "fouls": int(base.get("fouls_home") or 0),
        "xg": float(base.get("xg_home") or 0.0),
        "poss": float(base.get("poss_home") or 0.0),
        "passpct": float(base.get("passpct_home") or 0.0),
        "red": int(base.get("red_home") or 0),
    }
    A = {
        "tot": int(base.get("totshots_away") or 0),
        "sot": int(base.get("sot_away") or 0),
        "soff": int(base.get("soff_away") or 0),
        "blocked": int(base.get("blocked_away") or 0),
        "inside": int(base.get("inside_away") or 0),
        "outside": int(base.get("outside_away") or 0),
        "corners": int(base.get("corners_away") or 0),
        "offsides": int(base.get("offsides_away") or 0),
        "fouls": int(base.get("fouls_away") or 0),
        "xg": float(base.get("xg_away") or 0.0),
        "poss": float(base.get("poss_away") or 0.0),
        "passpct": float(base.get("passpct_away") or 0.0),
        "red": int(base.get("red_away") or 0),
    }

    ht = load_ht_snapshot(con, fid)

    # 1H
    if ht:
        s1_h = compute_strength(
            45,
            int(ht["totshots_home"] or 0), int(ht["sot_home"] or 0), int(ht["soff_home"] or 0),
            int(ht["inside_home"] or 0), int(ht["outside_home"] or 0), int(ht["blocked_home"] or 0),
            int(ht["corners_home"] or 0), int(ht["offsides_home"] or 0), int(ht["fouls_home"] or 0),
            float(ht["xg_home"] or 0.0),
            H["poss"], H["passpct"], int(ht["red_home"] or 0)
        )
        s1_a = compute_strength(
            45,
            int(ht["totshots_away"] or 0), int(ht["sot_away"] or 0), int(ht["soff_away"] or 0),
            int(ht["inside_away"] or 0), int(ht["outside_away"] or 0), int(ht["blocked_away"] or 0),
            int(ht["corners_away"] or 0), int(ht["offsides_away"] or 0), int(ht["fouls_away"] or 0),
            float(ht["xg_away"] or 0.0),
            A["poss"], A["passpct"], int(ht["red_away"] or 0)
        )
    else:
        m1 = min(minute, 45)
        s1_h = compute_strength(m1, H["tot"], H["sot"], H["soff"], H["inside"], H["outside"], H["blocked"],
                               H["corners"], H["offsides"], H["fouls"], H["xg"], H["poss"], H["passpct"], H["red"])
        s1_a = compute_strength(m1, A["tot"], A["sot"], A["soff"], A["inside"], A["outside"], A["blocked"],
                               A["corners"], A["offsides"], A["fouls"], A["xg"], A["poss"], A["passpct"], A["red"])

    pick_1h = likely_side(s1_h, s1_a)
    goalsoon_1h = goalsoon(s1_h + s1_a)

    # 2H delta
    s2_h, s2_a = 0.0, 0.0
    pick_2h, goalsoon_2h = "NONE", 0.0
    if minute > 45 and ht:
        m2 = max(minute - 45, 1)

        dH_tot = max(0, H["tot"] - int(ht["totshots_home"] or 0))
        dH_sot = max(0, H["sot"] - int(ht["sot_home"] or 0))
        dH_soff = max(0, H["soff"] - int(ht["soff_home"] or 0))
        dH_inside = max(0, H["inside"] - int(ht["inside_home"] or 0))
        dH_outside = max(0, H["outside"] - int(ht["outside_home"] or 0))
        dH_blocked = max(0, H["blocked"] - int(ht["blocked_home"] or 0))
        dH_corners = max(0, H["corners"] - int(ht["corners_home"] or 0))
        dH_off = max(0, H["offsides"] - int(ht["offsides_home"] or 0))
        dH_fouls = max(0, H["fouls"] - int(ht["fouls_home"] or 0))
        dH_xg = max(0.0, H["xg"] - float(ht["xg_home"] or 0.0))

        dA_tot = max(0, A["tot"] - int(ht["totshots_away"] or 0))
        dA_sot = max(0, A["sot"] - int(ht["sot_away"] or 0))
        dA_soff = max(0, A["soff"] - int(ht["soff_away"] or 0))
        dA_inside = max(0, A["inside"] - int(ht["inside_away"] or 0))
        dA_outside = max(0, A["outside"] - int(ht["outside_away"] or 0))
        dA_blocked = max(0, A["blocked"] - int(ht["blocked_away"] or 0))
        dA_corners = max(0, A["corners"] - int(ht["corners_away"] or 0))
        dA_off = max(0, A["offsides"] - int(ht["offsides_away"] or 0))
        dA_fouls = max(0, A["fouls"] - int(ht["fouls_away"] or 0))
        dA_xg = max(0.0, A["xg"] - float(ht["xg_away"] or 0.0))

        s2_h = compute_strength(m2, dH_tot, dH_sot, dH_soff, dH_inside, dH_outside, dH_blocked,
                               dH_corners, dH_off, dH_fouls, dH_xg, H["poss"], H["passpct"], H["red"])
        s2_a = compute_strength(m2, dA_tot, dA_sot, dA_soff, dA_inside, dA_outside, dA_blocked,
                               dA_corners, dA_off, dA_fouls, dA_xg, A["poss"], A["passpct"], A["red"])

        pick_2h = likely_side(s2_h, s2_a)
        goalsoon_2h = goalsoon(s2_h + s2_a)

    # Momentum (delta vs last history row -> approx "last poll window")
    prev = load_prev_history(con, fid)
    mom_h, mom_a = 0.0, 0.0
    if prev:
        prev_min = int(prev.get("minute") or 0)
        dm = max(minute - prev_min, 1)

        dH_tot = max(0, H["tot"] - int(prev.get("totshots_home") or 0))
        dH_sot = max(0, H["sot"] - int(prev.get("sot_home") or 0))
        dH_soff = max(0, H["soff"] - int(prev.get("soff_home") or 0))
        dH_inside = max(0, H["inside"] - int(prev.get("inside_home") or 0))
        dH_outside = max(0, H["outside"] - int(prev.get("outside_home") or 0))
        dH_blocked = max(0, H["blocked"] - int(prev.get("blocked_home") or 0))
        dH_corners = max(0, H["corners"] - int(prev.get("corners_home") or 0))
        dH_off = max(0, H["offsides"] - int(prev.get("offsides_home") or 0))
        dH_fouls = max(0, H["fouls"] - int(prev.get("fouls_home") or 0))
        dH_xg = max(0.0, H["xg"] - float(prev.get("xg_home") or 0.0))

        dA_tot = max(0, A["tot"] - int(prev.get("totshots_away") or 0))
        dA_sot = max(0, A["sot"] - int(prev.get("sot_away") or 0))
        dA_soff = max(0, A["soff"] - int(prev.get("soff_away") or 0))
        dA_inside = max(0, A["inside"] - int(prev.get("inside_away") or 0))
        dA_outside = max(0, A["outside"] - int(prev.get("outside_away") or 0))
        dA_blocked = max(0, A["blocked"] - int(prev.get("blocked_away") or 0))
        dA_corners = max(0, A["corners"] - int(prev.get("corners_away") or 0))
        dA_off = max(0, A["offsides"] - int(prev.get("offsides_away") or 0))
        dA_fouls = max(0, A["fouls"] - int(prev.get("fouls_away") or 0))
        dA_xg = max(0.0, A["xg"] - float(prev.get("xg_away") or 0.0))

        mom_h = compute_strength(dm, dH_tot, dH_sot, dH_soff, dH_inside, dH_outside, dH_blocked,
                                dH_corners, dH_off, dH_fouls, dH_xg, H["poss"], H["passpct"], H["red"])
        mom_a = compute_strength(dm, dA_tot, dA_sot, dA_soff, dA_inside, dA_outside, dA_blocked,
                                dA_corners, dA_off, dA_fouls, dA_xg, A["poss"], A["passpct"], A["red"])

    # Active half choice
    if minute <= 45 or status in {"1H", "HT"}:
        active_half = "1H"
        base_h, base_a = s1_h, s1_a
    else:
        active_half = "2H"
        base_h, base_a = s2_h, s2_a

    b_home, b_away = trailing_bonus(score_home, score_away)

    active_strength_home = BLEND_ACTIVE * base_h + BLEND_MOMENTUM * mom_h + b_home
    active_strength_away = BLEND_ACTIVE * base_a + BLEND_MOMENTUM * mom_a + b_away

    denom = max(active_strength_home + active_strength_away, 1e-6)
    edge = (active_strength_home - active_strength_away) / denom

    active_pick = likely_side(active_strength_home, active_strength_away)
    active_goalsoon = goalsoon(active_strength_home + active_strength_away)
    tier = tier_from(active_goalsoon, abs(edge), active_pick)

    base["active_half"] = active_half
    base["active_strength_home"] = float(active_strength_home)
    base["active_strength_away"] = float(active_strength_away)
    base["active_edge"] = float(edge)
    base["active_pick"] = active_pick
    base["active_goalsoon"] = float(active_goalsoon)
    base["tier"] = tier

    base["pick_1h"] = pick_1h
    base["goalsoon_1h"] = float(goalsoon_1h)
    base["strength_1h_home"] = float(s1_h)
    base["strength_1h_away"] = float(s1_a)

    base["pick_2h"] = pick_2h
    base["goalsoon_2h"] = float(goalsoon_2h)
    base["strength_2h_home"] = float(s2_h)
    base["strength_2h_away"] = float(s2_a)

    base["momentum_home"] = float(mom_h)
    base["momentum_away"] = float(mom_a)

    return base


# =========================================================
# VALUE HELPERS (model prob vs odds)
# =========================================================
def _safe_prob_from_odds(odd: Optional[float]) -> Optional[float]:
    if odd is None or odd <= 1.0:
        return None
    return 1.0 / float(odd)


def _poisson_tail_ge(k: int, lam: float) -> float:
    # P(N >= k) for N~Poisson(lam)
    if k <= 0:
        return 1.0
    if lam <= 0:
        return 0.0
    # CDF up to k-1
    term = math.exp(-lam)
    s = term
    for i in range(1, k):
        term *= lam / i
        s += term
    return float(max(0.0, min(1.0, 1.0 - s)))


def model_probs(row: Dict[str, Any]) -> Dict[str, float]:
    """
    Model probabilities:
      - p_goal10_any: any goal in next 10 minutes
      - p_next10_home/away/nogoal: next goal team in next 10 minutes
      - p_btts: both teams to score by FT (from now)
      - p_over25: FT total goals over 2.5
    """
    minute = int(row.get("minute") or 0)
    sh = float(row.get("active_strength_home") or 0.0)
    sa = float(row.get("active_strength_away") or 0.0)
    sh = max(sh, 0.0)
    sa = max(sa, 0.0)

    rh = K_PER_MIN * sh
    ra = K_PER_MIN * sa

    # next 10 minutes
    T10 = float(ODDS_MINUTES)
    rtot = rh + ra
    if rtot <= 0:
        p_any10 = 0.0
        p_no10 = 1.0
        p_h10 = 0.0
        p_a10 = 0.0
    else:
        p_any10 = 1.0 - math.exp(-rtot * T10)
        p_no10 = math.exp(-rtot * T10)
        p_h10 = (rh / rtot) * p_any10
        p_a10 = (ra / rtot) * p_any10

    # remaining minutes to FT
    rem = max(0, 90 - minute)
    lam_h = rh * rem
    lam_a = ra * rem
    p_h_scores = 1.0 - math.exp(-lam_h) if lam_h > 0 else 0.0
    p_a_scores = 1.0 - math.exp(-lam_a) if lam_a > 0 else 0.0

    score_home = int(row.get("score_home") or 0)
    score_away = int(row.get("score_away") or 0)

    if score_home > 0 and score_away > 0:
        p_btts = 1.0
    elif score_home > 0 and score_away == 0:
        p_btts = p_a_scores
    elif score_home == 0 and score_away > 0:
        p_btts = p_h_scores
    else:
        p_btts = p_h_scores * p_a_scores

    # FT over/under 2.5: additional goals N~Poisson(lam_tot)
    lam_tot = (rh + ra) * rem
    current_total = score_home + score_away
    need = max(0, 3 - current_total)  # goals needed to reach >=3
    p_over25 = _poisson_tail_ge(need, lam_tot)

    return {
        "p_goal10_any": float(max(0.0, min(1.0, p_any10))),
        "p_next10_home": float(max(0.0, min(1.0, p_h10))),
        "p_next10_away": float(max(0.0, min(1.0, p_a10))),
        "p_next10_nogoal": float(max(0.0, min(1.0, p_no10))),
        "p_btts": float(max(0.0, min(1.0, p_btts))),
        "p_over25": float(max(0.0, min(1.0, p_over25))),
    }


# =========================================================
# POLLER LOOP (single writer thread)
# =========================================================
def poller_loop(stop_event: threading.Event) -> None:
    client = ApiFootballClient(BASE_URL)
    con = db_connect_writer()

    while not stop_event.is_set():
        last_error = ""
        rows: List[Dict[str, Any]] = []
        stats_calls = 0
        live_all = 0
        matched_live = 0
        odds_ok = 0
        events_ok = 0

        try:
            live = fetch_live_fixtures(client)
            live_all = len(live)

            matched = [fx for fx in live if is_target_fixture(fx)]
            if not matched:
                matched = [fx for fx in live if country_fallback_fixture(fx)]
            matched_live = len(matched)

            if len(matched) > MAX_FIXTURES_PROCESS:
                matched = matched[:MAX_FIXTURES_PROCESS]

            base_rows: List[Dict[str, Any]] = []
            with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
                futs = [ex.submit(build_base_row, client, fx) for fx in matched]
                for f in as_completed(futs):
                    stats_calls += 1
                    r = f.result()
                    if r:
                        base_rows.append(r)

            for r in base_rows:
                ensure_ht_snapshot(con, r)

            rows = [enrich_strengths(con, r) for r in base_rows]

            rows.sort(
                key=lambda x: (
                    float(x.get("active_goalsoon", 0.0)),
                    abs(float(x.get("active_edge", 0.0))),
                    int(x.get("minute", 0))
                ),
                reverse=True
            )

            db_replace_live_current(con, rows)
            db_append_history(con, rows)
            db_prune_history(con, HISTORY_KEEP_HOURS)

            # ===== Tracking: save + settle (NO extra API) =====
            try:
                _exec_retry(con, "BEGIN IMMEDIATE;")
                db_insert_signals(con, rows, SIGNAL_HORIZON_MIN)
                db_settle_signals_from_history(con, limit=250)
                _exec_retry(con, "COMMIT;")
            except Exception:
                _exec_retry(con, "ROLLBACK;")

            # ===== Odds cache (1 call / cycle) =====
            if ODDS_ENABLED:
                try:
                    odds_resp = fetch_live_odds_all(client)
                    odds_map = odds_list_to_map(odds_resp)
                    odds_rows: List[Dict[str, Any]] = []
                    ts_utc = datetime.utcnow().isoformat(timespec="seconds")

                    for r in rows[:ODDS_TOP_FIXTURES]:
                        fid = int(r.get("fixture_id"))
                        item = odds_map.get(fid)
                        if not item:
                            continue
                        best = parse_best_odds_for_fixture(item, str(r.get("home") or ""), str(r.get("away") or ""))
                        best_row = {
                            "fixture_id": fid,
                            "ts_utc": ts_utc,
                            "odds_goal10_yes": best.get("odds_goal10_yes"),
                            "odds_goal10_no": best.get("odds_goal10_no"),
                            "odds_next10_home": best.get("odds_next10_home"),
                            "odds_next10_away": best.get("odds_next10_away"),
                            "odds_next10_nogoal": best.get("odds_next10_nogoal"),
                            "odds_btts_yes": best.get("odds_btts_yes"),
                            "odds_btts_no": best.get("odds_btts_no"),
                            "odds_over25": best.get("odds_over25"),
                            "odds_under25": best.get("odds_under25"),
                            "odds_json": json.dumps(item, ensure_ascii=False),
                        }
                        odds_rows.append(best_row)

                    db_replace_odds_current(con, odds_rows)
                    odds_ok = 1 if len(odds_rows) > 0 else 0
                except Exception:
                    odds_ok = 0

            # ===== Events cache (limited calls / cycle) =====
            try:
                # cache events for "interesting" matches (tiers) + top threats
                cand = [r for r in rows if str(r.get("tier")) in {"MED", "STRONG"}]
                if len(cand) < 12:
                    cand = rows[:12]
                cand = cand[:25]

                with ThreadPoolExecutor(max_workers=min(6, MAX_WORKERS)) as ex:
                    futs = []
                    for r in cand:
                        fid = int(r.get("fixture_id"))
                        futs.append(ex.submit(fetch_fixture_events, client, fid))
                    for r, f in zip(cand, futs):
                        try:
                            ev = f.result()
                            db_upsert_events(con, int(r.get("fixture_id")), int(r.get("minute") or 0), ev)
                        except Exception:
                            continue

                events_ok = 1
            except Exception:
                events_ok = 0

        except Exception as e:
            last_error = str(e)

        try:
            db_set_status(
                con,
                datetime.utcnow().isoformat(timespec="seconds"),
                last_error,
                len(rows),
                stats_calls,
                live_all,
                matched_live,
                odds_ok,
                events_ok,
            )
        except Exception:
            pass

        for _ in range(POLL_SECONDS):
            if stop_event.is_set():
                break
            time.sleep(1)

    con.close()


# =========================================================
# STREAMLIT UI
# =========================================================
st.set_page_config(page_title="GoalMind LIVE", layout="wide")
st.title("⚡ GoalMind LIVE — Goal Threat Radar (1H/2H + Momentum)")
st.caption("LIVE Goal Threat Radar — informational tool, no profit guarantee.")
st.caption("Deploy tip: if you ever see DB lock/old columns, delete `live_store.sqlite` OR bump `SCHEMA_VERSION` to reset DB.")

with st.expander("ℹ️ How to use (quick guide)", expanded=False):
        st.markdown(
        f"""
**What this is:** A live “goal threat radar” built from live match stats (shots, shots on target, box shots, corners, xG when available), split into **1H / 2H**, plus **momentum** (change since the last poll).

**Key columns**
- **Active Half:** which half is being evaluated right now (1H or 2H).
- **Active Strength (Home/Away):** attacking pressure score per team (higher = more threat).
- **Active Edge:** normalized difference between teams (positive = home stronger, negative = away stronger).
- **GoalSoon:** probability-like score (0–1) for a goal in the next **~{ODDS_MINUTES} minutes** (derived from total strength).
- **Pick:** HOME / AWAY when one side is clearly stronger (uses Pick Margin).
- **Tier:** WATCH / MED / STRONG based on GoalSoon + Edge + Pick.

**Odds + Value (if your plan supports `/odds/live`)**
- **Odds*** columns show the best live odds we can find for that market.
- **Model P** columns are model probabilities derived from the live strength.
- **Edge / EV** compare model vs odds:
  - `Edge = ModelP - (1/Odds)`
  - `EV = ModelP*Odds - 1` (positive = value)

**Events**
- The match events panel uses cached events (goals/cards/subs) so you can see what just happened without spamming the API.

**Refresh**
- UI refreshes every **30s** (no API calls; reads SQLite).
- Poller fetches live data every **{POLL_SECONDS}s** (real API calls).

**Disclaimer:** informational tool only — no guaranteed profit; not financial advice.
        """
    )


if not load_api_key():
    st.error("Missing API key. Add API_FOOTBALL_KEY to .streamlit/secrets.toml")
    st.stop()


def init_db():
    db_init_once()
    return True


@st.cache_resource
def start_poller_cached() -> threading.Event:
    stop = threading.Event()
    t = threading.Thread(target=poller_loop, args=(stop,), daemon=True)
    t.start()
    return stop


_ = init_db()
_ = start_poller_cached()

if st_autorefresh:
    st_autorefresh(interval=UI_REFRESH_MS, key="ui_refresh")

# =========================
# Stripe Paywall (optional)
# =========================
cfg = stripe_cfg()
if "is_paid" not in st.session_state:
    st.session_state["is_paid"] = False
if "paid_email" not in st.session_state:
    st.session_state["paid_email"] = ""

# read session_id from query params
session_id = None
try:
    qp = st.query_params
    session_id = qp.get("session_id")
except Exception:
    try:
        qp2 = st.experimental_get_query_params()
        session_id = (qp2.get("session_id") or [None])[0]
    except Exception:
        session_id = None

if session_id:
    email_paid = stripe_handle_return(str(session_id))
    if email_paid:
        st.session_state["paid_email"] = email_paid
        st.session_state["is_paid"] = True

with st.sidebar:
    st.subheader("Settings")

    # Model filters
    min_score = st.slider("Min GoalSoon (0 = show all)", 0.0, 1.0, 0.00, 0.01)
    only_pick = st.checkbox("Only HOME/AWAY pick", value=False)
    show_more = st.checkbox("Show more stat columns", value=False)
    show_odds = st.checkbox("Show odds + value columns", value=False)

    st.caption(f"Schema v{SCHEMA_VERSION} | Poll {POLL_SECONDS}s | UI {UI_REFRESH_MS}ms")

    st.divider()
    st.subheader("Access")

    if paywall_enabled():
        if stripe is None:
            st.error("Stripe not installed. Run: pip install stripe")
            st.stop()

        bypass = cfg.get("admin_bypass") or ""
        admin_code = st.text_input("Admin bypass code (optional)", type="password")
        email = st.text_input("Email", value=st.session_state.get("paid_email", ""))

        if bypass and admin_code and admin_code == bypass:
            st.session_state["is_paid"] = True
            st.session_state["paid_email"] = email or "admin@local"
            st.success("Admin access granted ✅")

        if st.button("Check subscription / Login"):
            if email and stripe_check_subscription(email):
                st.session_state["is_paid"] = True
                st.session_state["paid_email"] = email
                st.success("Subscription active ✅")
            else:
                st.warning("No active subscription found for this email.")

        if st.button("Subscribe (Stripe Checkout)"):
            if not email:
                st.warning("Enter your email first.")
            else:
                url = stripe_create_checkout(email)
                if url:
                    st.link_button("Open Stripe Checkout", url)
                else:
                    st.error("Cannot create checkout. Check secrets.toml (Stripe keys / price / URLs).")

        if st.session_state.get("is_paid") and st.session_state.get("paid_email"):
            portal = stripe_create_portal(st.session_state["paid_email"])
            if portal:
                st.link_button("Manage billing", portal)

        if not st.session_state.get("is_paid"):
            st.info(f"Demo mode: top {DEMO_ROWS} rows only. Subscribe to unlock full Live + Performance.")
    else:
        st.session_state["is_paid"] = True
        st.caption("Paywall disabled (PAYWALL_ENABLED=false).")


# =========================
# Status + poller health
# =========================
status = db_read_status()
c1, c2, c3, c4, c5, c6, c7, c8 = st.columns(8)
c1.metric("Last run (UTC)", status.get("last_run_utc") or "-")
c2.metric("Rows", int(status.get("rows") or 0))
c3.metric("Stats calls", int(status.get("stats_calls") or 0))
c4.metric("live_all", int(status.get("live_all") or 0))
c5.metric("matched_live", int(status.get("matched_live") or 0))
c6.metric("Pick margin", PICK_MARGIN)
c7.metric("Odds", "OK" if int(status.get("odds_ok") or 0) == 1 else "—")
c8.metric("Events", "OK" if int(status.get("events_ok") or 0) == 1 else "—")

if status.get("last_error"):
    st.warning("Poller error: " + status["last_error"])

last = status.get("last_run_utc") or ""
try:
    dt = datetime.fromisoformat(last.replace("Z", ""))
    age = (datetime.utcnow() - dt).total_seconds()
    if age <= POLL_SECONDS * 1.2:
        st.success(f"✅ Poller is running (last refresh {int(age)}s ago)")
    else:
        st.warning(f"⚠️ Poller not refreshing (last refresh {int(age)}s ago)")
except Exception:
    st.caption(f"Poller time parse: {last}")

df = db_read_current()
if len(df) == 0:
    st.warning("No LIVE matches in table yet (or API currently has none in target leagues).")
    st.stop()

# merge odds
try:
    df_odds = db_read_odds_current()
    if not df_odds.empty:
        df = df.merge(df_odds.drop(columns=["ts_utc"], errors="ignore"), on="fixture_id", how="left")
except Exception:
    pass

# Safe numeric columns
for col in ["active_goalsoon", "active_edge",
            "active_strength_home", "active_strength_away",
            "momentum_home", "momentum_away",
            "goalsoon_1h", "goalsoon_2h",
            "strength_1h_home", "strength_1h_away",
            "strength_2h_home", "strength_2h_away",
            "xg_home", "xg_away",
            "poss_home", "poss_away",
            "passpct_home", "passpct_away",
            "odds_goal10_yes", "odds_next10_home", "odds_next10_away", "odds_btts_yes", "odds_over25"]:
    if col in df.columns:
        df[col] = pd.to_numeric(df[col], errors="coerce")

# Filters
df = df[df["active_goalsoon"] >= float(min_score)]
if only_pick:
    df = df[df["active_pick"].isin(["HOME", "AWAY"])]

df = df.sort_values(["active_goalsoon", "active_edge", "minute"], ascending=[False, False, False]).copy()

# Compute value columns (row-wise; small tables)
if show_odds:
    mp_cols = ["model_p_goal10", "edge_goal10", "ev_goal10",
               "model_p_pick_next10", "odds_pick_next10", "edge_pick_next10", "ev_pick_next10",
               "model_p_btts", "edge_btts", "ev_btts",
               "model_p_over25", "edge_over25", "ev_over25"]
    for c in mp_cols:
        df[c] = None

    def _row_value(r: pd.Series) -> pd.Series:
        d = r.to_dict()
        mp = model_probs(d)

        # goal in next 10 (any)
        odd = d.get("odds_goal10_yes")
        if odd and odd > 1:
            imp = 1.0 / float(odd)
            p = mp["p_goal10_any"]
            d["model_p_goal10"] = p
            d["edge_goal10"] = p - imp
            d["ev_goal10"] = p * float(odd) - 1.0

        # pick next goal (within 10) using next-goal market odds (best-effort)
        pick = str(d.get("active_pick") or "").upper()
        if pick == "HOME":
            oddp = d.get("odds_next10_home")
            p = mp["p_next10_home"]
        elif pick == "AWAY":
            oddp = d.get("odds_next10_away")
            p = mp["p_next10_away"]
        else:
            oddp = None
            p = None

        if oddp and oddp > 1 and p is not None:
            imp = 1.0 / float(oddp)
            d["model_p_pick_next10"] = p
            d["odds_pick_next10"] = float(oddp)
            d["edge_pick_next10"] = p - imp
            d["ev_pick_next10"] = p * float(oddp) - 1.0

        # BTTS yes
        odd = d.get("odds_btts_yes")
        if odd and odd > 1:
            imp = 1.0 / float(odd)
            p = mp["p_btts"]
            d["model_p_btts"] = p
            d["edge_btts"] = p - imp
            d["ev_btts"] = p * float(odd) - 1.0

        # Over 2.5
        odd = d.get("odds_over25")
        if odd and odd > 1:
            imp = 1.0 / float(odd)
            p = mp["p_over25"]
            d["model_p_over25"] = p
            d["edge_over25"] = p - imp
            d["ev_over25"] = p * float(odd) - 1.0

        return pd.Series(d)

    try:
        df = df.apply(_row_value, axis=1)
    except Exception:
        pass

# Columns (readability)
base_cols = [
    "league_country", "league", "minute", "status",
    "home", "away", "score_home", "score_away",
    "tier",
    "active_half", "active_pick", "active_goalsoon",
    "active_strength_home", "active_strength_away", "active_edge",
    "momentum_home", "momentum_away",
    "pick_1h", "goalsoon_1h",
    "pick_2h", "goalsoon_2h",
]
odds_cols = [
    "odds_goal10_yes", "model_p_goal10", "edge_goal10", "ev_goal10",
    "odds_pick_next10", "model_p_pick_next10", "edge_pick_next10", "ev_pick_next10",
    "odds_btts_yes", "model_p_btts", "edge_btts", "ev_btts",
    "odds_over25", "model_p_over25", "edge_over25", "ev_over25",
]
more_cols = [
    "totshots_home", "sot_home", "soff_home", "inside_home", "corners_home", "poss_home", "passpct_home", "xg_home", "red_home", "yel_home",
    "totshots_away", "sot_away", "soff_away", "inside_away", "corners_away", "poss_away", "passpct_away", "xg_away", "red_away", "yel_away"
]
cols = base_cols + (odds_cols if show_odds else []) + (more_cols if show_more else []) + ["fixture_id"]
cols = [c for c in cols if c in df.columns]

# Formatting
DEC2 = [
    "active_goalsoon", "active_edge",
    "active_strength_home", "active_strength_away",
    "momentum_home", "momentum_away",
    "goalsoon_1h", "goalsoon_2h",
    "poss_home", "poss_away",
    "passpct_home", "passpct_away",
    "xg_home", "xg_away",
    "odds_goal10_yes", "odds_pick_next10", "odds_btts_yes", "odds_over25",
    "model_p_goal10", "edge_goal10", "ev_goal10",
    "model_p_pick_next10", "edge_pick_next10", "ev_pick_next10",
    "model_p_btts", "edge_btts", "ev_btts",
    "model_p_over25", "edge_over25", "ev_over25",
]
DEC0 = [
    "totshots_home", "sot_home", "soff_home", "inside_home", "corners_home", "red_home", "yel_home",
    "totshots_away", "sot_away", "soff_away", "inside_away", "corners_away", "red_away", "yel_away",
    "minute", "score_home", "score_away"
]
fmt: Dict[str, str] = {}
for c in DEC2:
    if c in df.columns:
        fmt[c] = "{:.2f}"
for c in DEC0:
    if c in df.columns:
        fmt[c] = "{:.0f}"

# =========================
# Table-view columns (compact, league-friendly)
# =========================
# Used by the optional "Table view" block inside the Live tab.
# Keep it compact so it stays readable (and matches the example you sent).
cols_table: List[str] = [
    "league_country", "league",
    "minute", "status",
    "home", "away", "score_home", "score_away",
    "tier",
    "active_half", "active_pick", "active_goalsoon", "active_edge",
]

# If odds/value columns exist (and the user enabled odds), include the most useful ones.
if "show_odds" in locals() and bool(show_odds):
    cols_table += [
        # Next ~10 min goal
        "odds_goal10_yes", "edge_goal10", "ev_goal10",
        # OU2.5
        "odds_over25", "edge_over25", "ev_over25",
        # BTTS
        "odds_btts_yes", "edge_btts", "ev_btts",
        # Pick (team goal in next 10)
        "odds_pick_next10", "edge_pick_next10", "ev_pick_next10",
    ]

# Always keep fixture_id at the end if present (debug/support).
cols_table += ["fixture_id"]


def style_rows(row):
    styles = {c: "" for c in cols}

    tier = str(row.get("tier") or "")
    if tier == "STRONG":
        styles["tier"] = "background-color: rgba(0,200,0,0.28); font-weight: 900;"
    elif tier == "MED":
        styles["tier"] = "background-color: rgba(255,215,0,0.25); font-weight: 800;"
    else:
        styles["tier"] = "opacity: 0.9;"

    h = float(row.get("active_strength_home") or 0)
    a = float(row.get("active_strength_away") or 0)
    if h > a:
        styles["home"] = "background-color: rgba(0,200,0,0.18); font-weight: 700;"
        if "active_strength_home" in styles:
            styles["active_strength_home"] = "background-color: rgba(0,200,0,0.18); font-weight: 700;"
    elif a > h:
        styles["away"] = "background-color: rgba(0,200,0,0.18); font-weight: 700;"
        if "active_strength_away" in styles:
            styles["active_strength_away"] = "background-color: rgba(0,200,0,0.18); font-weight: 700;"

    pick = str(row.get("active_pick") or "").upper()
    if pick in {"HOME", "AWAY"}:
        styles["active_pick"] = "background-color: rgba(0,200,0,0.22); font-weight: 900;"
        styles["active_goalsoon"] = "background-color: rgba(0,200,0,0.18); font-weight: 900;"

    if str(row.get("active_half") or "") == "2H":
        styles["active_half"] = "background-color: rgba(120,180,255,0.18); font-weight: 800;"

    # Value highlight (optional)
    if show_odds:
        for c in ["ev_goal10", "ev_pick_next10", "ev_btts", "ev_over25"]:
            try:
                v = row.get(c)
                if v is not None and float(v) >= 0.10:
                    styles[c] = "background-color: rgba(0,200,0,0.18); font-weight: 900;"
                elif v is not None and float(v) <= -0.10:
                    styles[c] = "background-color: rgba(255,80,80,0.16);"
            except Exception:
                pass

    return [styles.get(c, "") for c in cols]


# =========================
# Tabs
# =========================
tab_live, tab_perf = st.tabs(["Live Radar", "Performance (Proof)"])

with tab_live:
    # ---------- App-like styling ----------
    st.markdown(
        """
        <style>
            .gm-shell {background: rgba(0,0,0,0.08); border: 1px solid rgba(255,255,255,0.08);
                       border-radius: 16px; padding: 14px 14px 10px 14px;}
            .gm-card {background: rgba(20,25,35,0.55); border: 1px solid rgba(255,255,255,0.08);
                      border-radius: 16px; padding: 14px;}
            .gm-title {font-size: 18px; font-weight: 800; margin: 0 0 6px 0;}
            .gm-sub {opacity: 0.85; margin: 0 0 10px 0;}
            .gm-pill {display: inline-block; padding: 4px 10px; border-radius: 999px;
                      border: 1px solid rgba(255,255,255,0.12); font-size: 12px; opacity: 0.95;}
            .gm-row {display:flex; justify-content:space-between; gap:10px; align-items:center;}
            .gm-kv {display:flex; flex-direction:column; gap:2px;}
            .gm-k {font-size: 12px; opacity: 0.75;}
            .gm-v {font-size: 16px; font-weight: 800;}
            .gm-bar {height: 10px; border-radius: 999px; background: rgba(255,255,255,0.10); overflow: hidden;}
            .gm-bar > div {height: 10px; border-radius: 999px; background: rgba(0,200,0,0.55);}
            .gm-muted {opacity:0.78; font-size: 12px;}
            .gm-list {max-height: 72vh; overflow: auto; padding-right: 6px;}
            .gm-divider {height: 1px; background: rgba(255,255,255,0.08); margin: 10px 0;}
        </style>
        """,
        unsafe_allow_html=True,
    )

    st.subheader("🔥 LIVE Radar — app-style view")
    st.caption("Left: matches list • Center: match overview • Right: team panel.")

    # Demo mode: limit rows
    if paywall_enabled() and not st.session_state.get("is_paid"):
        df_view = df.head(DEMO_ROWS).copy()
        st.info(f"Demo mode: showing top {DEMO_ROWS} matches. Subscribe to unlock full list, details and Performance.")
    else:
        df_view = df.copy()

    # ---------- Filters for the list ----------
    # (These are *additional* filters, on top of the sidebar filters)
    leagues_all = (df_view["league_country"].fillna("") + " • " + df_view["league"].fillna("")).unique().tolist()
    leagues_all = [x for x in leagues_all if x.strip()]
    leagues_all = sorted(leagues_all)

    left, mid, right = st.columns([1.25, 1.75, 1.15], gap="large")

    with left:
        st.markdown("<div class='gm-shell'>", unsafe_allow_html=True)
        st.markdown("<div class='gm-title'>Matches</div>", unsafe_allow_html=True)

        q = st.text_input("Search team / league", value="", placeholder="e.g. Arsenal, Serie A, Croatia…")
        league_pick = st.multiselect("League filter", options=leagues_all, default=[])

        # quick sort toggle
        sort_mode = st.selectbox("Sort by", ["GoalSoon (desc)", "Minute (desc)"], index=0)

        view = df_view.copy()
        if q.strip():
            qq = q.strip().casefold()
            mask = (
                view["home"].fillna("").str.casefold().str.contains(qq)
                | view["away"].fillna("").str.casefold().str.contains(qq)
                | view["league"].fillna("").str.casefold().str.contains(qq)
                | view["league_country"].fillna("").str.casefold().str.contains(qq)
            )
            view = view[mask].copy()

        if league_pick:
            key = view["league_country"].fillna("") + " • " + view["league"].fillna("")
            view = view[key.isin(league_pick)].copy()

        if view.empty:
            st.warning("No matches after filters.")
            st.markdown("</div>", unsafe_allow_html=True)
            st.stop()

        if sort_mode.startswith("Minute"):
            view = view.sort_values(["minute", "active_goalsoon"], ascending=[False, False])
        else:
            view = view.sort_values(["active_goalsoon", "active_edge", "minute"], ascending=[False, False, False])

        # Build labels
        def _label(r: pd.Series) -> str:
            country = str(r.get("league_country") or "")
            league = str(r.get("league") or "")
            home = str(r.get("home") or "")
            away = str(r.get("away") or "")
            minute = int(r.get("minute") or 0)
            sh = int(r.get("score_home") or 0)
            sa = int(r.get("score_away") or 0)
            tier = str(r.get("tier") or "")
            gs = float(r.get("active_goalsoon") or 0.0)
            # compact label
            return f"{home} vs {away}  •  {sh}-{sa}  •  {minute}'  •  {tier}  •  GS {gs:.2f}\n{country} • {league}"

        labels = [ _label(row) for _, row in view.iterrows() ]
        ids = view["fixture_id"].astype(int).tolist()

        # Persist selection across refresh
        if "selected_live_fid" not in st.session_state:
            st.session_state["selected_live_fid"] = ids[0]

        # If the selected match disappeared (filters), reset to first
        if st.session_state["selected_live_fid"] not in ids:
            st.session_state["selected_live_fid"] = ids[0]

        idx = ids.index(st.session_state["selected_live_fid"])
        st.markdown("<div class='gm-list'>", unsafe_allow_html=True)
        sel_fid = st.radio(
            " ",
            options=ids,
            index=idx,
            format_func=lambda fid: labels[ids.index(fid)],
            label_visibility="collapsed",
        )
        st.markdown("</div>", unsafe_allow_html=True)
        st.session_state["selected_live_fid"] = int(sel_fid)

        with st.expander("Table view (optional)", expanded=False):
            # keep old styled table for power users
            tbl = view[cols].copy() if all(c in view.columns for c in cols) else view.copy()
            try:
                st.dataframe(tbl.style.format(fmt).apply(style_rows, axis=1), use_container_width=True, hide_index=True)
            except Exception:
                st.dataframe(tbl, use_container_width=True, hide_index=True)

        st.markdown("</div>", unsafe_allow_html=True)

    # ---------- Selected match ----------
    sel_row = df_view[df_view["fixture_id"].astype(int) == int(st.session_state["selected_live_fid"])]
    if sel_row.empty:
        sel_row = df_view.iloc[[0]]
    row = sel_row.iloc[0].to_dict()

    home = str(row.get("home") or "")
    away = str(row.get("away") or "")
    sh = int(row.get("score_home") or 0)
    sa = int(row.get("score_away") or 0)
    minute = int(row.get("minute") or 0)
    status_short = str(row.get("status") or "")
    country = str(row.get("league_country") or "")
    league = str(row.get("league") or "")

    tier = str(row.get("tier") or "")
    pick = str(row.get("active_pick") or "")
    gs = float(row.get("active_goalsoon") or 0.0)
    edge = float(row.get("active_edge") or 0.0)

    def _pct(x: float) -> int:
        return int(max(0, min(100, round(float(x) * 100))))

    def _bar(p: int) -> str:
        return f"<div class='gm-bar'><div style='width:{p}%;'></div></div>"

    with mid:
        st.markdown("<div class='gm-card'>", unsafe_allow_html=True)
        st.markdown(f"<div class='gm-title'>{home} <span class='gm-muted'>vs</span> {away}</div>", unsafe_allow_html=True)
        st.markdown(
            f"<div class='gm-sub'>{country} • {league} &nbsp;|&nbsp; <span class='gm-pill'>{status_short}</span> &nbsp; <span class='gm-pill'>{minute}'</span></div>",
            unsafe_allow_html=True,
        )
        st.markdown(f"<div class='gm-row'><div class='gm-kv'><div class='gm-k'>Score</div><div class='gm-v'>{sh} - {sa}</div></div>" 
                    f"<div class='gm-kv'><div class='gm-k'>Tier</div><div class='gm-v'>{tier}</div></div>"
                    f"<div class='gm-kv'><div class='gm-k'>Pick</div><div class='gm-v'>{pick}</div></div>"
                    f"</div>",
                    unsafe_allow_html=True)

        st.markdown("<div class='gm-divider'></div>", unsafe_allow_html=True)

        # GoalSoon
        st.markdown(f"<div class='gm-row'><div><b>GoalSoon</b> <span class='gm-muted'>(probability-like)</span></div><div><b>{gs:.2f}</b></div></div>", unsafe_allow_html=True)
        st.markdown(_bar(_pct(gs)), unsafe_allow_html=True)

        st.markdown(f"<div class='gm-row' style='margin-top:8px;'><div><b>Edge</b> <span class='gm-muted'>(+home, -away)</span></div><div><b>{edge:+.2f}</b></div></div>", unsafe_allow_html=True)
        # Edge bar: map [-1,1] to 0..100
        edge_p = _pct((edge + 1.0) / 2.0)
        st.markdown(_bar(edge_p), unsafe_allow_html=True)

        st.markdown("</div>", unsafe_allow_html=True)

        # Tabs inside middle panel
        t_over, t_stats, t_json = st.tabs(["Overview", "Stats", "JSON"])

        with t_over:
            c1, c2, c3, c4 = st.columns(4)
            c1.metric("Active Half", str(row.get("active_half") or ""))
            c2.metric("Strength (H)", float(row.get("active_strength_home") or 0.0))
            c3.metric("Strength (A)", float(row.get("active_strength_away") or 0.0))
            c4.metric("Momentum", f"{float(row.get('momentum_home') or 0.0):.2f} / {float(row.get('momentum_away') or 0.0):.2f}")

            st.caption("Momentum ≈ attacking pressure in the last polling window (with POLL_SECONDS=300 that's ~5 minutes).")

            st.markdown("**Half split**")
            hh1, hh2, hh3, hh4 = st.columns(4)
            hh1.metric("1H pick", str(row.get("pick_1h") or ""))
            hh2.metric("1H GoalSoon", float(row.get("goalsoon_1h") or 0.0))
            hh3.metric("2H pick", str(row.get("pick_2h") or ""))
            hh4.metric("2H GoalSoon", float(row.get("goalsoon_2h") or 0.0))

        with t_stats:
            # Minimal “match center” stats table
            stats_rows = [
                ("Total shots", int(row.get("totshots_home") or 0), int(row.get("totshots_away") or 0)),
                ("Shots on target", int(row.get("sot_home") or 0), int(row.get("sot_away") or 0)),
                ("Shots inside box", int(row.get("inside_home") or 0), int(row.get("inside_away") or 0)),
                ("Corners", int(row.get("corners_home") or 0), int(row.get("corners_away") or 0)),
                ("Possession %", float(row.get("poss_home") or 0.0), float(row.get("poss_away") or 0.0)),
                ("Pass acc %", float(row.get("passpct_home") or 0.0), float(row.get("passpct_away") or 0.0)),
                ("xG (if provided)", float(row.get("xg_home") or 0.0), float(row.get("xg_away") or 0.0)),
                ("Yellow cards", int(row.get("yel_home") or 0), int(row.get("yel_away") or 0)),
                ("Red cards", int(row.get("red_home") or 0), int(row.get("red_away") or 0)),
            ]
            st.dataframe(
                pd.DataFrame(stats_rows, columns=["Metric", home, away]),
                use_container_width=True,
                hide_index=True,
            )

        with t_json:
            if paywall_enabled() and not st.session_state.get("is_paid"):
                st.info("JSON details are locked in demo mode.")
            else:
                with st.expander("HOME raw stats JSON", expanded=False):
                    try:
                        st.json(json.loads(row.get("stats_json_home") or "{}"))
                    except Exception:
                        st.write("JSON parse error.")
                with st.expander("AWAY raw stats JSON", expanded=False):
                    try:
                        st.json(json.loads(row.get("stats_json_away") or "{}"))
                    except Exception:
                        st.write("JSON parse error.")

    # ---------- Right panel: team card ----------
    with right:
        st.markdown("<div class='gm-shell'>", unsafe_allow_html=True)
        st.markdown("<div class='gm-title'>Team Panel</div>", unsafe_allow_html=True)

        team_sel = st.radio("Team", ["HOME", "AWAY"], horizontal=True)
        is_home = team_sel == "HOME"

        team = home if is_home else away
        strength = float(row.get("active_strength_home") if is_home else row.get("active_strength_away") or 0.0)
        mom = float(row.get("momentum_home") if is_home else row.get("momentum_away") or 0.0)

        tot = int(row.get("totshots_home") if is_home else row.get("totshots_away") or 0)
        sot = int(row.get("sot_home") if is_home else row.get("sot_away") or 0)
        inside = int(row.get("inside_home") if is_home else row.get("inside_away") or 0)
        corners = int(row.get("corners_home") if is_home else row.get("corners_away") or 0)

        poss = float(row.get("poss_home") if is_home else row.get("poss_away") or 0.0)
        passpct = float(row.get("passpct_home") if is_home else row.get("passpct_away") or 0.0)
        xg = float(row.get("xg_home") if is_home else row.get("xg_away") or 0.0)

        yel = int(row.get("yel_home") if is_home else row.get("yel_away") or 0)
        red = int(row.get("red_home") if is_home else row.get("red_away") or 0)

        st.markdown(f"<div class='gm-card'><div class='gm-title'>{team}</div>", unsafe_allow_html=True)
        st.markdown(f"<div class='gm-sub'><span class='gm-pill'>{team_sel}</span> &nbsp; <span class='gm-pill'>Strength {strength:.2f}</span></div>", unsafe_allow_html=True)

        # simple “ratings”
        atk_score = min(1.0, max(0.0, (strength / 4.0)))
        mom_score = min(1.0, max(0.0, (mom / 3.0)))
        control_score = min(1.0, max(0.0, (0.5 * (poss / 100.0) + 0.5 * (passpct / 100.0))))

        st.markdown(f"<div class='gm-row'><div>Attack</div><div><b>{atk_score:.2f}</b></div></div>", unsafe_allow_html=True)
        st.markdown(_bar(_pct(atk_score)), unsafe_allow_html=True)

        st.markdown(f"<div class='gm-row' style='margin-top:8px;'><div>Momentum</div><div><b>{mom_score:.2f}</b></div></div>", unsafe_allow_html=True)
        st.markdown(_bar(_pct(mom_score)), unsafe_allow_html=True)

        st.markdown(f"<div class='gm-row' style='margin-top:8px;'><div>Control</div><div><b>{control_score:.2f}</b></div></div>", unsafe_allow_html=True)
        st.markdown(_bar(_pct(control_score)), unsafe_allow_html=True)

        st.markdown("<div class='gm-divider'></div>", unsafe_allow_html=True)

        st.markdown("""<div class='gm-row'><div class='gm-kv'><div class='gm-k'>Shots (total / SOT)</div><div class='gm-v'>%d / %d</div></div>
                         <div class='gm-kv'><div class='gm-k'>Inside box</div><div class='gm-v'>%d</div></div></div>""" % (tot, sot, inside), unsafe_allow_html=True)
        st.markdown("""<div class='gm-row' style='margin-top:10px;'><div class='gm-kv'><div class='gm-k'>Corners</div><div class='gm-v'>%d</div></div>
                         <div class='gm-kv'><div class='gm-k'>xG</div><div class='gm-v'>%.2f</div></div></div>""" % (corners, xg), unsafe_allow_html=True)
        st.markdown("""<div class='gm-row' style='margin-top:10px;'><div class='gm-kv'><div class='gm-k'>Possession</div><div class='gm-v'>%.0f%%</div></div>
                         <div class='gm-kv'><div class='gm-k'>Pass acc</div><div class='gm-v'>%.0f%%</div></div></div>""" % (poss, passpct), unsafe_allow_html=True)
        st.markdown("""<div class='gm-row' style='margin-top:10px;'><div class='gm-kv'><div class='gm-k'>Cards (Y / R)</div><div class='gm-v'>%d / %d</div></div></div>""" % (yel, red), unsafe_allow_html=True)

        st.markdown("</div></div>", unsafe_allow_html=True)
    # =========================================================
    # Table view (optional) — grouped by league, more visible
    # =========================================================
    st.divider()
    st.markdown("### 📋 League table view (optional)")
    st.caption("Grouped tables are useful for quick scanning inside one league (e.g., Championship).")

    show_table_bottom = st.checkbox("Show table view below", value=False, key="show_table_view_bottom")
    if show_table_bottom:
        group_by_league = st.checkbox("Group by league", value=True, key="group_table_by_league")

        # Use the same filtered view as the cards (and respect demo/paywall if applied)
        _tbl_df = df_view.copy()

        # Columns for table view
        _cols_table = [c for c in cols_table if c in _tbl_df.columns]

        def _render_tbl(_df_in: pd.DataFrame, title: str = "") -> None:
            if title:
                st.markdown(f"#### {title}")
            if _df_in.empty:
                st.info("No matches in this group.")
                return
            def _style_rows_table(row):
                # Must return styles with the same length as _cols_table
                styles = {c: "" for c in _cols_table}

                tier = str(row.get("tier") or "")
                if "tier" in styles:
                    if tier == "STRONG":
                        styles["tier"] = "background-color: rgba(0,200,0,0.28); font-weight: 900;"
                    elif tier == "MED":
                        styles["tier"] = "background-color: rgba(255,215,0,0.25); font-weight: 800;"
                    else:
                        styles["tier"] = "opacity: 0.9;"

                h = float(row.get("active_strength_home") or 0)
                a = float(row.get("active_strength_away") or 0)
                if h > a:
                    if "home" in styles:
                        styles["home"] = "background-color: rgba(0,200,0,0.18); font-weight: 700;"
                    if "active_strength_home" in styles:
                        styles["active_strength_home"] = "background-color: rgba(0,200,0,0.18); font-weight: 700;"
                elif a > h:
                    if "away" in styles:
                        styles["away"] = "background-color: rgba(0,200,0,0.18); font-weight: 700;"
                    if "active_strength_away" in styles:
                        styles["active_strength_away"] = "background-color: rgba(0,200,0,0.18); font-weight: 700;"

                pick = str(row.get("active_pick") or "").upper()
                if pick in {"HOME", "AWAY"}:
                    if "active_pick" in styles:
                        styles["active_pick"] = "background-color: rgba(0,200,0,0.22); font-weight: 900;"
                    if "active_goalsoon" in styles:
                        styles["active_goalsoon"] = "background-color: rgba(0,200,0,0.18); font-weight: 900;"

                if str(row.get("active_half") or "") == "2H":
                    if "active_half" in styles:
                        styles["active_half"] = "background-color: rgba(120,180,255,0.18); font-weight: 800;"

                return [styles.get(c, "") for c in _cols_table]

            _view = _df_in[_cols_table].copy()

            # Safe numeric formatting (handles None/NaN so Styler won't crash)
            for _c in set(DEC2 + DEC0):
                if _c in _view.columns:
                    _view[_c] = pd.to_numeric(_view[_c], errors="coerce")

            def _fmt2(x):
                try:
                    return "" if pd.isna(x) else f"{float(x):.2f}"
                except Exception:
                    return ""

            def _fmt0(x):
                try:
                    return "" if pd.isna(x) else f"{float(x):.0f}"
                except Exception:
                    return ""

            _formatters = {}
            for _c in _view.columns:
                if _c in DEC2:
                    _formatters[_c] = _fmt2
                elif _c in DEC0:
                    _formatters[_c] = _fmt0

            _sty = _view.style.format(_formatters).apply(_style_rows_table, axis=1)

            # Extra visibility on the key numeric columns
            try:
                if "active_goalsoon" in _cols_table:
                    _sty = _sty.background_gradient(subset=["active_goalsoon"], cmap="Greens")
                if "active_edge" in _cols_table:
                    _sty = _sty.background_gradient(subset=["active_edge"], cmap="RdYlGn")
            except Exception:
                pass

            try:
                st.dataframe(_sty, use_container_width=True, hide_index=True)
            except Exception:
                st.write(_sty)

        if group_by_league and {"league", "league_country"}.issubset(set(_tbl_df.columns)):
            # Order leagues by volume (most matches first)
            grp_keys = ["league_country", "league"]
            leagues = (
                _tbl_df.groupby(grp_keys)
                .size()
                .sort_values(ascending=False)
                .reset_index(name="n")
            )
            for _, r in leagues.iterrows():
                country = str(r["league_country"] or "").strip()
                league = str(r["league"] or "").strip()
                name = league if league else "Unknown league"
                if country:
                    name = f"{name} — {country}"
                gdf = _tbl_df[(_tbl_df["league_country"] == r["league_country"]) & (_tbl_df["league"] == r["league"])].copy()

                # Small summary line (helps like your screenshot)
                strong_n = int((gdf.get("tier", "") == "STRONG").sum()) if "tier" in gdf.columns else 0
                med_n = int((gdf.get("tier", "") == "MED").sum()) if "tier" in gdf.columns else 0
                st.markdown(f"#### {name}")
                st.caption(f"Matches: {len(gdf)} • STRONG: {strong_n} • MED: {med_n}")
                _render_tbl(gdf)
                st.write("")  # spacing
        else:
            _render_tbl(_tbl_df, title="All matches")

with tab_perf:
    st.subheader("📈 Performance Tracking (Signals proof)")

    if paywall_enabled() and not st.session_state.get("is_paid"):
        st.warning("Subscribe to unlock Performance analytics.")
        st.stop()

    st.caption(
        f"Signals are logged when: tier in {sorted(SIGNAL_TIERS)} + pick HOME/AWAY + GoalSoon ≥ {SIGNAL_MIN_GOALSOON:.2f}. "
        f"Settled when a goal happens within ~{SIGNAL_HORIZON_MIN} minutes (±buffer)."
    )

    last_hours = st.slider("Lookback (hours)", 6, 336, 48, 6)
    df_sig = db_read_signals(last_hours=last_hours)

    if df_sig.empty:
        st.info("No signals logged yet (wait for some live games).")
        st.stop()

    settled = df_sig[df_sig["settled"] == 1].copy()
    pending = df_sig[df_sig["settled"] == 0].copy()

    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Signals (total)", len(df_sig))
    c2.metric("Settled", len(settled))
    c3.metric("Pending", len(pending))
    if len(settled) > 0:
        c4.metric("Pick-goal hit rate", f"{(settled['pick_goal'].mean()*100):.1f}%")
    else:
        c4.metric("Pick-goal hit rate", "-")

    if len(settled) > 0:
        st.markdown("#### By Tier")
        g = settled.groupby("tier").agg(
            signals=("id", "count"),
            pick_goal_rate=("pick_goal", "mean"),
            any_goal_rate=("any_goal", "mean"),
            avg_goalsoon=("goalsoon", "mean"),
        ).reset_index()
        g["pick_goal_rate"] = (g["pick_goal_rate"] * 100).round(1)
        g["any_goal_rate"] = (g["any_goal_rate"] * 100).round(1)
        g["avg_goalsoon"] = g["avg_goalsoon"].round(3)
        st.dataframe(g, use_container_width=True, hide_index=True)

        st.markdown("#### By League (top 25 by volume)")
        gl = settled.groupby(["league_country", "league"]).agg(
            signals=("id", "count"),
            pick_goal_rate=("pick_goal", "mean"),
            any_goal_rate=("any_goal", "mean"),
        ).reset_index()
        gl["pick_goal_rate"] = (gl["pick_goal_rate"] * 100).round(1)
        gl["any_goal_rate"] = (gl["any_goal_rate"] * 100).round(1)
        gl = gl.sort_values("signals", ascending=False).head(25)
        st.dataframe(gl, use_container_width=True, hide_index=True)

        st.markdown("#### By Half")
        gh = settled.groupby(["active_half", "tier"]).agg(
            signals=("id", "count"),
            pick_goal_rate=("pick_goal", "mean"),
        ).reset_index()
        gh["pick_goal_rate"] = (gh["pick_goal_rate"] * 100).round(1)
        st.dataframe(gh, use_container_width=True, hide_index=True)

    st.divider()
    st.markdown("#### Export")
    st.download_button(
        "Download signals CSV",
        data=df_sig.to_csv(index=False).encode("utf-8"),
        file_name="signals_tracking.csv",
        mime="text/csv"
    )
