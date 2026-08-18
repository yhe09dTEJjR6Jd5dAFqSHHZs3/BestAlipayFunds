                       
from __future__ import annotations

# ===== 标准库 / 全局配置 =====
import concurrent.futures
import ctypes
import datetime as _dt
import base64
import bisect
import calendar
import gzip
import hashlib
import hmac
import html
import io
import importlib
import json
import math
import platform
import struct
import os
import queue
import random
import sqlite3
import re
import statistics
import subprocess
import sys
import threading
import time
import tempfile
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path


APP_NAME = "Best Alipay Funds"
VERSION = "13.0.0"
LATEST_TIMEOUT = 4.0
LATEST_ATTEMPTS = 2
LATEST_BATCH_SIZE = 50
MIN_HISTORY_POINTS = 757
MIN_PYTHON = (3, 10)
BASE_DIR = Path(__file__).resolve().parent
CACHE_PATH = BASE_DIR / "BestAlipayFunds_cache.sqlite3"
MODEL_PATH = BASE_DIR / "BestAlipayFunds_AI.json"
ALIPAY_FILE_PATH = BASE_DIR / "BestAlipayFunds_AlipayAvailability.json"
SETTINGS_PATH = BASE_DIR / "BestAlipayFunds_Settings.json"
DEPS_DIR = BASE_DIR / "BestAlipayFunds_deps"
DEPS_TMP_DIR = BASE_DIR / "BestAlipayFunds_deps.tmp"
DEPS_BACKUP_DIR = BASE_DIR / "BestAlipayFunds_deps.rollback"
SETTINGS_SCHEMA_VERSION = 2
LOCAL_DEPENDENCY_PINS = (
    {
        "numpy": "numpy==2.5.2",
        "scipy": "scipy==1.18.0",
        "lightgbm": "lightgbm==4.7.0",
        "xgboost": "xgboost-cpu==3.4.1",
    }
    if sys.version_info >= (3, 12)
    else {
        "numpy": "numpy==2.2.6",
        "scipy": "scipy==1.15.3",
        "lightgbm": "lightgbm==4.7.0",
        "xgboost": "xgboost-cpu==3.4.1",
    }
)
QUICK_START_REPRESENTATIVES = 80

# Optional AI packages are intentionally loaded only from the script-local target directory.
# This keeps the user's global Python environment untouched.
if DEPS_DIR.is_dir():
    _deps_text = str(DEPS_DIR)
    if _deps_text not in sys.path:
        sys.path.insert(0, _deps_text)
ALIPAY_MAX_AGE_SECONDS = 30 * 60
DEFAULT_RISK_FREE_RATE = 0.015
OOS_DEPLOYMENT_WINDOWS = 6
OOS_UNTOUCHED_TEST_WINDOWS = 4
MIN_OOS_GATE_WINDOWS = 4
REFRESH_MIN_COVERAGE = 0.97
LATEST_PRIORITY_COUNT = 20
HISTORY_YEARS = 18
CACHE_VERSION = 17
MODEL_VERSION = 16
AVAILABILITY_SCHEMA_VERSION = 5
MIN_AVAILABILITY_FUNDS = 25
MAX_AVAILABILITY_FUTURE_SKEW_SECONDS = 5 * 60
MODEL_RETRAIN_DAYS = 7
MAX_HTTP_RESPONSE_BYTES = 16 * 1024 * 1024
MAX_HTTP_DECOMPRESSED_BYTES = 64 * 1024 * 1024
TARGET_HALF_YEAR_DAYS = 183
TARGET_ONE_YEAR_DAYS = 365
TARGET_THREE_YEAR_DAYS = 1096
TARGET_FIVE_YEAR_DAYS = 1826
MIN_HALF_YEAR_OBSERVATIONS = 100
MIN_ONE_YEAR_OBSERVATIONS = 200
MIN_THREE_YEAR_OBSERVATIONS = 600
MIN_FIVE_YEAR_OBSERVATIONS = 1000
TARGET_SPECS = (
    {"name":"3y-core-75", "horizon":"3y", "weights":{"6m":0.08,"1y":0.17,"3y":0.75}},
    {"name":"3y-core-85", "horizon":"3y", "weights":{"6m":0.05,"1y":0.10,"3y":0.85}},
    {"name":"5y-core-80", "horizon":"5y", "weights":{"6m":0.04,"1y":0.08,"3y":0.48,"5y":0.40}},
    {"name":"5y-core-90", "horizon":"5y", "weights":{"6m":0.02,"1y":0.05,"3y":0.48,"5y":0.45}},
)
LONG_TERM_BLEND_CANDIDATES = (0.75, 0.80, 0.85, 0.90)
METADATA_ENRICH_CANDIDATES = 240
HISTORY_CHECKPOINT_BATCH = 75
ASSET_MODEL_MIN_SAMPLES = 90
GLOBAL_ASSET_BLEND = 0.35
ASSET_SPECIFIC_BLEND = 0.65
FULL_NAV_REFRESH_SECONDS = 20 * 60
AVAILABILITY_REFRESH_SECONDS = 30 * 60
FRESH_NAV_MAX_MARKET_SESSIONS = 1
FINAL_FRESHNESS_COVERAGE = 0.95
FINAL_FRESHNESS_CANDIDATES = 30
PIT_RATING_MIN_UNIVERSE_COVERAGE = 0.25
PIT_RATING_MIN_OOS_WINDOWS = 4
SOURCE_CONTRACT_PROBES = ("000001", "110022", "161725")
PURCHASE_UNAVAILABLE_STATUSES = frozenset({"purchase_suspended", "closed", "confirmed_unavailable", "high_probability_unavailable", "unavailable"})
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36"
)

CHINA_TZ = _dt.timezone(_dt.timedelta(hours=8))


def _china_today() -> _dt.date:
    """Single China-market calendar date entry point; independent of the Windows local timezone."""
    return _dt.datetime.now(tz=CHINA_TZ).date()


def _availability_max_age_seconds(now: _dt.datetime | None = None) -> int:
    now_cn = (now or _dt.datetime.now(tz=CHINA_TZ)).astimezone(CHINA_TZ)
    minute = now_cn.hour * 60 + now_cn.minute
    if now_cn.weekday() >= 5:
        return 6 * 60 * 60
    if 9 * 60 <= minute < 23 * 60:
        return ALIPAY_MAX_AGE_SECONDS
    return 4 * 60 * 60


def _human_seconds(seconds: float) -> str:
    seconds = max(0, int(math.ceil(seconds)))
    if seconds < 60:
        return f"{seconds}秒"
    minutes, seconds = divmod(seconds, 60)
    if minutes < 60:
        return f"{minutes}分{seconds:02d}秒" if seconds else f"{minutes}分钟"
    hours, minutes = divmod(minutes, 60)
    return f"{hours}小时{minutes:02d}分"


class SmartRefreshPolicy:

    def __init__(self, rng=None):
        self.rng = rng or random.Random()
        self.error_streak = 0
        self.low_coverage_streak = 0
        self.stable_streak = 0
        self.last_delay = 0.0
        self.last_reason = "等待首次分析"

    @staticmethod
    def _latest_date(results: list[dict] | None) -> str:
        dates = [str(item.get("latest_date") or "")[:10] for item in (results or [])]
        dates = [value for value in dates if re.fullmatch(r"\d{4}-\d{2}-\d{2}", value)]
        return max(dates, default="")

    @staticmethod
    def _phase(now: _dt.datetime) -> tuple[str, float, float]:
        now = now.astimezone(CHINA_TZ)
        minute = now.hour * 60 + now.minute
        if now.weekday() >= 5:
            return "周末低活跃", 1800.0, 3600.0
        if 15 * 60 <= minute < 23 * 60:
            return "收盘净值披露", 300.0, 900.0
        if 9 * 60 <= minute < 15 * 60:
            return "交易时段", 600.0, 1200.0
        if 7 * 60 + 30 <= minute < 9 * 60:
            return "开盘前", 900.0, 1800.0
        return "低活跃时段", 1800.0, 3600.0


    @classmethod
    def _nav_pending(cls, results: list[dict] | None, now: _dt.datetime) -> bool:
        now_cn = now.astimezone(CHINA_TZ)
        if now_cn.weekday() >= 5 or now_cn.hour < 15:
            return False
        latest = cls._latest_date(results)
        return bool(latest and latest < now_cn.date().isoformat())

    def _jitter(self, seconds: float, spread: float = 0.08) -> float:
        return max(20.0, seconds * self.rng.uniform(1.0 - spread, 1.0 + spread))

    def _finish(self, seconds: float, reason: str, elapsed: float = 0.0) -> float:
        if elapsed > 0:
            seconds = max(seconds, min(900.0, elapsed * 6.0))
        self.last_delay = self._jitter(_clamp(seconds, 60.0, 3600.0))
        self.last_reason = reason
        return self.last_delay

    def initial_delay(self, results: list[dict] | None, now: _dt.datetime | None = None) -> float:
        now = now or _dt.datetime.now(tz=CHINA_TZ)
        phase, base, cap = self._phase(now)
        if self._nav_pending(results, now):
            base = min(base, 300.0)
            reason = f"{phase}·等待今日净值"
        else:
            reason = phase
        return self._finish(min(base, cap), reason)

    def on_success(self, outcome: dict, now: _dt.datetime | None = None) -> float:
        now = now or _dt.datetime.now(tz=CHINA_TZ)
        self.error_streak = 0
        coverage = _finite(outcome.get("coverage"), 0.0)
        elapsed = _finite(outcome.get("elapsed_seconds"), 0.0)
        results = outcome.get("results") or []
        changed = int(outcome.get("updated_series") or 0)
        pool_changes = len(outcome.get("new_codes") or []) + len(outcome.get("removed_codes") or [])

        if coverage < REFRESH_MIN_COVERAGE or outcome.get("ranking_updated") is False:
            self.low_coverage_streak += 1
            self.stable_streak = 0
            delay = min(1200.0, 180.0 * (2 ** min(self.low_coverage_streak - 1, 3)))
            detail = "Top候选不完整" if outcome.get("priority_complete") is False else f"覆盖率{coverage:.1%}"
            return self._finish(delay, f"{detail}·自适应退避重试", elapsed)

        self.low_coverage_streak = 0
        if pool_changes:
            self.stable_streak = 0
            return self._finish(180.0, f"可购池变化{pool_changes}项·快速复核", elapsed)
        if changed:
            self.stable_streak = 0
            delay = 300.0 if self._nav_pending(results, now) else 600.0
            return self._finish(delay, f"发现{changed}个新净值·快速复核", elapsed)

        self.stable_streak += 1
        phase, base, cap = self._phase(now)
        pending = self._nav_pending(results, now)
        if pending:
            base, cap = min(base, 300.0), min(cap, 900.0)
            reason = f"{phase}·今日净值待披露"
        else:
            if phase == "收盘净值披露":
                base = max(base, 600.0)
            reason = f"{phase}·数据稳定"
        multiplier = min(2.6, 1.0 + 0.28 * max(0, self.stable_streak - 1))
        return self._finish(min(cap, base * multiplier), reason, elapsed)

    def on_error(self, elapsed: float = 0.0) -> float:
        self.error_streak += 1
        self.low_coverage_streak = 0
        self.stable_streak = 0
        delay = min(1800.0, 180.0 * (2 ** min(self.error_streak - 1, 4)))
        return self._finish(delay, f"网络/数据失败×{self.error_streak}·指数退避", elapsed)



class DataError(RuntimeError):
    pass


def _now_iso() -> str:
    return _dt.datetime.now().astimezone().isoformat(timespec="seconds")


def _parse_iso(value: str | None) -> _dt.datetime | None:
    if not value:
        return None
    try:
        text = str(value).strip()
        if text.endswith("Z"):
            text = text[:-1] + "+00:00"
        return _dt.datetime.fromisoformat(text)
    except (TypeError, ValueError):
        return None


def _finite(value, default=0.0) -> float:
    try:
        number = float(value)
        return number if math.isfinite(number) else default
    except (TypeError, ValueError):
        return default


def _clamp(value: float, low: float, high: float) -> float:
    return max(low, min(high, value))


def _compound(values) -> float:
    total = 1.0
    for value in values:
        total *= max(0.01, 1.0 + _clamp(_finite(value), -0.95, 3.0))
    return total - 1.0


def _max_drawdown(values) -> float:
    wealth = 1.0
    peak = 1.0
    worst = 0.0
    for value in values:
        wealth *= max(0.01, 1.0 + _clamp(_finite(value), -0.95, 3.0))
        peak = max(peak, wealth)
        worst = min(worst, wealth / peak - 1.0)
    return worst


def _pearson(xs, ys) -> float:
    if len(xs) != len(ys) or len(xs) < 3:
        return 0.0
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    numerator = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    dx = sum((x - mx) ** 2 for x in xs)
    dy = sum((y - my) ** 2 for y in ys)
    if dx <= 1e-15 or dy <= 1e-15:
        return 0.0
    return numerator / math.sqrt(dx * dy)


def _spearman(xs, ys) -> float:
    if len(xs) != len(ys) or len(xs) < 3:
        return 0.0
    return _pearson(_rank_scale(xs), _rank_scale(ys))


def _median(values, default=0.0) -> float:
    clean = [_finite(v, float("nan")) for v in values]
    clean = [v for v in clean if math.isfinite(v)]
    return statistics.median(clean) if clean else default


def _chunks(values, size):
    for start in range(0, len(values), size):
        yield values[start:start + size]


def _rate(value, default=0.0) -> float:
    return _clamp(_finite(value, default), 0.0, 0.25)


def _risk_free_rate() -> float:
    return _clamp(_finite(os.environ.get("BEST_ALIPAY_RISK_FREE_RATE"), DEFAULT_RISK_FREE_RATE), -0.02, 0.08)


def _asset_bucket(name: str, fund_type: str) -> str:
    text = f"{name} {fund_type}".upper()
    if "QDII" in text or "海外" in text or any(word in text for word in ("纳斯达克", "标普", "全球", "恒生", "美国")):
        return "QDII/海外"
    coarse = _coarse_type(fund_type)
    if coarse == "债券":
        return "债券"
    if coarse == "指数":
        return "指数"
    if coarse in ("股票", "混合"):
        return "主动权益"
    return "其他"



def _holding_costs(fees: dict | None) -> dict:
    """Return explicit transaction-vs-embedded cost semantics.

    transaction_cost_* is purchase + redemption only. total_share_class_cost_* adds
    annual management/custody/sales-service costs. Legacy holding_cost_* aliases are
    retained only so old caches can be migrated without breaking a first launch.
    """
    if not isinstance(fees, dict):
        output = {"annual_cost": None, "embedded_annual_cost": None, "purchase_cost": None}
        for years in (3, 5, 10):
            output[f"transaction_cost_{years}y"] = None
            output[f"total_share_class_cost_{years}y"] = None
            output[f"holding_cost_{years}y"] = None
        return output

    def known_rate(key: str):
        value = fees.get(key)
        if value is None:
            return None
        return _rate(value)

    purchase = known_rate("purchase_fee")
    embedded_parts = [known_rate(key) for key in (
        "management_fee_annual", "custody_fee_annual", "sales_service_fee_annual",
    )]
    embedded_annual = sum(embedded_parts) if all(value is not None for value in embedded_parts) else None
    costs = {}
    for years in (3, 5, 10):
        redemption = known_rate(f"redemption_fee_{years}y")
        transaction = purchase + redemption if purchase is not None and redemption is not None else None
        total = transaction + years * embedded_annual if transaction is not None and embedded_annual is not None else None
        costs[f"transaction_cost_{years}y"] = transaction
        costs[f"total_share_class_cost_{years}y"] = total
        costs[f"holding_cost_{years}y"] = transaction  # legacy cache alias
    costs["annual_cost"] = embedded_annual
    costs["embedded_annual_cost"] = embedded_annual
    costs["purchase_cost"] = purchase
    return costs


def _expected_holding_years(value=None) -> int:
    try:
        years = int(value if value is not None else os.environ.get("BEST_ALIPAY_HOLDING_YEARS", "5"))
    except (TypeError, ValueError):
        years = 5
    return years if years in (3, 5, 10) else 5


def _share_class_cost(fund: dict, years: int) -> float:
    years = _expected_holding_years(years)
    if fund.get("fees_verified") is not True:
        return float("inf")
    fees = fund.get("fees") if isinstance(fund.get("fees"), dict) else {}
    required = (
        "purchase_fee", "management_fee_annual", "custody_fee_annual", "sales_service_fee_annual",
        f"redemption_fee_{years}y",
    )
    if any(fees.get(key) is None for key in required):
        return float("inf")
    total = fund.get(f"total_share_class_cost_{years}y")
    if total is None:
        total = _holding_costs(fees).get(f"total_share_class_cost_{years}y")
    if total is None:
        return float("inf")
    return _clamp(_finite(total), 0.0, 3.0)



def _underlying_key(fund: dict) -> str:
    explicit = str(
        fund.get("underlying_fund_id") or fund.get("master_code")
        or fund.get("primary_code") or ""
    ).strip().casefold()
    if explicit:
        return explicit if explicit.startswith(("id:", "name:", "code:")) else "id:" + explicit
    base = _base_name(str(fund.get("name") or ""))
    wrapper = _wrapper_type(str(fund.get("type") or ""))
    return f"name:{base.casefold()}|{wrapper}" if base else "code:" + str(fund.get("code") or "")


def _add_years(day: _dt.date, years: int) -> _dt.date:
    try:
        return day.replace(year=day.year + years)
    except ValueError:
        return day.replace(year=day.year + years, day=28)


def _years_before(day: _dt.date, years: int) -> _dt.date:
    return _add_years(day, -years)


_LUNAR_NEW_YEAR = {
    2024: _dt.date(2024, 2, 10), 2025: _dt.date(2025, 1, 29),
    2026: _dt.date(2026, 2, 17), 2027: _dt.date(2027, 2, 6),
    2028: _dt.date(2028, 1, 26), 2029: _dt.date(2029, 2, 13),
    2030: _dt.date(2030, 2, 3),
}


def _probable_china_market_holiday(day: _dt.date) -> bool:
    if day.weekday() >= 5:
        return True
    if (day.month, day.day) in {(1, 1)} or (day.month == 4 and 4 <= day.day <= 6):
        return True
    if day.month == 5 and day.day <= 5:
        return True
    if day.month == 10 and day.day <= 7:
        return True
    lunar_new_year = _LUNAR_NEW_YEAR.get(day.year)
    if lunar_new_year and lunar_new_year - _dt.timedelta(days=2) <= day <= lunar_new_year + _dt.timedelta(days=7):
        return True
    return False


def _expected_market_sessions(start_exclusive: _dt.date, finish_inclusive: _dt.date) -> int:
    if finish_inclusive <= start_exclusive:
        return 0
    count = 0
    day = start_exclusive + _dt.timedelta(days=1)
    while day <= finish_inclusive:
        count += int(not _probable_china_market_holiday(day))
        day += _dt.timedelta(days=1)
    return count


def _age_seconds(iso_value: str | None) -> float:
    stamp = _parse_iso(iso_value)
    if stamp is None or stamp.tzinfo is None:
        return float("inf")
    return max(0.0, (_dt.datetime.now().astimezone() - stamp.astimezone()).total_seconds())


def _rank_scale(values) -> list[float]:
    count = len(values)
    if count <= 1:
        return [0.0] * count
    order = sorted(range(count), key=lambda i: (_finite(values[i]), i))
    result = [0.0] * count
    start = 0
    while start < count:
        end = start + 1
        current = _finite(values[order[start]])
        while end < count and abs(_finite(values[order[end]]) - current) < 1e-12:
            end += 1
        average_rank = (start + end - 1) / 2.0
        scaled = 2.0 * average_rank / (count - 1) - 1.0
        for position in range(start, end):
            result[order[position]] = scaled
        start = end
    return result


def _atomic_bytes(path: Path, data: bytes) -> None:
    path = Path(path)
    descriptor, temp_name = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    temp = Path(temp_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp, path)
    finally:
        try:
            temp.unlink(missing_ok=True)
        except OSError:
            pass


def _write_json(path: Path, payload) -> None:
    raw = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True).encode("utf-8")
    _atomic_bytes(path, raw)


def _read_json(path: Path, default):
    try:
        with open(path, "r", encoding="utf-8") as handle:
            return json.load(handle)
    except (OSError, ValueError, TypeError):
        return default


def _default_install_settings() -> dict:
    return {
        "schema_version": SETTINGS_SCHEMA_VERSION,
        "install_mode": "",
        "lightgbm": False,
        "advanced_tree": False,
        "auto_update_model": True,
        "dependency_pins": dict(LOCAL_DEPENDENCY_PINS),
        "dependency_install_status": "not-configured",
        "configured_at": "",
    }


def _load_install_settings() -> dict:
    raw = _read_json(SETTINGS_PATH, {})
    settings = _default_install_settings()
    if isinstance(raw, dict):
        settings.update(raw)
    if int(_finite(settings.get("schema_version"), -1)) != SETTINGS_SCHEMA_VERSION:
        return _default_install_settings()
    return settings


def _save_install_settings(settings: dict) -> None:
    payload = _default_install_settings()
    payload.update(settings or {})
    payload["schema_version"] = SETTINGS_SCHEMA_VERSION
    payload["dependency_pins"] = dict(LOCAL_DEPENDENCY_PINS)
    payload["configured_at"] = payload.get("configured_at") or _now_iso()
    _write_json(SETTINGS_PATH, payload)


def _activate_local_dependencies() -> None:
    if not DEPS_DIR.is_dir():
        return
    text = str(DEPS_DIR)
    if text not in sys.path:
        sys.path.insert(0, text)
    importlib.invalidate_caches()


def _model_auto_update_enabled() -> bool:
    settings = _load_install_settings()
    return settings.get("auto_update_model") is not False


def _dependency_import_probe(target: Path, settings: dict) -> tuple[bool, str]:
    names = ["numpy"]
    if settings.get("lightgbm") is True:
        names.append("lightgbm")
    if settings.get("advanced_tree") is True:
        names.append("xgboost")
    probe = (
        "import importlib, json, sys; "
        f"sys.path.insert(0, {str(target)!r}); "
        f"names={names!r}; "
        "mods=[importlib.import_module(n) for n in names]; "
        "print(json.dumps({m.__name__:getattr(m,'__version__','unknown') for m in mods}))"
    )
    env = dict(os.environ)
    env["PYTHONNOUSERSITE"] = "1"
    completed = subprocess.run([sys.executable, "-I", "-c", probe], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=90, check=False, env=env)
    if completed.returncode != 0:
        return False, (completed.stderr or completed.stdout or "import probe failed").strip()[-1200:]
    return True, completed.stdout.strip()


def _ensure_pip_available() -> tuple[bool, str]:
    """Make unattended installs resilient when pip was removed from an otherwise valid Python."""
    probe = subprocess.run(
        [sys.executable, "-m", "pip", "--version"], stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, timeout=30, check=False,
    )
    if probe.returncode == 0:
        return True, (probe.stdout or "pip available").strip()
    ensure = subprocess.run(
        [sys.executable, "-m", "ensurepip", "--upgrade"], stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, timeout=180, check=False,
    )
    if ensure.returncode != 0:
        return False, (ensure.stderr or ensure.stdout or "ensurepip failed").strip()[-1000:]
    probe2 = subprocess.run(
        [sys.executable, "-m", "pip", "--version"], stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, timeout=30, check=False,
    )
    return probe2.returncode == 0, (probe2.stdout or probe2.stderr or "pip probe failed").strip()[-1000:]


def _verify_downloaded_wheels_against_pypi(wheel_dir: Path, packages: list[str]) -> tuple[bool, str, dict[str, str]]:
    """Verify every downloaded binary against the SHA-256 digest published by PyPI JSON metadata."""
    requested = {}
    for spec in packages:
        if "==" not in spec:
            return False, f"依赖未固定版本：{spec}", {}
        name, version = spec.split("==", 1)
        requested[name.lower().replace("_", "-")] = version
    wheels = sorted(wheel_dir.glob("*.whl"))
    if len(wheels) < len(requested):
        return False, f"wheel 数量异常：{len(wheels)} < {len(requested)}", {}
    verified = {}
    metadata_cache = {}
    for name, version in requested.items():
        url = f"https://pypi.org/pypi/{urllib.parse.quote(name)}/{urllib.parse.quote(version)}/json"
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=20) as response:
                raw = response.read(4 * 1024 * 1024 + 1)
            if len(raw) > 4 * 1024 * 1024:
                return False, f"PyPI 元数据过大：{name}", {}
            payload = json.loads(raw.decode("utf-8"))
        except Exception as exc:
            return False, f"无法取得 PyPI SHA-256 元数据：{name}=={version}: {exc}", {}
        by_filename = {}
        for row in payload.get("urls") or []:
            filename = str(row.get("filename") or "")
            digest = str((row.get("digests") or {}).get("sha256") or "").lower()
            if filename and re.fullmatch(r"[0-9a-f]{64}", digest):
                by_filename[filename] = digest
        metadata_cache[(name, version)] = by_filename
    for wheel in wheels:
        filename = wheel.name
        matches = []
        for (name, version), by_filename in metadata_cache.items():
            if filename in by_filename:
                matches.append((name, version, by_filename[filename]))
        if not matches:
            return False, f"下载了未在固定 PyPI 发布清单中的 wheel：{filename}", {}
        name, version, expected = matches[0]
        actual = hashlib.sha256(wheel.read_bytes()).hexdigest().lower()
        if not hmac.compare_digest(actual, expected):
            return False, f"SHA-256 校验失败：{filename}", {}
        verified[filename] = actual
    represented = {name for filename in verified for (name, version), listing in metadata_cache.items() if filename in listing}
    missing = sorted(set(requested) - represented)
    if missing:
        return False, "固定依赖未全部下载/校验：" + ",".join(missing), {}
    return True, f"已核验 {len(verified)} 个 wheel 的 PyPI SHA-256", verified


def _install_local_dependencies(settings: dict, status_callback=None) -> tuple[bool, str]:
    packages = []
    if settings.get("lightgbm") is True:
        packages.extend((LOCAL_DEPENDENCY_PINS["numpy"], LOCAL_DEPENDENCY_PINS["scipy"], LOCAL_DEPENDENCY_PINS["lightgbm"]))
    if settings.get("advanced_tree") is True:
        if sys.version_info < (3, 12):
            settings["advanced_tree"] = False
        else:
            packages.extend((LOCAL_DEPENDENCY_PINS["numpy"], LOCAL_DEPENDENCY_PINS["scipy"], LOCAL_DEPENDENCY_PINS["xgboost"]))
    packages = list(dict.fromkeys(packages))
    if not packages:
        settings["dependency_install_status"] = "minimal-standard-library-only"
        _save_install_settings(settings)
        return True, "极简安装：仅使用 Python 标准库"

    pip_ok, pip_detail = _ensure_pip_available()
    if not pip_ok:
        settings["dependency_install_status"] = "pip-unavailable-fallback-minimal"
        settings["dependency_install_error"] = pip_detail
        settings["lightgbm"] = False
        settings["advanced_tree"] = False
        _save_install_settings(settings)
        return False, "pip 不可用且 ensurepip 自动修复失败；已自动回退极简模式。"

    import shutil
    wheel_dir = BASE_DIR / "BestAlipayFunds_wheels.tmp"
    for path in (DEPS_TMP_DIR, DEPS_BACKUP_DIR, wheel_dir):
        try:
            if path.exists():
                shutil.rmtree(path)
        except OSError as exc:
            settings["dependency_install_status"] = f"prepare-failed:{type(exc).__name__}"
            _save_install_settings(settings)
            return False, f"无法准备本地 AI 临时目录：{exc}"
    try:
        DEPS_TMP_DIR.mkdir(parents=True, exist_ok=False)
        wheel_dir.mkdir(parents=True, exist_ok=False)
    except OSError as exc:
        settings["dependency_install_status"] = f"deps-dir-failed:{type(exc).__name__}"
        _save_install_settings(settings)
        return False, f"无法创建本地 AI 临时目录：{exc}"

    package_names = [value.split("==",1)[0] for value in packages]
    if status_callback:
        status_callback("后台下载固定版本 wheel：" + " / ".join(package_names) + "；随后自动做 SHA-256 校验…")
    download_command = [
        sys.executable, "-m", "pip", "download", "--disable-pip-version-check", "--quiet",
        "--only-binary=:all:", "--no-deps", "--no-cache-dir", "--dest", str(wheel_dir), *packages,
    ]
    old_moved = False
    try:
        downloaded = subprocess.run(download_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=900, check=False)
        if downloaded.returncode != 0:
            detail = (downloaded.stderr or downloaded.stdout or "pip download failed").strip()[-1200:]
            settings["dependency_install_status"] = "download-failed"
            settings["dependency_install_error"] = detail
            _save_install_settings(settings)
            shutil.rmtree(DEPS_TMP_DIR, ignore_errors=True); shutil.rmtree(wheel_dir, ignore_errors=True)
            return False, "本地 AI 二进制依赖下载失败；程序将自动使用原有依赖或纯 Python 模型。"
        ok_hash, hash_detail, verified_hashes = _verify_downloaded_wheels_against_pypi(wheel_dir, packages)
        if not ok_hash:
            settings["dependency_install_status"] = "sha256-verify-failed"
            settings["dependency_install_error"] = hash_detail
            _save_install_settings(settings)
            shutil.rmtree(DEPS_TMP_DIR, ignore_errors=True); shutil.rmtree(wheel_dir, ignore_errors=True)
            return False, "本地 AI wheel 的 SHA-256 校验失败或无法确认；已拒绝安装并自动降级。"
        if status_callback:
            status_callback(hash_detail + "；正在离线安装到脚本同级临时目录…")
        install_command = [
            sys.executable, "-m", "pip", "install", "--disable-pip-version-check", "--quiet",
            "--no-index", "--no-cache-dir", "--find-links", str(wheel_dir), "--target", str(DEPS_TMP_DIR), *packages,
        ]
        installed = subprocess.run(install_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=900, check=False)
        if installed.returncode != 0:
            detail = (installed.stderr or installed.stdout or "pip install failed").strip()[-1200:]
            settings["dependency_install_status"] = "install-failed"
            settings["dependency_install_error"] = detail
            _save_install_settings(settings)
            shutil.rmtree(DEPS_TMP_DIR, ignore_errors=True); shutil.rmtree(wheel_dir, ignore_errors=True)
            return False, "校验后的本地 AI 依赖安装失败；程序将自动使用原有依赖或纯 Python 模型。"
        if status_callback:
            status_callback("安装完成；正在验证 NumPy / SciPy / LightGBM / XGBoost 的本地导入…")
        ok, detail = _dependency_import_probe(DEPS_TMP_DIR, settings)
        if not ok:
            settings["dependency_install_status"] = "verify-failed"
            settings["dependency_install_error"] = detail
            _save_install_settings(settings)
            shutil.rmtree(DEPS_TMP_DIR, ignore_errors=True); shutil.rmtree(wheel_dir, ignore_errors=True)
            return False, "本地 AI 依赖验证失败，未覆盖现有目录；程序会自动降级。"
        if status_callback:
            status_callback("验证通过；正在原子切换本地 AI 目录并保留一次回滚点…")
        if DEPS_DIR.exists():
            os.replace(DEPS_DIR, DEPS_BACKUP_DIR); old_moved = True
        os.replace(DEPS_TMP_DIR, DEPS_DIR)
        _activate_local_dependencies()
        settings["dependency_install_status"] = "installed-atomic-sha256:" + detail[:500]
        settings["dependency_wheel_sha256"] = verified_hashes
        settings.pop("dependency_install_error", None)
        _save_install_settings(settings)
        if DEPS_BACKUP_DIR.exists():
            shutil.rmtree(DEPS_BACKUP_DIR, ignore_errors=True)
        shutil.rmtree(wheel_dir, ignore_errors=True)
        return True, "本地 AI 依赖已下载、SHA-256 核验、验证并原子启用。"
    except Exception as exc:
        try:
            shutil.rmtree(DEPS_TMP_DIR, ignore_errors=True); shutil.rmtree(wheel_dir, ignore_errors=True)
            if old_moved and DEPS_BACKUP_DIR.exists() and not DEPS_DIR.exists():
                os.replace(DEPS_BACKUP_DIR, DEPS_DIR)
        except Exception:
            pass
        settings["dependency_install_status"] = f"exception:{type(exc).__name__}"
        settings["dependency_install_error"] = str(exc)[:1200]
        _save_install_settings(settings)
        return False, "本地 AI 安装出现异常；已尽量回滚，程序将自动降级继续运行。"


def _choose_install_mode_gui(force: bool = False) -> dict:
    settings = _load_install_settings()
    if settings.get("install_mode") and not force:
        _activate_local_dependencies()
        return settings
    try:
        import tkinter as tk
        from tkinter import messagebox
    except ImportError:
        settings.update({"install_mode":"minimal", "lightgbm":False, "advanced_tree":False, "auto_update_model":True})
        _save_install_settings(settings)
        return settings

    root = tk.Tk()
    root.title(f"{APP_NAME} · 首次安装")
    root.geometry("660x510")
    root.resizable(False, False)
    root.configure(bg="#0b1220")
    mode = tk.StringVar(value="full")
    lgb = tk.BooleanVar(value=True)
    advanced = tk.BooleanVar(value=sys.version_info >= (3, 12))
    auto_update = tk.BooleanVar(value=True)
    result = {"done": False}

    tk.Label(root, text="选择一次安装方式", font=("Microsoft YaHei UI", 20, "bold"), bg="#0b1220", fg="#f8fafc").pack(anchor="w", padx=26, pady=(24, 6))
    tk.Label(root, text="所有 AI 依赖只安装到脚本同级 BestAlipayFunds_deps，不修改全局 Python。", font=("Microsoft YaHei UI", 10), bg="#0b1220", fg="#94a3b8").pack(anchor="w", padx=26, pady=(0, 16))

    frame = tk.Frame(root, bg="#111c31", padx=18, pady=14)
    frame.pack(fill="x", padx=26)
    descriptions = {
        "minimal": "极简安装：仅标准库；不下载第三方 AI 包；启动最快。",
        "full": "完整安装：本地安装固定版本 NumPy/SciPy/LightGBM；Python 3.12+ 同时启用 XGBoost 排名模型。",
        "custom": "自定义安装：自行选择排名树模型，并决定是否自动更新模型。",
    }
    custom = tk.Frame(root, bg="#0b1220")
    def update_custom():
        custom_mode = mode.get() == "custom"
        lgb_box.configure(state="normal" if custom_mode else "disabled")
        xgb_box.configure(state="normal" if custom_mode and sys.version_info >= (3,12) else "disabled")
        auto_box.configure(state="normal" if custom_mode else "disabled")
    for value, title in (("minimal","极简安装"),("full","完整安装"),("custom","自定义安装")):
        row = tk.Frame(frame, bg="#111c31")
        row.pack(fill="x", pady=4)
        tk.Radiobutton(row, text=title, variable=mode, value=value, command=update_custom,
                       font=("Microsoft YaHei UI", 11, "bold"), bg="#111c31", fg="#e2e8f0",
                       selectcolor="#18263f", activebackground="#111c31", activeforeground="#ffffff").pack(anchor="w")
        tk.Label(row, text=descriptions[value], font=("Microsoft YaHei UI", 9), bg="#111c31", fg="#94a3b8", wraplength=570, justify="left").pack(anchor="w", padx=(24,0))

    custom.pack(fill="x", padx=32, pady=(14, 4))
    lgb_box = tk.Checkbutton(custom, text="LightGBM LambdaRank（推荐）", variable=lgb, font=("Microsoft YaHei UI", 10), bg="#0b1220", fg="#e2e8f0", selectcolor="#18263f", activebackground="#0b1220", activeforeground="#ffffff")
    lgb_box.pack(anchor="w")
    xgb_box = tk.Checkbutton(custom, text="XGBoost rank:ndcg（第二树模型，Python 3.12+）", variable=advanced, font=("Microsoft YaHei UI", 10), bg="#0b1220", fg="#e2e8f0", selectcolor="#18263f", activebackground="#0b1220", activeforeground="#ffffff")
    xgb_box.pack(anchor="w")
    auto_box = tk.Checkbutton(custom, text="允许程序按 OOS 证据和数据变化自动更新模型", variable=auto_update, font=("Microsoft YaHei UI", 10), bg="#0b1220", fg="#e2e8f0", selectcolor="#18263f", activebackground="#0b1220", activeforeground="#ffffff")
    auto_box.pack(anchor="w")
    status = tk.StringVar(value="")
    tk.Label(root, textvariable=status, font=("Microsoft YaHei UI", 9), bg="#0b1220", fg="#fbbf24", wraplength=600, justify="left").pack(anchor="w", padx=26, pady=(6, 0))
    update_custom()

    install_events = queue.Queue()
    install_running = {"value": False}

    def status_callback(text):
        install_events.put(("status", str(text)))

    def poll_install_events():
        try:
            while True:
                event = install_events.get_nowait()
                if event[0] == "status":
                    status.set(event[1])
                elif event[0] == "finished":
                    ok, message = event[1], event[2]
                    if not ok:
                        messagebox.showwarning(APP_NAME, message + "\n\n之后无需手工处理；程序会自动降级。", parent=root)
                    result["done"] = True
                    root.destroy()
                    return
        except queue.Empty:
            pass
        if root.winfo_exists():
            root.after(120, poll_install_events)

    def apply_choice():
        if install_running["value"]:
            return
        selected = mode.get()
        settings["install_mode"] = selected
        if selected == "minimal":
            settings["lightgbm"] = False; settings["advanced_tree"] = False; settings["auto_update_model"] = True
        elif selected == "full":
            settings["lightgbm"] = True; settings["advanced_tree"] = sys.version_info >= (3,12); settings["auto_update_model"] = True
        else:
            settings["lightgbm"] = bool(lgb.get()); settings["advanced_tree"] = bool(advanced.get()) and sys.version_info >= (3,12); settings["auto_update_model"] = bool(auto_update.get())
        settings["configured_at"] = _now_iso()
        _save_install_settings(settings)
        install_running["value"] = True
        save_button.configure(state="disabled", text="正在后台安装…")
        status.set("已启动后台安装；窗口仍可响应，请勿关闭直到自动进入主界面。")

        def worker():
            ok, message = _install_local_dependencies(settings, status_callback=status_callback)
            install_events.put(("finished", ok, message))
        threading.Thread(target=worker, name="dependency-installer", daemon=True).start()

    def close_window():
        if install_running["value"]:
            status.set("依赖正在后台安装并验证；完成后会自动进入主界面。")
            return
        if not result["done"]:
            settings.update({"install_mode":"minimal", "lightgbm":False, "advanced_tree":False, "auto_update_model":True, "configured_at":_now_iso()})
            _save_install_settings(settings)
        root.destroy()
    root.protocol("WM_DELETE_WINDOW", close_window)
    save_button = tk.Button(root, text="保存选择并启动", command=apply_choice, font=("Microsoft YaHei UI", 11, "bold"), bg="#2563eb", fg="#ffffff", activebackground="#1d4ed8", activeforeground="#ffffff", relief="flat", padx=18, pady=9)
    save_button.pack(anchor="e", padx=26, pady=(12, 20))
    root.after(120, poll_install_events)
    root.mainloop()
    _activate_local_dependencies()
    return _load_install_settings()


def _decode_response(raw: bytes, charset: str | None) -> str:
    candidates = [charset, "utf-8-sig", "utf-8", "gb18030"]
    for candidate in candidates:
        if not candidate:
            continue
        try:
            return raw.decode(candidate)
        except (LookupError, UnicodeDecodeError):
            pass
    return raw.decode("utf-8", errors="replace")


def _read_response_limited(response, limit: int = MAX_HTTP_RESPONSE_BYTES) -> bytes:
    try:
        content_length = int(response.headers.get("Content-Length") or 0)
    except (TypeError, ValueError):
        content_length = 0
    if content_length > limit:
        raise DataError(f"网络响应声明大小 {content_length} 字节，超过安全上限 {limit} 字节")
    raw = response.read(limit + 1)
    if len(raw) > limit:
        raise DataError(f"网络响应超过安全上限 {limit} 字节")
    return raw


def _safe_gzip_decompress(raw: bytes, limit: int = MAX_HTTP_DECOMPRESSED_BYTES) -> bytes:
    try:
        with gzip.GzipFile(fileobj=io.BytesIO(raw), mode="rb") as handle:
            decoded = handle.read(limit + 1)
    except (OSError, EOFError) as exc:
        raise DataError(f"gzip 响应损坏：{exc}") from exc
    if len(decoded) > limit:
        raise DataError(f"gzip 解压结果超过安全上限 {limit} 字节")
    return decoded


class _DomainTokenBucket:
    """Small per-domain token bucket to avoid turning concurrency into self-inflicted throttling."""
    def __init__(self, rate: float, capacity: float):
        self.rate = max(0.25, float(rate))
        self.capacity = max(1.0, float(capacity))
        self.tokens = self.capacity
        self.updated = time.monotonic()
        self.penalty_until = 0.0
        self.lock = threading.Lock()

    def acquire(self) -> None:
        while True:
            with self.lock:
                now = time.monotonic()
                effective_rate = self.rate * (0.35 if now < self.penalty_until else 1.0)
                self.tokens = min(self.capacity, self.tokens + (now - self.updated) * effective_rate)
                self.updated = now
                if self.tokens >= 1.0:
                    self.tokens -= 1.0
                    return
                wait = (1.0 - self.tokens) / max(0.25, effective_rate)
            time.sleep(min(0.35, max(0.01, wait)))

    def penalize(self, seconds: float = 20.0) -> None:
        with self.lock:
            self.tokens = min(self.tokens, 0.25)
            self.penalty_until = max(self.penalty_until, time.monotonic() + max(2.0, seconds))


_DOMAIN_BUCKETS: dict[str, _DomainTokenBucket] = {}
_DOMAIN_BUCKETS_LOCK = threading.Lock()


def _domain_bucket(url: str) -> _DomainTokenBucket:
    host = (urllib.parse.urlsplit(url).hostname or "unknown").lower()
    with _DOMAIN_BUCKETS_LOCK:
        bucket = _DOMAIN_BUCKETS.get(host)
        if bucket is None:
            # Sina HTML fallback is deliberately gentler; Eastmoney public APIs can tolerate somewhat more parallelism.
            rate, capacity = ((3.0, 3.0) if "sina" in host else (7.0, 6.0))
            bucket = _DOMAIN_BUCKETS[host] = _DomainTokenBucket(rate, capacity)
        return bucket


class _PinnedRedirectHandler(urllib.request.HTTPRedirectHandler):
    def __init__(self, allowed_hosts: set[str] | frozenset[str]):
        super().__init__()
        self.allowed_hosts = {str(host).strip().lower() for host in allowed_hosts if str(host).strip()}

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        parsed = urllib.parse.urlsplit(newurl)
        host = (parsed.hostname or "").lower()
        if parsed.scheme.lower() != "https" or host not in self.allowed_hosts:
            raise urllib.error.HTTPError(
                req.full_url, code,
                f"已阻止携带受信请求头跳转到白名单外地址：{newurl}", headers, fp,
            )
        return super().redirect_request(req, fp, code, msg, headers, newurl)


# ===== HTTP / 限流 =====

def _http_text(
    url: str,
    *,
    data: dict | None = None,
    referer: str = "https://fund.eastmoney.com/",
    timeout: float = 9.0,
    attempts: int = 2,
    headers_extra: dict | None = None,
    allowed_redirect_hosts: set[str] | frozenset[str] | None = None,
    max_response_bytes: int = MAX_HTTP_RESPONSE_BYTES,
) -> str:
    encoded = None
    if data is not None:
        encoded = urllib.parse.urlencode(data).encode("utf-8")
    headers = {
        "User-Agent": USER_AGENT,
        "Accept": "application/json,text/javascript,*/*;q=0.8",
        "Accept-Encoding": "gzip",
        "Referer": referer,
        "Cache-Control": "no-cache",
        "X-Requested-With": "XMLHttpRequest",
    }
    if encoded is not None:
        headers["Content-Type"] = "application/x-www-form-urlencoded; charset=UTF-8"
    if headers_extra:
        headers.update({str(k): str(v) for k, v in headers_extra.items() if v is not None})
    last_error = None
    bucket = _domain_bucket(url)
    for attempt in range(attempts):
        try:
            bucket.acquire()
            request = urllib.request.Request(url, data=encoded, headers=headers)
            opener = (
                urllib.request.build_opener(_PinnedRedirectHandler(allowed_redirect_hosts))
                if allowed_redirect_hosts is not None else urllib.request.build_opener()
            )
            with opener.open(request, timeout=timeout) as response:
                raw = _read_response_limited(response, max_response_bytes)
                if response.headers.get("Content-Encoding", "").lower() == "gzip":
                    raw = _safe_gzip_decompress(raw)
                return _decode_response(raw, response.headers.get_content_charset())
        except (OSError, urllib.error.URLError, urllib.error.HTTPError, TimeoutError) as exc:
            last_error = exc
            if isinstance(exc, urllib.error.HTTPError) and exc.code == 429:
                bucket.penalize(30.0)
            elif isinstance(exc, (TimeoutError, urllib.error.URLError)):
                bucket.penalize(6.0)
            if attempt + 1 < attempts:
                time.sleep(0.35 * (attempt + 1) + random.random() * 0.2)
    raise DataError(f"网络请求失败：{last_error}")


def _http_json(url: str, **kwargs):
    text = _http_text(url, **kwargs)
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        match = re.search(r"\{[\s\S]*\}", text)
        if match:
            try:
                return json.loads(match.group(0))
            except json.JSONDecodeError:
                pass
        raise DataError(f"数据格式无法识别：{exc}") from exc


def _wrapper_type(value: str) -> str:
    text = (value or "").upper()
    if "QDII" in text or "海外" in text:
        return "QDII"
    if "FOF" in text or "基金中基金" in text:
        return "FOF"
    return "普通"


def _coarse_type(value: str) -> str:
    text = value or "其他"
    if "债" in text:
        return "债券"
    if "指数" in text or "ETF" in text.upper():
        return "指数"
    if "股票" in text:
        return "股票"
    if "混合" in text:
        return "混合"
    if _wrapper_type(text) == "FOF":
        return "混合"
    if _wrapper_type(text) == "QDII":
        return "指数" if "指数" in text else "股票"
    return "其他"


def _base_name(name: str) -> str:
    value = re.sub(r"[（(](人民币|前端|后端|场外)[）)]", "", name or "")
    value = re.sub(r"(?:ETF)?联接基金?([AC])?$", "联接", value, flags=re.I)
    value = re.sub(r"(?:人民币)?[A-EH-IY]类?$", "", value, flags=re.I)
    value = re.sub(r"[\s·\-_（）()]", "", value)
    return value


def _share_preference(name: str) -> int:
    compact = (name or "").strip().upper()
    if re.search(r"A类?$", compact):
        return 4
    if re.search(r"C类?$", compact):
        return 3
    if re.search(r"[BDEHIY]类?$", compact):
        return 2
    return 3


def _theme(name: str) -> str:
    groups = {
        "医药医疗": ("医药", "医疗", "生物", "创新药"),
        "科技半导体": ("科技", "半导体", "芯片", "软件", "计算机", "人工智能", "机器人"),
        "新能源": ("新能源", "光伏", "电池", "汽车"),
        "消费": ("消费", "白酒", "食品", "家电"),
        "周期资源": ("煤炭", "有色", "钢铁", "资源", "化工", "黄金"),
        "军工": ("军工", "国防", "航天"),
        "金融地产": ("金融", "银行", "证券", "地产"),
        "海外": ("全球", "海外", "美国", "纳斯达克", "标普", "港股", "恒生"),
    }
    for label, words in groups.items():
        if any(word in (name or "") for word in words):
            return label
    return "宽基/全市场"


def _candidate_allowed(name: str, fund_type: str) -> bool:
    text = f"{name} {fund_type}".upper()
    blocked = (
        "货币", "理财", "同业存单", "REIT", "封闭", "定期开放", "定开",
        "后端", "分级", "杠杆", "商品", "原油", "白银",
    )
    if any(word.upper() in text for word in blocked):
        return False
    if not re.fullmatch(r"[\s\S]{2,80}", name or ""):
        return False
    return _coarse_type(fund_type) != "其他"


def _public_availability_signals(item: dict) -> set[str]:
    signals = {str(value) for value in (item.get("availability_public_signals") or []) if str(value)}
    status_text = re.sub(r"\s+", "", str(item.get("public_purchase_status") or ""))
    purchase_blocked = any(word in status_text for word in ("暂停申购", "终止申购", "封闭期", "暂停交易", "清盘", "终止运作")) and "暂停大额申购" not in status_text
    if any(word in status_text for word in ("开放申购", "可申购", "开放")) and not purchase_blocked:
        signals.add("public-purchase-open")
    if any(word in status_text for word in ("暂停大额申购", "限制大额申购", "限购", "大额申购上限")):
        signals.add("public-purchase-limited")
    catalog_sources = {str(value) for value in (item.get("catalog_sources") or []) if str(value)}
    if len(catalog_sources) >= 2 or int(_finite(item.get("public_catalog_confirmations"), 0)) >= 2:
        signals.add("multi-public-catalog")
    latest_sources = {str(value) for value in (item.get("latest_sources") or []) if str(value)}
    if len(latest_sources) >= 2 or int(_finite(item.get("latest_public_confirmations"), 0)) >= 2:
        signals.add("multi-source-latest-nav")
    latest_text = str(item.get("latest_date") or item.get("display_nav_date") or "")[:10]
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", latest_text):
        try:
            if _expected_market_sessions(_dt.date.fromisoformat(latest_text), _china_today()) <= 5:
                signals.add("recent-nav-active")
        except ValueError:
            pass
    return signals


def _alipay_availability_confidence(item: dict) -> int:
    """Compatibility field: 100 alone means real signed Alipay confirmation; lower values are platform/public inference."""
    status = str(item.get("availability_status") or ("confirmed_purchasable" if item.get("availability_declared") is True else "unknown"))
    if status in PURCHASE_UNAVAILABLE_STATUSES:
        return 0
    if status == "confirmed_purchasable":
        return 100
    signals = _public_availability_signals(item)
    confirmations = max(int(_finite(item.get("availability_public_confirmations"), 0)), len(signals))
    if status == "limited_purchasable" or "public-purchase-limited" in signals:
        return 55
    if "public-purchase-open" in signals and confirmations >= 3:
        return 80
    if "public-purchase-open" in signals or confirmations >= 2 or status == "public_open":
        return 60
    if status == "redemption_suspended":
        return 35
    return 30


def _purchase_evidence_label(item: dict) -> str:
    status = str(item.get("availability_status") or "unknown")
    confidence = _alipay_availability_confidence(item)
    if status == "confirmed_purchasable":
        return "支付宝已确认 100/100"
    if status == "limited_purchasable":
        return f"平台可购推测 {confidence}/100 · 限购"
    if status == "redemption_suspended":
        return f"平台可购推测 {confidence}/100 · 赎回受限"
    if status in PURCHASE_UNAVAILABLE_STATUSES:
        return "公开证据：不可申购"
    return f"平台可购推测 {confidence}/100"



def _valuation_entry_signal(item: dict) -> float:
    """Small current-entry signal; zero when no public index valuation percentile is available."""
    if _asset_bucket(item.get("name", ""), item.get("type", "")) not in {"指数", "QDII/海外"}:
        return 0.0
    features = item.get("product_features") if isinstance(item.get("product_features"), dict) else {}
    values = []
    for key in ("pe_percentile", "pb_percentile"):
        value = _finite(features.get(key), float("nan"))
        if math.isfinite(value):
            values.append(1.0 - 2.0 * _clamp(value, 0.0, 1.0))
    for key in ("dividend_yield_percentile", "equity_risk_premium_percentile"):
        value = _finite(features.get(key), float("nan"))
        if math.isfinite(value):
            values.append(2.0 * _clamp(value, 0.0, 1.0) - 1.0)
    return _clamp(statistics.fmean(values), -1.0, 1.0) if values else 0.0


def _product_integrity_score(item: dict) -> float:
    """Metadata/product completeness score used only as a modest ranking adjustment."""
    score = 55.0
    if item.get("fees_verified") is True:
        score += 18.0
    if str(item.get("fund_company") or "").strip():
        score += 8.0
    if str(item.get("benchmark") or item.get("index_code") or "").strip():
        score += 6.0
    if item.get("product_features"):
        score += 6.0
    if str(item.get("fund_manager") or "").strip():
        score += 4.0
    if str(item.get("metadata_checked_at") or "").strip():
        score += 3.0
    return _clamp(score, 0.0, 100.0)


def _model_evidence_factor(model: dict, item: dict) -> tuple[float, dict]:
    """Shrink confidence when historical universe/OOS/freshness evidence is weak."""
    universe_cov = _clamp(_finite(model.get("historical_universe_known_coverage"), 0.0), 0.0, 1.0)
    availability_cov = _clamp(_finite(model.get("historical_availability_coverage"), 0.0), 0.0, 1.0)
    metrics = model.get("full_pipeline_oos") or model.get("untouched_test_oos") or model.get("validation_metrics") or {}
    windows = max(0, int(_finite(metrics.get("windows"), 0)))
    windows_factor = _clamp(windows / 8.0, 0.40, 1.0)
    dispersion = abs(_finite(metrics.get("rank_ic_std"), 0.0))
    if dispersion <= 1e-12:
        median = _finite(metrics.get("rank_ic_median"), 0.0)
        p25 = _finite(metrics.get("rank_ic_p25"), median)
        dispersion = abs(median - p25)
    dispersion_factor = _clamp(1.0 - dispersion / 0.45, 0.45, 1.0)
    latest_text = str(item.get("latest_date") or ((item.get("dates") or [""])[-1] if item.get("dates") else ""))[:10]
    freshness_factor = 0.72
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", latest_text):
        try:
            sessions = _expected_market_sessions(_dt.date.fromisoformat(latest_text), _china_today())
            freshness_factor = 1.0 if sessions <= 1 else 0.94 if sessions <= 3 else 0.86 if sessions <= 5 else 0.72
        except ValueError:
            pass
    coverage_factor = 0.65 * universe_cov + 0.35 * availability_cov
    evidence = 0.35 * coverage_factor + 0.25 * windows_factor + 0.20 * dispersion_factor + 0.20 * freshness_factor
    # Missing historical dead-fund coverage must materially reduce evidence rather than merely print a warning.
    factor = _clamp(0.52 + 0.48 * evidence, 0.50, 1.0)
    # First-run/current-universe-only backtests can look deceptively strong. Until the local historical
    # universe archive has meaningful coverage, cap visible model evidence at 50-60/100.
    if universe_cov < 0.25:
        factor = min(factor, 0.50)
    elif universe_cov < 0.60:
        factor = min(factor, 0.60)
    elif universe_cov < 0.85:
        factor = min(factor, 0.78)
    details = {
        "historical_universe_known_coverage": round(universe_cov, 4),
        "historical_availability_coverage": round(availability_cov, 4),
        "oos_windows": windows,
        "rank_ic_dispersion": round(dispersion, 4),
        "freshness_factor": round(freshness_factor, 4),
        "factor": round(factor, 4),
    }
    return factor, details


# ===== 支付宝可购证据 =====

class AlipayAvailabilitySource:

    SCHEMA = "best-alipay-funds-availability-v5"

                                                                                                 
                                                                                                
                                                                                                   
                                                   
    DEFAULT_URL = ""
    PUBLIC_RSA_KEYS: dict[str, tuple[int, int]] = {}
    DEFAULT_PUBLIC_HOSTS: frozenset[str] = frozenset()

    def __init__(self):
        self.last_snapshot_state: dict = {}

    @staticmethod
    def _payload_time(payload: dict) -> str:
        return str(payload.get("generated_at") or payload.get("declared_at") or payload.get("verified_at") or "")

    @staticmethod
    def _canonical_signature_bytes(payload: dict) -> bytes:
        unsigned = dict(payload)
        unsigned.pop("signature", None)
        return json.dumps(unsigned, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")

    @staticmethod
    def _verify_rsa_sha256(signature_b64: str, message: bytes, n: int, e: int = 65537) -> bool:
        try:
            signature = base64.b64decode(signature_b64, validate=True)
            size = (int(n).bit_length() + 7) // 8
            if size < 128 or len(signature) != size:
                return False
            em = pow(int.from_bytes(signature, "big"), int(e), int(n)).to_bytes(size, "big")
            digest_info = bytes.fromhex("3031300d060960864801650304020105000420") + hashlib.sha256(message).digest()
            padding_len = size - len(digest_info) - 3
            expected = b"\x00\x01" + b"\xff" * padding_len + b"\x00" + digest_info
            return padding_len >= 8 and hmac.compare_digest(em, expected)
        except (ValueError, TypeError, OverflowError):
            return False

    @classmethod
    def _trusted_url(cls) -> tuple[str, bool, frozenset[str]]:
        custom = os.environ.get("BEST_ALIPAY_AVAILABILITY_URL", "").strip()
        url = custom or cls.DEFAULT_URL
        if not url:
            return "", False, frozenset()
        parsed = urllib.parse.urlsplit(url)
        if parsed.scheme.lower() != "https" or not parsed.hostname:
            raise DataError("可信支付宝可购状态源必须是有效 HTTPS 地址")
        host = parsed.hostname.lower()
        is_public = not bool(custom)
        if is_public:
            allowed = set(cls.DEFAULT_PUBLIC_HOSTS)
            default_host = urllib.parse.urlsplit(cls.DEFAULT_URL).hostname if cls.DEFAULT_URL else None
            if default_host:
                allowed.add(default_host.lower())
            if not allowed or host not in allowed:
                raise DataError(f"内置公共可购源域名 {host} 不在发行版固定白名单")
        else:
            configured = {
                h.strip().lower() for h in os.environ.get("BEST_ALIPAY_AVAILABILITY_HOSTS", "").split(",") if h.strip()
            }
                                                                                                 
                                                                                           
            allowed = configured or {host}
            if host not in allowed:
                raise DataError(f"私有可购状态源域名 {host} 不在固定白名单中")
        return url, is_public, frozenset(allowed)

    def _write_snapshot(self, payload: dict) -> None:
        try:
            _write_json(ALIPAY_FILE_PATH, payload)
        except OSError as exc:
            raise DataError(f"无法在脚本同目录写入可购状态快照：{exc}") from exc

    @staticmethod
    def _dt_aware(value: str, field: str) -> _dt.datetime:
        stamp = _parse_iso(value)
        if stamp is None:
            raise DataError(f"可购状态源缺少合法 {field}")
        if stamp.tzinfo is None:
            stamp = stamp.replace(tzinfo=_dt.timezone.utc)
        return stamp

    def _verify_signature(self, payload: dict, *, public_source: bool) -> None:
        source_id = str(payload.get("source_id") or "").strip()
        alg = str(payload.get("signature_alg") or "").strip().lower()
        signature = str(payload.get("signature") or "").strip()
        message = self._canonical_signature_bytes(payload)
        if not signature:
            raise DataError("可购状态缺少数字签名，已拒绝")
        if alg == "rsa-sha256":
            key_tuple = self.PUBLIC_RSA_KEYS.get(source_id)
            if key_tuple is None and not public_source:
                n_text = os.environ.get("BEST_ALIPAY_AVAILABILITY_RSA_N", "").strip()
                e_text = os.environ.get("BEST_ALIPAY_AVAILABILITY_RSA_E", "65537").strip()
                if n_text:
                    try:
                        key_tuple = (int(n_text, 0), int(e_text, 0))
                    except ValueError as exc:
                        raise DataError("私有可购状态 RSA 公钥参数无效") from exc
            if key_tuple is None:
                scope = "发行版内置" if public_source else "受信"
                raise DataError(f"可购状态源 {source_id} 没有{scope} RSA 公钥")
            if not self._verify_rsa_sha256(signature, message, *key_tuple):
                raise DataError("可购状态 RSA-SHA256 签名校验失败")
            return
        if alg == "hmac-sha256" and not public_source:
            key = os.environ.get("BEST_ALIPAY_AVAILABILITY_HMAC_KEY", "")
            if not key:
                raise DataError("私有 HMAC 可购源缺少 BEST_ALIPAY_AVAILABILITY_HMAC_KEY")
            expected = hmac.new(key.encode("utf-8"), message, hashlib.sha256).hexdigest()
            if not hmac.compare_digest(signature.lower(), expected):
                raise DataError("可购状态 HMAC-SHA256 签名校验失败")
            return
        if public_source:
            raise DataError("发行版公共可购源必须使用 RSA-SHA256 非对称签名")
        raise DataError(f"不支持或不允许的可购状态签名算法：{alg or 'missing'}")

    def _validate_payload(self, payload: dict, *, require_fresh: bool = True, public_source: bool = False) -> dict:
        if not isinstance(payload, dict):
            raise DataError("可购状态数据必须是 JSON object")
        if payload.get("schema") != self.SCHEMA or int(_finite(payload.get("schema_version"), -1)) != AVAILABILITY_SCHEMA_VERSION:
            raise DataError(f"可购状态 schema 必须是 {self.SCHEMA} / version {AVAILABILITY_SCHEMA_VERSION}")
        source_id = str(payload.get("source_id") or "").strip()
        if not re.fullmatch(r"[A-Za-z0-9._:-]{3,100}", source_id):
            raise DataError("可购状态源缺少合法 source_id")
        try:
            sequence = int(payload.get("sequence"))
        except (TypeError, ValueError) as exc:
            raise DataError("可购状态源缺少合法 sequence") from exc
        if sequence < 1:
            raise DataError("可购状态 sequence 必须 >= 1")
        generated_at = str(payload.get("generated_at") or "")
        expires_at = str(payload.get("expires_at") or "")
        generated = self._dt_aware(generated_at, "generated_at")
        expires = self._dt_aware(expires_at, "expires_at")
        now = _dt.datetime.now().astimezone()
        generated_local = generated.astimezone(now.tzinfo)
        expires_local = expires.astimezone(now.tzinfo)
        if generated_local > now + _dt.timedelta(seconds=MAX_AVAILABILITY_FUTURE_SKEW_SECONDS):
            raise DataError("可购状态 generated_at 比本机时间超前超过 5 分钟")
        if expires <= generated:
            raise DataError("可购状态 expires_at 必须晚于 generated_at")
        if expires - generated > _dt.timedelta(hours=24):
            raise DataError("可购状态有效期超过 24 小时，拒绝过宽可信窗口")

                                                                                 
        self._verify_signature(payload, public_source=public_source)
        if payload.get("declared") is not True and payload.get("verified") is not True:
            raise DataError("可购状态源没有明确声明 declared/verified=true")
        if require_fresh:
            if now > expires_local:
                raise DataError(f"可购状态已于 {expires_at} 过期")
            max_age = _availability_max_age_seconds(now)
            if _age_seconds(generated_at) > max_age:
                raise DataError(f"可购状态 generated_at 已超过当前时段可信窗口 {max_age // 60} 分钟")

        rows = payload.get("funds")
        if not isinstance(rows, list):
            raise DataError("可购状态 funds 必须是数组")
        seen = set(); purchasable_count = 0
        for index, row in enumerate(rows):
            if not isinstance(row, dict):
                raise DataError(f"可购状态 funds[{index}] 不是对象")
            code = str(row.get("code") or "")
            if not re.fullmatch(r"\d{6}", code):
                raise DataError(f"可购状态包含非法基金代码：{code!r}")
            if code in seen:
                raise DataError(f"可购状态基金代码重复：{code}")
            seen.add(code)
            if row.get("purchasable") is not True:
                continue
            if row.get("declared") is not True and row.get("verified") is not True:
                raise DataError(f"{code} 标为 purchasable 但未声明 declared/verified=true")
            item_time = str(row.get("declared_at") or row.get("verified_at") or generated_at)
            item_stamp = self._dt_aware(item_time, f"{code}.declared_at")
            if item_stamp.astimezone(now.tzinfo) > now + _dt.timedelta(seconds=MAX_AVAILABILITY_FUTURE_SKEW_SECONDS):
                raise DataError(f"{code} 声明时间超前超过 5 分钟")
            if require_fresh and item_stamp > expires:
                raise DataError(f"{code} 声明时间晚于清单 expires_at")
            if require_fresh and _age_seconds(item_time) > _availability_max_age_seconds(now):
                raise DataError(f"{code} 可购声明本身已超过当前时段可信窗口")
            purchasable_count += 1
        if purchasable_count < MIN_AVAILABILITY_FUNDS:
            raise DataError(f"可信可购状态源仅声明 {purchasable_count} 个当前可购具体份额，低于最低 {MIN_AVAILABILITY_FUNDS} 个")
        return payload

    @staticmethod
    def _rollback_guard(new_payload: dict, old_payload: dict) -> None:
        if not isinstance(old_payload, dict):
            return
        if str(new_payload.get("source_id") or "") != str(old_payload.get("source_id") or ""):
            return
        try:
            new_seq, old_seq = int(new_payload.get("sequence")), int(old_payload.get("sequence"))
        except (TypeError, ValueError):
            return
        if new_seq < old_seq:
            raise DataError(f"检测到可购清单 sequence 回滚：{new_seq} < {old_seq}")
        if new_seq == old_seq and AlipayAvailabilitySource._canonical_signature_bytes(new_payload) != AlipayAvailabilitySource._canonical_signature_bytes(old_payload):
            raise DataError("相同 sequence 对应不同可购清单内容，已拒绝")

    def _stale_summary(self, local: dict, *, public_source: bool) -> str:
        try:
            stale = self._validate_payload(local, require_fresh=False, public_source=public_source)
            rows = sum(1 for r in stale.get("funds") or [] if isinstance(r, dict) and r.get("purchasable") is True)
            return (
                f"已保留最后一份验签成功的历史缓存：source_id={stale.get('source_id')}，"
                f"sequence={stale.get('sequence')}，generated_at={stale.get('generated_at')}，"
                f"expires_at={stale.get('expires_at')}，当时可购 {rows} 个份额。"
                "该缓存仅供历史参考，不代表当前支付宝可购。"
            )
        except Exception as exc:
            return f"本地历史快照也无法通过签名/结构校验：{exc}"

    def _load_payload(self) -> tuple[dict, bool]:
        url, is_public, allowed_hosts = self._trusted_url()
        local = _read_json(ALIPAY_FILE_PATH, {})
        if url:
            token = os.environ.get("BEST_ALIPAY_AVAILABILITY_TOKEN", "").strip()
            headers = {"Authorization": f"Bearer {token}"} if token else {}
            try:
                downloaded = _http_json(url, referer="https://open.alipay.com/", timeout=LATEST_TIMEOUT,
                                        attempts=LATEST_ATTEMPTS, headers_extra=headers,
                                        allowed_redirect_hosts=allowed_hosts)
                validated = self._validate_payload(downloaded, require_fresh=True, public_source=is_public)
                                                                                                   
                                                                           
                try:
                    old_valid = self._validate_payload(local, require_fresh=False, public_source=is_public)
                except Exception:
                    old_valid = {}
                self._rollback_guard(validated, old_valid)
                self._write_snapshot(validated)
                self.last_snapshot_state = {"current": True, "source_id": validated.get("source_id"),
                                            "generated_at": validated.get("generated_at"), "expires_at": validated.get("expires_at"),
                                            "sequence": validated.get("sequence"), "origin": "online"}
                return validated, is_public
            except Exception as online_exc:
                try:
                    validated = self._validate_payload(local, require_fresh=True, public_source=is_public)
                    self.last_snapshot_state = {"current": True, "source_id": validated.get("source_id"),
                                                "generated_at": validated.get("generated_at"), "expires_at": validated.get("expires_at"),
                                                "sequence": validated.get("sequence"), "origin": "verified-cache"}
                    return validated, is_public
                except Exception:
                    stale = self._stale_summary(local, public_source=is_public)
                    self.last_snapshot_state = {"current": False, "historical_only": stale}
                    raise DataError(f"可信在线可购状态源不可用，且没有仍在有效期内的验签快照：{online_exc}\n{stale}") from online_exc

                                                                                                     
                                                                            
        stale = self._stale_summary(local, public_source=True)
        self.last_snapshot_state = {"current": False, "historical_only": stale}
        raise DataError(
            "未取得可信的支付宝当前可购买基金份额，程序已拒绝生成“支付宝 Top 10”。\n"
            "截至本发行版构建时，公开资料没有提供一个无需机构 app_id/权限、可覆盖支付宝全量当前可购份额的官方公共 API；"
            "因此发行版不会伪造默认地址或把第三方全市场申购状态冒充成支付宝可购。\n"
            "要实现真正开箱即用，发行维护方必须发布并运营 HTTPS 签名清单，然后把 DEFAULT_URL、固定域名白名单和对应 RSA 公钥写入发行版。\n"
            + stale
        )

    @staticmethod
    def _normalize_fee_row(row: dict) -> dict:
        fees = row.get("fees") if isinstance(row.get("fees"), dict) else {}
        output = {}
        for key in (
            "purchase_fee", "management_fee_annual", "custody_fee_annual",
            "sales_service_fee_annual", "redemption_fee_3y", "redemption_fee_5y", "redemption_fee_10y",
        ):
            value = fees.get(key)
            if value is None and key.startswith("redemption_fee_"):
                value = fees.get("redemption_fee")
            output[key] = None if value is None else _rate(value)
        output["purchase_fee_standard"] = output.get("purchase_fee")
        output["purchase_fee_channel_estimate"] = (
            _rate(fees.get("purchase_fee_channel_estimate"))
            if fees.get("purchase_fee_channel_estimate") is not None else None
        )
        return output


    def snapshot(self) -> dict[str, dict]:
        payload, is_public = self._load_payload()
        payload = self._validate_payload(payload, require_fresh=True, public_source=is_public)
        declared_at = str(payload.get("generated_at") or "")
        evidence = str(payload.get("evidence") or "signed-source-declaration")
        source_id = str(payload.get("source_id") or "")
        output = {}
        for row in payload.get("funds") or []:
            if row.get("purchasable") is not True:
                continue
            code = str(row.get("code") or "")
            item_time = str(row.get("declared_at") or row.get("verified_at") or declared_at)
            fees = self._normalize_fee_row(row)
            output[code] = {
                "code": code,
                "name": str(row.get("name") or "").strip(),
                "type": str(row.get("type") or "").strip(),
                "share_class": str(row.get("share_class") or "").strip(),
                "availability_declared": True,
                "availability_status": "confirmed_purchasable",
                "availability_note": "支付宝可购：签名清单已确认",
                "fund_data_source": "东方财富基金公开数据（净值）",
                "availability_declared_at": item_time,
                "availability_generated_at": declared_at,
                "availability_expires_at": str(payload.get("expires_at") or ""),
                "availability_sequence": int(payload.get("sequence") or 0),
                "availability_signature_alg": str(payload.get("signature_alg") or ""),
                "availability_source": str(payload.get("source") or "signed-external"),
                "availability_source_id": source_id,
                "availability_evidence": evidence,
                "availability_schema_version": AVAILABILITY_SCHEMA_VERSION,
                "fees_verified": row.get("fees_verified") is True and all(
                    fees.get(key) is not None for key in (
                        "purchase_fee", "management_fee_annual", "custody_fee_annual",
                        "sales_service_fee_annual", "redemption_fee_3y", "redemption_fee_5y", "redemption_fee_10y",
                    )
                ),
                "fees": fees,
                "fees_history": row.get("fees_history") if isinstance(row.get("fees_history"), list) else [],
                "available_from": str(row.get("available_from") or "")[:10],
                "available_to": str(row.get("available_to") or "")[:10],
                "availability_history": row.get("availability_history") if isinstance(row.get("availability_history"), list) else [],
                "product_features": row.get("product_features") if isinstance(row.get("product_features"), dict) else {},
                "product_features_history": row.get("product_features_history") if isinstance(row.get("product_features_history"), list) else [],
                "benchmark": str(row.get("benchmark") or "").strip(),
                "index_code": str(row.get("index_code") or "").strip(),
                "fund_company": str(row.get("fund_company") or "").strip(),
                "theme": str(row.get("theme") or "").strip(),
            }
            output[code].update(_holding_costs(fees if output[code]["fees_verified"] else None))
        if len(output) < 10:
            raise DataError(f"当前可信可购状态源仅返回 {len(output)} 个具体份额，无法生成 Top 10")
        return output


# ===== 数据源适配器 =====

class FundDataSource:
    LIST_URL = "https://fund.eastmoney.com/js/fundcode_search.js"
    HISTORY_URL = "https://api.fund.eastmoney.com/f10/lsjz"
    PING_URL = "https://fund.eastmoney.com/pingzhongdata/{code}.js"
    MOBILE_BASE = "https://fundmobapi.eastmoney.com/FundMNewApi"
    SINA_VERIFY_URL = "https://money.finance.sina.com.cn/fund/go.php/vAkFundInfo_JJGLR/q/{code}.phtml"
    BASIC_URL = "https://fundf10.eastmoney.com/jbgk_{code}.html"
    FEE_URL = "https://fundf10.eastmoney.com/jjfl_{code}.html"

    def all_funds(self) -> list[dict]:
        text = _http_text(self.LIST_URL)
        start, end = text.find("["), text.rfind("]")
        if start < 0 or end <= start:
            raise DataError("基金清单接口返回异常")
        try:
            rows = json.loads(text[start:end + 1])
        except json.JSONDecodeError as exc:
            raise DataError("基金清单解析失败") from exc
        funds = []
        for row in rows:
            if not isinstance(row, list) or len(row) < 4 or not re.fullmatch(r"\d{6}", str(row[0])):
                continue
            funds.append({"code": str(row[0]), "name": str(row[2]), "type": str(row[3])})
        return funds

    def public_fallback_universe(self, limit: int | None = None) -> dict[str, dict]:
                                                                                            
                                                                                                   
        chosen = sorted(
            (row for row in self.all_funds() if _candidate_allowed(row.get("name", ""), row.get("type", ""))),
            key=lambda row: int(row.get("code") or 999999),
        )
        observed = _now_iso()
        output = {}
        for row in chosen:
            code = row["code"]
            output[code] = {
                **row,
                "availability_declared": False,
                "availability_status": "unknown",
                "availability_declared_at": "",
                "availability_generated_at": observed,
                "availability_expires_at": "",
                "availability_sequence": 0,
                "availability_signature_alg": "",
                "availability_source": "东方财富基金公开基金清单（非支付宝）",
                "availability_source_id": "eastmoney-public-fallback",
                "availability_evidence": "未取得支付宝可购证明；仅确认公开基金数据存在",
                "availability_note": "支付宝可购状态未知（不会因此排除；下单前需在支付宝确认）",
                "availability_schema_version": 0,
                "fund_data_source": "东方财富基金公开基金清单/历史净值",
                "fees_verified": False, "fees": {}, "fees_history": [],
                "available_from": "", "available_to": "", "availability_history": [],
                "share_class": "", "product_features": {}, "product_features_history": [],
                "benchmark": "", "index_code": "", "fund_company": "", "theme": "",
                **_holding_costs({}),
            }
        if len(output) < 25:
            raise DataError(f"公开基金候选池仅 {len(output)} 个，无法进行长期分析")
        return output

    @staticmethod
    def structural_prefilter(availability: dict[str, dict], limit: int | None = None) -> dict[str, dict]:
        rows = []
        for code, row in availability.items():
            name = str(row.get("name") or "")
            fund_type = str(row.get("type") or "")
            status = str(row.get("availability_status") or "unknown")
            if status in PURCHASE_UNAVAILABLE_STATUSES:
                continue
            if not _candidate_allowed(name, fund_type):
                continue
            if row.get("termination_date"):
                continue
            rows.append((code, row))
        rows.sort(key=lambda pair: pair[0])
        if limit is not None:
            rows = rows[:max(0, int(limit))]
        return dict(rows)

    @staticmethod
    def _strip_html(value: str) -> str:
        value = re.sub(r"<script[\s\S]*?</script>|<style[\s\S]*?</style>", " ", value or "", flags=re.I)
        value = re.sub(r"<[^>]+>", " ", value)
        return re.sub(r"\s+", " ", html.unescape(value)).strip()

    @classmethod
    def _parse_basic_metadata(cls, text: str) -> dict:
        def cell(*labels: str) -> str:
            for label in labels:
                patterns = (
                    rf">\s*{re.escape(label)}\s*</(?:th|td)>\s*<(?:td|th)[^>]*>([\s\S]*?)</(?:td|th)>",
                    rf"{re.escape(label)}\s*</[^>]+>\s*<(?:td|th)[^>]*>([\s\S]*?)</(?:td|th)>",
                )
                for pattern in patterns:
                    match = re.search(pattern, text or "", flags=re.I)
                    if match:
                        value = cls._strip_html(match.group(1))
                        if value:
                            return value
            return ""

        company = cell("基金管理人", "管理人")
        benchmark = cell("业绩比较基准")
        tracking = cell("跟踪标的", "标的指数")
        inception_raw = cell("成立日期/规模", "成立日期")
        termination_raw = cell("终止日期", "清盘日期")
        size_raw = cell("基金规模") or inception_raw
        purchase_status = cell("申购状态", "申购赎回状态")
        tracking_error_raw = cell("跟踪误差", "年化跟踪误差")
        manager_raw = cell("基金经理", "现任基金经理")
        manager_tenure_raw = cell("任职时间", "任职年限")
        objective_match = re.search(
            r"(?:投资目标|投资方向)\s*</[^>]+>\s*(?:<[^>]+>)*([\s\S]{0,1200}?)(?=<h\d|</div>)",
            text or "", flags=re.I,
        )
        objective = cls._strip_html(objective_match.group(1)) if objective_match else ""
        inception_match = re.search(r"\d{4}[-年]\d{1,2}[-月]\d{1,2}", inception_raw)
        termination_match = re.search(r"\d{4}[-年]\d{1,2}[-月]\d{1,2}", termination_raw)

        def normalized_date(match) -> str:
            if not match:
                return ""
            value = match.group(0).replace("年", "-").replace("月", "-").replace("日", "")
            try:
                return _dt.date.fromisoformat("-".join(f"{int(x):02d}" if i else x for i, x in enumerate(value.split("-")))).isoformat()
            except ValueError:
                return ""

        no_tracking = any(word in tracking for word in ("无跟踪标的", "不适用", "--", "暂无"))
        index_code = "" if no_tracking else tracking
        public_theme = _theme(" ".join(value for value in (tracking, objective) if value))
        if public_theme == "宽基/全市场":
            public_theme = ""
        size_match = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*亿元", size_raw)
        te_match = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*%", tracking_error_raw)
        product_features = {}
        if size_match:
            product_features["fund_size_billion"] = float(size_match.group(1)) / 10.0
        if te_match:
            product_features["tracking_error_annual"] = _rate(float(te_match.group(1)) / 100.0)
        plain = cls._strip_html(text or "")
        tenure_text = " ".join(value for value in (manager_tenure_raw, manager_raw, plain) if value)
        tenure_match = re.search(r"(?:任职时间|任职年限|任职以来)[^0-9]{0,24}([0-9]+(?:\.[0-9]+)?)\s*年", tenure_text)
        if tenure_match:
            product_features["manager_tenure_years"] = _clamp(float(tenure_match.group(1)), 0.0, 40.0)
        manager_names = []
        for value in re.findall(r"(?:基金经理|现任基金经理)[：:]?\s*([\u4e00-\u9fa5·]{2,12})", plain):
            if value not in manager_names:
                manager_names.append(value)
        if manager_raw:
            product_features["manager_name"] = manager_raw
        if manager_names:
            # 这里只记录当前公开页可证实的经理信息；历史换帅次数必须依赖后续历史快照累积，不能用今天页面回填历史。
            product_features["manager_count_current"] = len(manager_names)
        if public_theme:
            product_features["style_label"] = public_theme
        valuation_patterns = {
            "pe_percentile": r"(?:PE|市盈率)[^。；;]{0,80}(?:历史)?百分位[^0-9]{0,12}([0-9]+(?:\.[0-9]+)?)\s*%",
            "pb_percentile": r"(?:PB|市净率)[^。；;]{0,80}(?:历史)?百分位[^0-9]{0,12}([0-9]+(?:\.[0-9]+)?)\s*%",
            "dividend_yield_percentile": r"(?:股息率|股息)[^。；;]{0,80}(?:历史)?百分位[^0-9]{0,12}([0-9]+(?:\.[0-9]+)?)\s*%",
            "equity_risk_premium_percentile": r"(?:风险溢价|ERP)[^。；;]{0,80}(?:历史)?百分位[^0-9]{0,12}([0-9]+(?:\.[0-9]+)?)\s*%",
        }
        for key, pattern in valuation_patterns.items():
            match = re.search(pattern, plain, flags=re.I)
            if match:
                product_features[key] = _clamp(float(match.group(1)) / 100.0, 0.0, 1.0)
        equity_match = re.search(r"(?:股票|权益)(?:资产)?[^0-9%]{0,40}(?:占基金资产|仓位|比例)[^0-9%]{0,20}([0-9]+(?:\.[0-9]+)?)\s*%", objective + " " + plain)
        if equity_match:
            product_features["equity_exposure"] = _clamp(float(equity_match.group(1)) / 100.0, 0.0, 1.0)
        return {
            "fund_company": company,
            "benchmark": benchmark,
            "index_code": index_code,
            "theme": public_theme,
            "inception_date": normalized_date(inception_match),
            "termination_date": normalized_date(termination_match),
            "public_purchase_status": purchase_status,
            "fund_manager": manager_raw,
            "product_features": product_features,
            "metadata_source": "东方财富基金档案公开结构化页面",
            "metadata_checked_at": _now_iso(),
        }

    @classmethod
    def _parse_fee_schedule(cls, text: str) -> dict:
        plain = cls._strip_html(text)

        def labelled_rate(label: str) -> float | None:
            match = re.search(rf"{re.escape(label)}[^0-9%]{{0,40}}([0-9]+(?:\.[0-9]+)?)\s*%", plain)
            if match:
                return _rate(float(match.group(1)) / 100.0)
            explicit_zero = re.search(rf"{re.escape(label)}[^。；;]{{0,40}}(?:0(?:\.0+)?\s*%|不收取|免收|免费)", plain)
            return 0.0 if explicit_zero else None

        def segment_after(label: str) -> str:
            position = (text or "").find(label)
            return (text or "")[position:position + 24000] if position >= 0 else ""

        purchase = None
        purchase_channel_estimate = None
        for row in re.findall(r"<tr[^>]*>([\s\S]*?)</tr>", segment_after("申购费率"), flags=re.I):
            row_text = cls._strip_html(row)
            rates = [float(value) / 100.0 for value in re.findall(r"([0-9]+(?:\.[0-9]+)?)\s*%", row_text)]
            if rates and any(word in row_text for word in ("小于", "以下", "万元", "申购")):
                purchase = max(rates)  # 标准费率：不再把最低折扣当确定成本
                purchase_channel_estimate = min(rates)
                break
        if purchase is None and re.search(r"申购费率[^。；;]{0,80}(?:0(?:\.0+)?\s*%|不收取|免收)", plain):
            purchase = 0.0
            purchase_channel_estimate = 0.0

        def duration_bounds(row_text: str) -> tuple[float, float]:
            lower, upper = 0.0, float("inf")
            units = {"天":1.0, "日":1.0, "月":30.4369, "年":365.2425}
            for pattern, kind in (
                (r"(?:大于等于|不少于|≥)([0-9]+(?:\.[0-9]+)?)\s*(天|日|月|年)", "lower"),
                (r"([0-9]+(?:\.[0-9]+)?)\s*(天|日|月|年)(?:及|或)?以上", "lower"),
                (r"(?:小于|少于|<)([0-9]+(?:\.[0-9]+)?)\s*(天|日|月|年)", "upper"),
                (r"([0-9]+(?:\.[0-9]+)?)\s*(天|日|月|年)(?:以内|以下)", "upper"),
            ):
                for value, unit in re.findall(pattern, row_text):
                    days = float(value) * units[unit]
                    if kind == "lower":
                        lower = max(lower, days)
                    else:
                        upper = min(upper, days)
            return lower, upper

        redemption_rows = []
        for row in re.findall(r"<tr[^>]*>([\s\S]*?)</tr>", segment_after("赎回费率"), flags=re.I):
            row_text = cls._strip_html(row)
            rates = [float(value) / 100.0 for value in re.findall(r"([0-9]+(?:\.[0-9]+)?)\s*%", row_text)]
            if not rates and any(word in row_text for word in ("不收取", "免收")):
                rates = [0.0]
            if not rates or not any(unit in row_text for unit in ("天", "日", "月", "年", "以上", "以下")):
                continue
            lower, upper = duration_bounds(row_text)
            redemption_rows.append((lower, upper, min(rates)))

        fees = {
            "purchase_fee": purchase,
            "purchase_fee_standard": purchase,
            "purchase_fee_channel_estimate": purchase_channel_estimate,
            "management_fee_annual": labelled_rate("管理费率"),
            "custody_fee_annual": labelled_rate("托管费率"),
            "sales_service_fee_annual": labelled_rate("销售服务费率"),
        }
        for years in (3, 5, 10):
            days = years * 365.2425
            matching = [rate for lower, upper, rate in redemption_rows if lower <= days < upper]
            fees[f"redemption_fee_{years}y"] = min(matching) if matching else None

        required = (
            "purchase_fee", "management_fee_annual", "custody_fee_annual", "sales_service_fee_annual",
            "redemption_fee_3y", "redemption_fee_5y", "redemption_fee_10y",
        )
        verified_fields = {key: fees.get(key) is not None for key in required}
        complete = all(verified_fields.values())
        normalized = {key: (None if value is None else _rate(value)) for key, value in fees.items()}
        return {
            "fees": normalized,
            "fees_verified": complete,
            "fee_schedule_complete": complete,
            "fee_field_verified": verified_fields,
            "fees_source": "东方财富公开费率表（支付宝下单前仍需复核）",
            **_holding_costs(normalized if complete else None),
        }


    def basic_metadata(self, code: str) -> dict:
        text = _http_text(
            self.BASIC_URL.format(code=code), referer=f"https://fund.eastmoney.com/{code}.html",
            timeout=5.0, attempts=1,
        )
        result = self._parse_basic_metadata(text)
        try:
            fee_text = _http_text(
                self.FEE_URL.format(code=code), referer=f"https://fund.eastmoney.com/{code}.html",
                timeout=5.0, attempts=1,
            )
            result.update(self._parse_fee_schedule(fee_text))
        except DataError:
            pass
        return result

    def metadata_many(self, funds: list[dict]) -> dict[str, dict]:
        targets = [fund for fund in funds if re.fullmatch(r"\d{6}", str(fund.get("code") or ""))]
        output = {}
        if not targets:
            return output
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(6, len(targets)), thread_name_prefix="fund-meta") as pool:
            future_map = {pool.submit(self.basic_metadata, str(fund["code"])): str(fund["code"]) for fund in targets}
            for future in concurrent.futures.as_completed(future_map):
                code = future_map[future]
                try:
                    output[code] = future.result()
                except Exception:
                    output[code] = {"metadata_source": "公开基金档案暂不可用", "metadata_checked_at": _now_iso()}
        return output

    def candidates(self, availability: dict[str, dict], progress=lambda *_: None) -> list[dict]:
                                                                                                  
                                                                                                
        progress("读取基金全集并与当前可购声明求交集", 6)
        market = {item["code"]: item for item in self.all_funds()}
        selected = []
        for code, verified in availability.items():
            meta = market.get(code, {})
            name = verified.get("name") or meta.get("name") or code
            fund_type = verified.get("type") or meta.get("type") or "其他"
            if not _candidate_allowed(name, fund_type):
                continue
            selected.append({**meta, **verified, "code": code, "name": name, "type": fund_type})
        selected.sort(key=lambda item: item["code"])
        if len(selected) < 25:
            raise DataError(f"当前声明可购且可用于长期量化分析的份额仅 {len(selected)} 个，样本不足")
        return selected

    @staticmethod
    def _history_rows(payload) -> tuple[list[dict], int]:
        if not isinstance(payload, dict):
            return [], 0
        data = payload.get("Data")
        if isinstance(data, dict):
            rows = data.get("LSJZList") or []
            total = int(_finite(data.get("TotalCount"), len(rows)))
            return rows, total
        rows = payload.get("Datas") or []
        total = int(_finite(payload.get("TotalCount"), len(rows)))
        return rows, total

    @staticmethod
    def _normalize_history(rows: list[dict]) -> dict:
        clean = []
        for row in rows:
            date = str(row.get("FSRQ") or "")[:10]
            nav = _finite(row.get("DWJZ"), float("nan"))
            accumulated = _finite(row.get("LJJZ"), float("nan"))
            event = str(row.get("FHFCZ") or row.get("unitMoney") or "").strip()
            if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date) or not math.isfinite(nav) or nav <= 0:
                continue
            change_raw = row.get("JZZZL")
            change = None if change_raw in (None, "", "--") else _finite(change_raw) / 100.0
            clean.append((date, nav, accumulated if math.isfinite(accumulated) and accumulated > 0 else None, change, event))
        clean.sort(key=lambda item: item[0])
        clean = list({item[0]: item for item in clean}.values())
        dates, returns = [], []
        previous_nav = None
        previous_accumulated = None
        provider_fallbacks = corporate_actions = accumulated_confirmations = 0

        def cash_dividend(text: str) -> float:
            if not text:
                return 0.0
                                                                 
            match = re.search(r"每\s*(10)?\s*份[^0-9]{0,12}(?:派|分红|现金)[^0-9]{0,8}([0-9]+(?:\.[0-9]+)?)", text)
            if match:
                amount = _finite(match.group(2), 0.0)
                return amount / 10.0 if match.group(1) else amount
            match = re.search(r"(?:派现金|现金分红)[^0-9]{0,6}([0-9]+(?:\.[0-9]+)?)", text)
            return _finite(match.group(1), 0.0) if match else 0.0

        for date, nav, accumulated, reported, event in clean:
            dates.append(date)
            if previous_nav is None:
                value = 0.0
            else:
                mechanical = nav / previous_nav - 1.0
                accumulated_move = None
                if accumulated is not None and previous_accumulated is not None and previous_accumulated > 0:
                    accumulated_move = accumulated / previous_accumulated - 1.0
                dividend = cash_dividend(event)
                event_flag = bool(event and event not in ("--", "暂无分红"))
                lggj_support = (
                    reported is not None and accumulated_move is not None and -0.8 < reported < 2.0
                    and abs(reported - accumulated_move) <= 0.006
                    and abs(reported - mechanical) >= 0.015
                )
                if dividend > 0:
                    value = (nav + dividend) / previous_nav - 1.0
                    corporate_actions += 1
                    if reported is not None and abs(value - reported) <= 0.006:
                        accumulated_confirmations += int(accumulated_move is not None)
                elif reported is not None and -0.8 < reported < 2.0 and abs(reported - mechanical) <= 0.0035:
                                                                                               
                    value = mechanical
                elif reported is not None and -0.8 < reported < 2.0 and (event_flag or lggj_support):
                                                                                                     
                                                                                                   
                                                                                       
                    value = reported
                    corporate_actions += 1
                    provider_fallbacks += 1
                    accumulated_confirmations += int(lggj_support)
                else:
                    value = mechanical
            returns.append(_clamp(value, -0.8, 2.0))
            previous_nav = nav
            if accumulated is not None:
                previous_accumulated = accumulated
        return {
            "dates": dates, "returns": returns,
            "latest_nav": clean[-1][1] if clean else None,
            "latest_date": clean[-1][0] if clean else "",
            "return_basis": "adjusted-unit-nav+explicit-corporate-actions",
            "return_provider_fallbacks": provider_fallbacks,
            "return_corporate_actions": corporate_actions,
            "return_accumulated_confirmations": accumulated_confirmations,
        }

    def _ping_history(self, code: str, start: _dt.date) -> dict:
        params = urllib.parse.urlencode({"v": int(time.time() * 1000)})
        text = _http_text(
            self.PING_URL.format(code=code) + "?" + params,
            referer=f"https://fund.eastmoney.com/{code}.html", attempts=1,
        )
        match = re.search(r"var\s+Data_netWorthTrend\s*=\s*(\[[\s\S]*?\])\s*;", text)
        if not match:
            raise DataError(f"{code} 走势图数据缺失")
        try:
            source_rows = json.loads(match.group(1))
        except json.JSONDecodeError:
            source_rows = []
            for object_text in re.findall(r"\{[^{}]*\}", match.group(1)):
                x_match = re.search(r'["\']?x["\']?\s*:\s*(\d+)', object_text)
                y_match = re.search(r'["\']?y["\']?\s*:\s*(-?\d+(?:\.\d+)?)', object_text)
                r_match = re.search(r'["\']?equityReturn["\']?\s*:\s*(-?\d+(?:\.\d+)?)', object_text)
                if x_match and y_match:
                    source_rows.append({
                        "x": int(x_match.group(1)), "y": float(y_match.group(1)),
                        "equityReturn": float(r_match.group(1)) if r_match else None,
                        "unitMoney": "",
                    })
        rows = []
        for row in source_rows:
            try:
                day = _dt.datetime.fromtimestamp(float(row.get("x")) / 1000.0, tz=_dt.timezone.utc).date()
            except (TypeError, ValueError, OSError, OverflowError):
                continue
            if day < start:
                continue
            rows.append({"FSRQ": day.isoformat(), "DWJZ": row.get("y"), "JZZZL": row.get("equityReturn"), "FHFCZ": row.get("unitMoney")})
        result = self._normalize_history(rows)
        if len(result["dates"]) < 450:
            raise DataError(f"{code} 走势图历史不足")
        name_match = re.search(r"var\s+fS_name\s*=\s*['\"]([^'\"]+)['\"]", text)
        if name_match:
            result["name"] = name_match.group(1).strip()
        return result

    def history(self, code: str) -> dict:
        today = _china_today()
        start = today - _dt.timedelta(days=366 * HISTORY_YEARS + 60)
        errors = []
        try:
            return self._ping_history(code, start)
        except DataError as exc:
            errors.append(str(exc))
        mobile_params = {
            "FCODE": code, "pageIndex": 1, "pageSize": 4200, "plat": "Android",
            "appType": "ttjj", "product": "EFund", "version": "6.2.4",
            "deviceid": "best-alipay-funds-local",
        }
        try:
            payload = _http_json(f"{self.MOBILE_BASE}/FundMNHisNetList?" + urllib.parse.urlencode(mobile_params), attempts=1)
            rows, _ = self._history_rows(payload)
            result = self._normalize_history(rows)
            if len(result["dates"]) >= 450:
                return result
        except DataError as exc:
            errors.append(str(exc))
        params = {
            "fundCode": code, "pageIndex": 1, "pageSize": 4200,
            "startDate": start.isoformat(), "endDate": today.isoformat(), "_": int(time.time() * 1000),
        }
        try:
            payload = _http_json(
                self.HISTORY_URL + "?" + urllib.parse.urlencode(params),
                referer="https://fundf10.eastmoney.com/", attempts=1,
            )
            rows, total = self._history_rows(payload)
            if len(rows) >= 450 or total <= len(rows):
                result = self._normalize_history(rows)
                if len(result["dates"]) >= 450:
                    return result
        except DataError as exc:
            errors.append(str(exc))
        raise DataError(f"{code} 历史净值不足或暂不可用：{'；'.join(errors[-2:]) or '数据不足'}")

    def update_history(self, code: str, cached: dict) -> dict:
        dates = list(cached.get("dates") or [])
        returns = list(cached.get("returns") or [])
        if len(dates) < MIN_HISTORY_POINTS or len(dates) != len(returns):
            return self.history(code)
        try:
            last_date = _dt.date.fromisoformat(str(cached.get("latest_date") or dates[-1])[:10])
        except ValueError:
            return self.history(code)
        today = _china_today()
        if last_date >= today:
            return {
                "dates": dates, "returns": returns,
                "latest_nav": cached.get("latest_nav"), "latest_date": str(cached.get("latest_date") or dates[-1])[:10],
            }
        delta = max(1, (today - last_date).days)
        params = {
            "fundCode": code, "pageIndex": 1, "pageSize": min(3200, max(64, delta * 3 + 20)),
            "startDate": (last_date - _dt.timedelta(days=7)).isoformat(), "endDate": today.isoformat(), "_": int(time.time() * 1000),
        }
        try:
            payload = _http_json(
                self.HISTORY_URL + "?" + urllib.parse.urlencode(params),
                referer="https://fundf10.eastmoney.com/", attempts=1,
            )
            rows, _ = self._history_rows(payload)
            incremental = self._normalize_history(rows)
            if incremental.get("dates"):
                known = set(dates)
                for day, value in zip(incremental["dates"], incremental["returns"]):
                    if day > dates[-1] and day not in known:
                        dates.append(day)
                        returns.append(value)
                        known.add(day)
                latest_date = max(str(cached.get("latest_date") or dates[-1])[:10], incremental.get("latest_date") or "")
                latest_nav = incremental.get("latest_nav") if incremental.get("latest_date") == latest_date else cached.get("latest_nav")
                return {"dates": dates, "returns": returns, "latest_nav": latest_nav, "latest_date": latest_date}
        except Exception:
            pass
                                                                                                
        return self.history(code)

    def latest(self, codes: list[str], *, timeout=LATEST_TIMEOUT, attempts=LATEST_ATTEMPTS) -> dict[str, dict]:
        if not codes:
            return {}
        params = {
            "pageIndex": 1, "pageSize": max(10, len(codes)), "plat": "Android",
            "appType": "ttjj", "product": "EFund", "Version": "6.2.4",
            "deviceid": "best-alipay-funds-local", "Fcodes": ",".join(codes),
        }
        payload = _http_json(
            f"{self.MOBILE_BASE}/FundMNFInfo?" + urllib.parse.urlencode(params),
            attempts=attempts, timeout=timeout,
        )
        output = {}
        for row in payload.get("Datas") or []:
            code = str(row.get("FCODE") or "")
            if code not in codes:
                continue
            nav = _finite(row.get("NAV"), float("nan"))
            nav_date = str(row.get("PDATE") or "")[:10]
            if not math.isfinite(nav) or nav <= 0 or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", nav_date):
                continue
            output[code] = {
                "code": code, "name": str(row.get("SHORTNAME") or "").strip(),
                "nav": nav,
                "day_change": _finite(row.get("NAVCHGRT"), float("nan")),
                "nav_date": nav_date,
            }
        return output

    def latest_many(self, codes: list[str]) -> dict:
        codes = list(dict.fromkeys(str(code) for code in codes if re.fullmatch(r"\d{6}", str(code))))
        if not codes:
            return {"rows": {}, "requested": 0, "received": 0, "failed_codes": [], "errors": []}
        output = {}
        errors = []
        failed_batches = []
        batches = list(_chunks(codes, LATEST_BATCH_SIZE))
        workers = min(6, len(batches))
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, workers), thread_name_prefix="latest") as pool:
            future_map = {
                pool.submit(self.latest, batch, timeout=LATEST_TIMEOUT, attempts=LATEST_ATTEMPTS): batch
                for batch in batches
            }
            for future in concurrent.futures.as_completed(future_map):
                batch = future_map[future]
                try:
                    output.update(future.result())
                except Exception as exc:
                    failed_batches.extend(batch)
                    errors.append(str(exc))
        missing = [code for code in codes if code not in output]
        failed_codes = list(dict.fromkeys(failed_batches + missing))
        return {
            "rows": output,
            "requested": len(codes),
            "received": len(output),
            "failed_codes": failed_codes,
            "errors": errors,
        }


    def _sina_verify_one(self, item: dict) -> dict:
        code = str(item.get("code") or "")
        if not re.fullmatch(r"\d{6}", code):
            return {"ok": False, "reason": "invalid-code"}
        try:
            text = _http_text(
                self.SINA_VERIFY_URL.format(code=code), referer="https://finance.sina.com.cn/fund/",
                timeout=3.5, attempts=1,
            )
            normalized = re.sub(r"\s+", " ", text)
            code_ok = code in normalized
            name = str(item.get("name") or "").strip()
                                                                                                
                                                                           
            stem = re.sub(r"[A-HI-ZＡ-Ｚ]$", "", name, flags=re.I).strip()
            stem = re.sub(r"[（）()\s·•]", "", stem)
            name_ok = (not stem) or stem[:6] in re.sub(r"[（）()\s·•]", "", normalized)
            company = re.sub(r"基金管理有限公司$|基金管理$|基金$", "", str(item.get("fund_company") or "")).strip()
            company_ok = (not company) or company[:4] in normalized
            nav_match = re.search(r"(?:最新净值|昨日净值)\s*[:：]?\s*([0-9]+(?:\.[0-9]+)?)", normalized)
            sina_nav = _finite(nav_match.group(1), float("nan")) if nav_match else float("nan")
            local_nav = _finite(item.get("display_nav", item.get("latest_nav")), float("nan"))
                                                                                                   
                                                                  
            nav_ratio = abs(sina_nav / local_nav - 1.0) if math.isfinite(sina_nav) and math.isfinite(local_nav) and local_nav > 0 else None
            nav_ok = nav_ratio is None or nav_ratio <= 0.25
            return {
                "ok": bool(code_ok and name_ok and nav_ok and company_ok), "code_ok": bool(code_ok), "name_ok": bool(name_ok),
                "company_ok": bool(company_ok),
                "nav_ok": bool(nav_ok), "sina_nav": sina_nav if math.isfinite(sina_nav) else None,
                "nav_relative_diff": nav_ratio, "source": "新浪财经基金中心",
                "url_kind": "money.finance.sina.com.cn/fund",
            }
        except Exception as exc:
            return {"ok": False, "reason": str(exc)[:160], "source": "新浪财经基金中心"}

    def cross_verify_top10(self, items: list[dict]) -> dict:
        rows = list(items[:10])
        if not rows:
            return {"verified": 0, "requested": 0, "source": "新浪财经基金中心"}
        verified = 0; details = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(5, len(rows)), thread_name_prefix="sina-verify") as pool:
            future_map = {pool.submit(self._sina_verify_one, item): item for item in rows}
            for future in concurrent.futures.as_completed(future_map):
                item = future_map[future]
                try:
                    result = future.result()
                except Exception as exc:
                    result = {"ok": False, "reason": str(exc)[:160], "source": "新浪财经基金中心"}
                details[item["code"]] = result
                if result.get("ok"):
                    verified += 1
        for item in rows:
            result = details.get(item["code"], {})
            item["independent_source_verified"] = result.get("ok") is True
            item["metadata_cross_verified"] = result.get("company_ok") is True
            item["independent_source"] = "新浪财经基金中心"
            item["independent_source_nav"] = result.get("sina_nav")
            item["independent_source_note"] = result.get("reason") or ("代码/名称/净值证据一致" if result.get("ok") else "交叉核验不完整")
        return {"verified": verified, "requested": len(rows), "source": "新浪财经基金中心", "details": details}


# Preserve the original Eastmoney implementation as the primary adapter, then expose a resilient two-source facade.
PrimarySource = FundDataSource


class SecondarySource:
    """Sina public-fund adapter. It is a real fallback path, not just a final Top10 badge."""
    CATALOG_URL = "https://vip.stock.finance.sina.com.cn/fund_center/data/jsonp.php/IO.XSRV2.CallbackList['best']/NetValueReturn_Service.NetValueReturnOpen"
    HISTORY_URL = "https://stock.finance.sina.com.cn/fundInfo/view/FundInfo_LSJZ.php?symbol={code}&page={page}"
    INFO_URL = "https://stock.finance.sina.com.cn/fundInfo/view/FundInfo_XGFG.php?symbol={code}"

    @staticmethod
    def _walk_dicts(value):
        if isinstance(value, dict):
            yield value
            for child in value.values():
                yield from SecondarySource._walk_dicts(child)
        elif isinstance(value, list):
            for child in value:
                yield from SecondarySource._walk_dicts(child)

    @staticmethod
    def _fund_from_row(row: dict) -> dict | None:
        code = ""
        for key in ("symbol", "code", "fundcode", "fcode", "scode"):
            value = str(row.get(key) or "")
            match = re.search(r"(?<!\d)(\d{6})(?!\d)", value)
            if match:
                code = match.group(1); break
        if not code:
            return None
        name = next((str(row.get(key) or "").strip() for key in ("name", "sname", "fundname", "shortname") if str(row.get(key) or "").strip()), "")
        if not name:
            return None
        fund_type = next((str(row.get(key) or "").strip() for key in ("type", "typename", "fundtype", "type2") if str(row.get(key) or "").strip()), "公开基金")
        return {"code": code, "name": name, "type": fund_type}

    def all_funds(self) -> list[dict]:
        output = {}
        stale_pages = 0
        for page in range(1, 17):
            params = {"page": page, "num": 500, "sort": "form_year", "asc": 0, "ccode": "", "type2": 0, "type3": ""}
            payload = _http_json(self.CATALOG_URL + "?" + urllib.parse.urlencode(params), referer="https://vip.stock.finance.sina.com.cn/fund_center/", timeout=7.0, attempts=2)
            before = len(output)
            for row in self._walk_dicts(payload):
                item = self._fund_from_row(row)
                if item:
                    output[item["code"]] = item
            if len(output) == before:
                stale_pages += 1
            else:
                stale_pages = 0
            if stale_pages >= 2:
                break
        if len(output) < 25:
            raise DataError(f"新浪公开基金目录仅解析到 {len(output)} 个基金")
        return sorted(output.values(), key=lambda row: row["code"])

    @staticmethod
    def _history_rows_from_html(text: str) -> list[tuple[str, float, float | None]]:
        rows = []
        for block in re.findall(r"<tr[^>]*>([\s\S]*?)</tr>", text or "", flags=re.I):
            plain = PrimarySource._strip_html(block)
            match = re.search(r"(20\d{2}|19\d{2})[/-](\d{1,2})[/-](\d{1,2})\s+([0-9]+(?:\.[0-9]+)?)\s+([0-9]+(?:\.[0-9]+)?)\s+([+-]?[0-9]+(?:\.[0-9]+)?)\s*%", plain)
            if not match:
                continue
            day = f"{int(match.group(1)):04d}-{int(match.group(2)):02d}-{int(match.group(3)):02d}"
            rows.append((day, float(match.group(4)), float(match.group(6)) / 100.0))
        return rows

    def history(self, code: str) -> dict:
        collected = {}
        # Forty pages is about 800 trading-day observations: enough for the minimum 3y gate.
        # It intentionally avoids thousands of fallback HTTP calls per fund if the primary provider is down.
        for page in range(1, 41):
            text = _http_text(self.HISTORY_URL.format(code=code, page=page), referer="https://finance.sina.com.cn/fund/", timeout=6.0, attempts=2)
            rows = self._history_rows_from_html(text)
            if not rows:
                if page == 1:
                    raise DataError(f"新浪历史净值未解析到 {code}")
                break
            before = len(collected)
            for day, nav, growth in rows:
                collected[day] = (nav, growth)
            if len(collected) == before:
                break
            if len(collected) >= max(MIN_HISTORY_POINTS, 820):
                break
        if len(collected) < MIN_HISTORY_POINTS:
            raise DataError(f"新浪历史净值 {code} 仅 {len(collected)} 条，低于长期分析门槛")
        dates = sorted(collected)
        returns = []
        prev_nav = None
        for day in dates:
            nav, growth = collected[day]
            value = growth if growth is not None else (nav / prev_nav - 1.0 if prev_nav and prev_nav > 0 else 0.0)
            returns.append(_clamp(_finite(value), -0.95, 3.0))
            prev_nav = nav
        latest_day = dates[-1]
        latest_nav = collected[latest_day][0]
        return {"dates": dates, "returns": returns, "latest_nav": latest_nav, "latest_date": latest_day, "history_source": "新浪财经基金历史净值"}

    def latest_one(self, code: str) -> dict | None:
        text = _http_text(self.INFO_URL.format(code=code), referer="https://finance.sina.com.cn/fund/", timeout=4.5, attempts=1)
        plain = PrimarySource._strip_html(text)
        date_match = re.search(r"截止日期[：:]?\s*(20\d{2})[/-](\d{1,2})[/-](\d{1,2})", plain)
        nav_match = re.search(r"单位净值[：:]?\s*([0-9]+(?:\.[0-9]+)?)", plain)
        if not date_match or not nav_match:
            return None
        day = f"{int(date_match.group(1)):04d}-{int(date_match.group(2)):02d}-{int(date_match.group(3)):02d}"
        change_match = re.search(r"净值增长率[：:]?\s*([+-]?[0-9]+(?:\.[0-9]+)?)\s*%", plain)
        return {"code": code, "nav": float(nav_match.group(1)), "nav_date": day, "day_change": (_finite(change_match.group(1)) if change_match else float("nan")), "source": "新浪财经基金中心"}

    def latest_many(self, codes: list[str], limit: int | None = None) -> dict:
        codes = list(dict.fromkeys(str(code) for code in codes if re.fullmatch(r"\d{6}", str(code))))
        if limit is not None:
            codes = codes[:max(0, int(limit))]
        output, errors = {}, []
        if not codes:
            return {"rows": {}, "requested": 0, "received": 0, "failed_codes": [], "errors": []}
        workers = min(4, len(codes))
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, workers), thread_name_prefix="sina-latest") as pool:
            future_map = {pool.submit(self.latest_one, code): code for code in codes}
            for future in concurrent.futures.as_completed(future_map):
                code = future_map[future]
                try:
                    row = future.result()
                    if row:
                        output[code] = row
                except Exception as exc:
                    errors.append(f"{code}:{exc}")
        missing = [code for code in codes if code not in output]
        return {"rows": output, "requested": len(codes), "received": len(output), "failed_codes": missing, "errors": errors}

    def basic_metadata(self, code: str) -> dict:
        text = _http_text(self.INFO_URL.format(code=code), referer="https://finance.sina.com.cn/fund/", timeout=5.0, attempts=1)
        plain = PrimarySource._strip_html(text)
        def capture(*patterns):
            for pattern in patterns:
                match = re.search(pattern, plain)
                if match:
                    return re.sub(r"\s+", " ", match.group(1)).strip()
            return ""
        purchase = capture(r"申购状态[：:]?\s*([^\s|]{2,24})", r"交易状态[：:]?\s*([^\s|]{2,24})")
        company = capture(r"(?:基金管理人|基金管理公司|管理人)[：:]?\s*([^|]{2,40}?基金(?:管理)?有限公司)")
        manager = capture(r"基金经理[：:]?\s*([\u4e00-\u9fa5·、]{2,30})")
        return {"fund_company": company, "fund_manager": manager, "public_purchase_status": purchase, "metadata_source_secondary": "新浪财经基金中心", "metadata_checked_at_secondary": _now_iso()}


class FundDataSource:
    """Two-adapter facade with automatic source degradation and independent public evidence."""
    _parse_fee_schedule = staticmethod(PrimarySource._parse_fee_schedule)
    _history_rows = staticmethod(PrimarySource._history_rows)
    _normalize_history = staticmethod(PrimarySource._normalize_history)
    _strip_html = staticmethod(PrimarySource._strip_html)

    def __init__(self):
        self.primary = PrimarySource()
        self.secondary = SecondarySource()
        self.source_health = {"primary": 1.0, "secondary": 1.0}
        self.source_degraded = {"primary": False, "secondary": False}
        self.source_contract = {"checked": False, "details": {}}
        self._catalog_cache: list[dict] | None = None
        self._catalog_cache_at = 0.0

    def __getattr__(self, name):
        return getattr(self.primary, name)

    @staticmethod
    def _contract_row_valid(row: dict) -> bool:
        code = str(row.get("code") or "")
        name = str(row.get("name") or "").strip()
        return bool(re.fullmatch(r"\d{6}", code) and 1 < len(name) <= 100)

    def startup_contract_test(self) -> dict:
        if self.source_contract.get("checked"):
            return dict(self.source_contract)
        details = {}
        for key, adapter in (("primary", self.primary), ("secondary", self.secondary)):
            received_but_invalid = False
            notes = []
            try:
                catalog = adapter.all_funds()
                valid = [row for row in catalog if isinstance(row, dict) and self._contract_row_valid(row)]
                present = [code for code in SOURCE_CONTRACT_PROBES if any(str(row.get("code")) == code for row in valid)]
                if len(valid) < 100 or len(present) < 2:
                    received_but_invalid = True; notes.append(f"目录契约异常 valid={len(valid)} probes={len(present)}")
                else:
                    try:
                        latest = adapter.latest_many(present[:3])
                        rows = latest.get("rows") or {}
                        valid_latest = 0
                        for code, row in rows.items():
                            nav = _finite(row.get("nav"), float("nan")); day = str(row.get("nav_date") or "")[:10]
                            if math.isfinite(nav) and nav > 0 and re.fullmatch(r"\d{4}-\d{2}-\d{2}", day):
                                try:
                                    if -2 <= (_china_today() - _dt.date.fromisoformat(day)).days <= 40:
                                        valid_latest += 1
                                except ValueError:
                                    pass
                        if valid_latest < max(1, len(present[:3]) - 1):
                            received_but_invalid = True; notes.append(f"最新净值契约异常 {valid_latest}/{len(present[:3])}")
                    except Exception as exc:
                        notes.append(f"最新净值暂不可达:{type(exc).__name__}")
                    try:
                        meta = adapter.basic_metadata(present[0])
                        if not isinstance(meta, dict) or not (meta.get("metadata_checked_at") or meta.get("metadata_checked_at_secondary")):
                            received_but_invalid = True; notes.append("元数据契约异常")
                    except Exception as exc:
                        notes.append(f"元数据暂不可达:{type(exc).__name__}")
            except Exception as exc:
                # Connectivity/remote outage is not automatically treated as parser drift.
                notes.append(f"目录暂不可达:{type(exc).__name__}")
            if received_but_invalid:
                self.source_degraded[key] = True
                self.source_health[key] *= 0.20
            details[key] = {"degraded": self.source_degraded[key], "note": "；".join(notes) or "契约通过"}
        self.source_contract = {"checked": True, "details": details, "checked_at": _now_iso()}
        if all(self.source_degraded.values()):
            raise DataError("东方财富与新浪的数据格式契约均异常，已自动熔断，拒绝让疑似错字段进入模型")
        return dict(self.source_contract)

    @staticmethod
    def structural_prefilter(availability: dict[str, dict], limit: int | None = None) -> dict[str, dict]:
        return PrimarySource.structural_prefilter(availability, limit)

    def all_funds(self) -> list[dict]:
        if self._catalog_cache is not None and time.monotonic() - self._catalog_cache_at < 20 * 60:
            return [dict(row) for row in self._catalog_cache]
        primary_rows = secondary_rows = []
        errors = []
        try:
            if self.source_degraded.get("primary"):
                raise DataError("东方财富源已因格式契约异常熔断")
            primary_rows = self.primary.all_funds()
        except Exception as exc:
            self.source_health["primary"] *= 0.35; errors.append(f"东方财富目录:{exc}")
        try:
            if self.source_degraded.get("secondary"):
                raise DataError("新浪源已因格式契约异常熔断")
            secondary_rows = self.secondary.all_funds()
        except Exception as exc:
            self.source_health["secondary"] *= 0.50; errors.append(f"新浪目录:{exc}")
        if not primary_rows and not secondary_rows:
            raise DataError("双基金目录均不可用：" + "；".join(errors))
        merged = {}
        for source_name, rows in (("东方财富", primary_rows), ("新浪财经", secondary_rows)):
            for row in rows:
                code = str(row.get("code") or "")
                if not re.fullmatch(r"\d{6}", code):
                    continue
                item = merged.setdefault(code, {"code": code, "name": "", "type": ""})
                if not item.get("name") and row.get("name"):
                    item["name"] = row.get("name")
                if not item.get("type") and row.get("type"):
                    item["type"] = row.get("type")
                sources = set(item.get("catalog_sources") or [])
                sources.add(source_name); item["catalog_sources"] = sorted(sources)
        for item in merged.values():
            item["public_catalog_confirmations"] = len(item.get("catalog_sources") or [])
            item["availability_public_signals"] = (["multi-public-catalog"] if item["public_catalog_confirmations"] >= 2 else [])
        if len(merged) < 25:
            raise DataError(f"双源合并基金目录仅 {len(merged)} 个")
        result = sorted(merged.values(), key=lambda row: row["code"])
        self._catalog_cache = [dict(row) for row in result]
        self._catalog_cache_at = time.monotonic()
        return result

    def public_fallback_universe(self, limit: int | None = None) -> dict[str, dict]:
        chosen = sorted((row for row in self.all_funds() if _candidate_allowed(row.get("name", ""), row.get("type", ""))), key=lambda row: int(row.get("code") or 999999))
        if limit is not None:
            chosen = chosen[:max(0, int(limit))]
        observed = _now_iso(); output = {}
        for row in chosen:
            code = row["code"]
            output[code] = {**row, "availability_declared": False, "availability_status": "unknown", "availability_declared_at": "", "availability_generated_at": observed, "availability_expires_at": "", "availability_sequence": 0, "availability_signature_alg": "", "availability_source": "公开基金多信号候选（非支付宝官方）", "availability_source_id": "public-multisignal-fallback", "availability_evidence": "支付宝签名证据未知；公开目录/申购/净值活跃度将分别计分", "availability_note": "支付宝证据未知；将用公开申购状态、在售活跃度和跨渠道存在性分层", "availability_schema_version": 0, "fund_data_source": "东方财富 + 新浪财经公开基金数据", "fees_verified": False, "fees": {}, "fees_history": [], "available_from": "", "available_to": "", "availability_history": [], "share_class": "", "product_features": {}, "product_features_history": [], "benchmark": "", "index_code": "", "fund_company": "", "theme": "", **_holding_costs({})}
        if len(output) < 25:
            raise DataError(f"公开基金候选池仅 {len(output)} 个，无法进行长期分析")
        return output

    def history(self, code: str) -> dict:
        try:
            if self.source_degraded.get("primary"):
                raise DataError("东方财富源已熔断")
            result = self.primary.history(code)
            result["history_source"] = "东方财富基金历史净值"
            return result
        except Exception as primary_exc:
            self.source_health["primary"] *= 0.92
            try:
                if self.source_degraded.get("secondary"):
                    raise DataError("新浪源已熔断")
                result = self.secondary.history(code)
                result["history_fallback_reason"] = str(primary_exc)[:200]
                return result
            except Exception as secondary_exc:
                self.source_health["secondary"] *= 0.92
                raise DataError(f"{code} 双历史源失败：东方财富={primary_exc}；新浪={secondary_exc}") from secondary_exc

    def update_history(self, code: str, cached: dict) -> dict:
        try:
            result = self.primary.update_history(code, cached)
            result["history_source"] = "东方财富基金历史净值"
            return result
        except Exception:
            return self.secondary.history(code)

    @staticmethod
    def _merge_latest_rows(primary: dict, secondary: dict) -> dict:
        output = dict(primary or secondary or {})
        sources = []
        if primary: sources.append("东方财富")
        if secondary: sources.append("新浪财经")
        output["latest_sources"] = sources
        output["latest_public_confirmations"] = len(sources)
        if primary and secondary:
            pnav, snav = _finite(primary.get("nav"), float("nan")), _finite(secondary.get("nav"), float("nan"))
            if math.isfinite(pnav) and math.isfinite(snav) and pnav > 0:
                output["latest_cross_source_relative_diff"] = abs(snav / pnav - 1.0)
        return output

    def latest_many(self, codes: list[str]) -> dict:
        codes = list(dict.fromkeys(str(code) for code in codes if re.fullmatch(r"\d{6}", str(code))))
        try:
            if self.source_degraded.get("primary"):
                raise DataError("东方财富源已熔断")
            primary_result = self.primary.latest_many(codes)
        except Exception as exc:
            primary_result = {"rows": {}, "requested": len(codes), "received": 0, "failed_codes": codes, "errors": [str(exc)]}
        primary_rows = primary_result.get("rows") or {}
        # Cross-check a bounded representative set; if primary misses codes, those are first in line for secondary takeover.
        missing = [code for code in codes if code not in primary_rows]
        secondary_targets = list(dict.fromkeys(missing + codes[:20]))[:60]
        try:
            if self.source_degraded.get("secondary"):
                raise DataError("新浪源已熔断")
            secondary_result = self.secondary.latest_many(secondary_targets)
        except Exception as exc:
            secondary_result = {"rows": {}, "requested": len(secondary_targets), "received": 0, "failed_codes": secondary_targets, "errors": [str(exc)]}
        secondary_rows = secondary_result.get("rows") or {}
        merged = {}
        for code in codes:
            if code in primary_rows or code in secondary_rows:
                merged[code] = self._merge_latest_rows(primary_rows.get(code), secondary_rows.get(code))
        failed = [code for code in codes if code not in merged]
        return {"rows": merged, "requested": len(codes), "received": len(merged), "failed_codes": failed, "errors": list(primary_result.get("errors") or []) + list(secondary_result.get("errors") or [])}

    def latest(self, codes: list[str], **_kwargs) -> dict[str, dict]:
        return self.latest_many(codes)["rows"]

    def basic_metadata(self, code: str) -> dict:
        primary = secondary = {}
        try:
            if self.source_degraded.get("primary"):
                raise DataError("东方财富源已熔断")
            primary = self.primary.basic_metadata(code)
        except Exception: self.source_health["primary"] *= 0.98
        try:
            if self.source_degraded.get("secondary"):
                raise DataError("新浪源已熔断")
            secondary = self.secondary.basic_metadata(code)
        except Exception: self.source_health["secondary"] *= 0.98
        if not primary and not secondary:
            raise DataError(f"{code} 双元数据源均不可用")
        output = dict(primary or {})
        for key, value in secondary.items():
            if value and not output.get(key): output[key] = value
        statuses = [str(value.get("public_purchase_status") or "") for value in (primary, secondary) if value]
        # Purchase-side restrictions must not be conflated with redemption-only restrictions or large-purchase limits.
        def _public_status_is_open(text: str) -> bool:
            normalized = re.sub(r"\s+", "", str(text or ""))
            purchase_blocked = (
                ("暂停申购" in normalized and "暂停大额申购" not in normalized)
                or "终止申购" in normalized
                or any(word in normalized for word in ("封闭期", "基金清盘", "终止运作", "基金终止"))
            )
            return any(word in normalized for word in ("开放申购", "可申购", "开放")) and not purchase_blocked
        open_count = sum(_public_status_is_open(text) for text in statuses)
        signals = set(output.get("availability_public_signals") or [])
        if open_count: signals.add("public-purchase-open")
        if len(statuses) >= 2: signals.add("multi-public-metadata")
        output["availability_public_signals"] = sorted(signals)
        output["availability_public_confirmations"] = len(signals)
        output["metadata_sources"] = [name for name, value in (("东方财富", primary), ("新浪财经", secondary)) if value]
        output["public_purchase_status_secondary"] = str(secondary.get("public_purchase_status") or "")
        return output

    def metadata_many(self, funds: list[dict]) -> dict[str, dict]:
        targets = [fund for fund in funds if re.fullmatch(r"\d{6}", str(fund.get("code") or ""))]
        output = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(6, max(1, len(targets))), thread_name_prefix="dual-fund-meta") as pool:
            future_map = {pool.submit(self.basic_metadata, str(fund["code"])): str(fund["code"]) for fund in targets}
            for future in concurrent.futures.as_completed(future_map):
                code = future_map[future]
                try: output[code] = future.result()
                except Exception: pass
        return output

    def cross_verify_top10(self, items: list[dict]) -> dict:
        rows = list(items[:10]); details = {}; verified = 0
        if self.source_degraded.get("secondary"):
            for item in rows:
                item["independent_source_verified"] = False
                item["independent_source"] = "新浪财经基金中心"
                item["independent_source_note"] = "新浪源契约检查已熔断，本轮不使用其交叉证据"
            return {"verified": 0, "requested": len(rows), "source": "新浪财经基金中心（已熔断）", "details": {}}
        secondary = self.secondary.latest_many([item["code"] for item in rows]) if rows else {"rows": {}}
        sec_rows = secondary.get("rows") or {}
        for item in rows:
            sec = sec_rows.get(item["code"])
            ok = False
            if sec:
                local_nav = _finite(item.get("display_nav", item.get("latest_nav")), float("nan")); snav = _finite(sec.get("nav"), float("nan"))
                ok = math.isfinite(local_nav) and math.isfinite(snav) and local_nav > 0 and abs(snav / local_nav - 1.0) <= 0.25
                sources = set(item.get("latest_sources") or []); sources.add("新浪财经"); item["latest_sources"] = sorted(sources)
                item["latest_public_confirmations"] = len(sources)
                signals = _public_availability_signals(item); item["availability_public_signals"] = sorted(signals)
                item["availability_public_confirmations"] = len(signals)
            item["independent_source_verified"] = ok
            item["independent_source"] = "新浪财经基金中心"
            item["independent_source_nav"] = sec.get("nav") if sec else None
            item["independent_source_note"] = "最新净值交叉证据一致" if ok else "新浪最新净值交叉证据不完整"
            details[item["code"]] = {"ok": ok, "source": "新浪财经基金中心", "sina_nav": sec.get("nav") if sec else None}
            verified += int(ok)
        return {"verified": verified, "requested": len(rows), "source": "新浪财经基金中心", "details": details}



# ===== 本地存储 =====

class LocalStore:
    def __init__(self):
        self.cache = self._load_cache()
        self.model = self._load_model()

    @staticmethod
    def _load_cache() -> dict:
        empty = {"version": CACHE_VERSION, "updated_at": None, "funds": {}, "fund_master": {}}
        try:
            connection = sqlite3.connect(CACHE_PATH, timeout=20)
            connection.row_factory = sqlite3.Row
            try:
                connection.execute("PRAGMA journal_mode=WAL")
                connection.execute("PRAGMA synchronous=NORMAL")
                connection.executescript(
                    """
                    CREATE TABLE IF NOT EXISTS runtime_state (
                        key TEXT PRIMARY KEY,
                        value_json TEXT NOT NULL
                    );
                    CREATE TABLE IF NOT EXISTS fund_master (
                        code TEXT PRIMARY KEY,
                        payload_json TEXT NOT NULL
                    );
                    CREATE TABLE IF NOT EXISTS nav_returns (
                        code TEXT NOT NULL,
                        nav_date TEXT NOT NULL,
                        daily_return REAL NOT NULL,
                        PRIMARY KEY (code, nav_date)
                    );
                    CREATE INDEX IF NOT EXISTS idx_nav_returns_code_date ON nav_returns(code, nav_date);
                    CREATE TABLE IF NOT EXISTS metadata (
                        code TEXT PRIMARY KEY,
                        payload_json TEXT NOT NULL
                    );
                    CREATE TABLE IF NOT EXISTS availability_history (
                        code TEXT NOT NULL,
                        span_from TEXT NOT NULL,
                        span_to TEXT NOT NULL DEFAULT '',
                        purchasable INTEGER NOT NULL,
                        payload_json TEXT NOT NULL,
                        PRIMARY KEY (code, span_from, span_to, purchasable)
                    );
                    """
                )
                state = {}
                for row in connection.execute("SELECT key, value_json FROM runtime_state"):
                    try:
                        state[row["key"]] = json.loads(row["value_json"])
                    except (TypeError, json.JSONDecodeError):
                        pass
                if state.get("version") not in (None, CACHE_VERSION):
                    return empty
                funds = {}
                for row in connection.execute("SELECT code, payload_json FROM metadata"):
                    try:
                        payload = json.loads(row["payload_json"])
                    except json.JSONDecodeError:
                        continue
                    funds[row["code"]] = payload if isinstance(payload, dict) else {}
                by_code = {}
                for row in connection.execute(
                    "SELECT code, nav_date, daily_return FROM nav_returns ORDER BY code, nav_date"
                ):
                    dates, returns = by_code.setdefault(row["code"], ([], []))
                    dates.append(row["nav_date"])
                    returns.append(float(row["daily_return"]))
                for code, (dates, returns) in by_code.items():
                    funds.setdefault(code, {})
                    funds[code]["dates"] = dates
                    funds[code]["returns"] = returns
                for row in connection.execute(
                    "SELECT code, payload_json FROM availability_history ORDER BY code, span_from, span_to"
                ):
                    try:
                        span = json.loads(row["payload_json"])
                    except json.JSONDecodeError:
                        continue
                    funds.setdefault(row["code"], {})
                    funds[row["code"]].setdefault("availability_history", []).append(span)
                master = {}
                for row in connection.execute("SELECT code, payload_json FROM fund_master"):
                    try:
                        payload = json.loads(row["payload_json"])
                    except json.JSONDecodeError:
                        continue
                    if isinstance(payload, dict):
                        master[row["code"]] = payload
                return {
                    "version": CACHE_VERSION,
                    "updated_at": state.get("updated_at"),
                    "funds": funds,
                    "fund_master": master,
                }
            finally:
                connection.close()
        except (OSError, sqlite3.Error, ValueError, TypeError):
            return empty


    @staticmethod
    def default_model() -> dict:
            return {
                "version": MODEL_VERSION,
                "trained_at": None,
                "feature_names": AdaptiveRanker.FEATURE_NAMES,
                "linear_weights": [0.0] * len(AdaptiveRanker.FEATURE_NAMES),
                "nonlinear_models": [],
                "asset_models": {},
                "asset_model_blend": {"global": GLOBAL_ASSET_BLEND, "asset_specific": ASSET_SPECIFIC_BLEND},
                "component_weights": {"expert": 1.0, "linear": 0.0, "nonlinear": 0.0, "external": 0.0, "tree2": 0.0},
                "optional_ml": None,
                "optional_tree2": None,
                "optional_ml_status": "not-trained",
                "optional_tree2_status": "not-trained",
                "validation_ic": 0.0,
                "model_quality": 0.0,
                "validation_metrics": {},
                "full_pipeline_oos": {},
                "untouched_test_oos": {},
                "candidate_deployment_oos": {},
                "expert_deployment_oos": {},
                "training_samples": 0,
                "tuning_samples": 0,
                "deployment_validation_samples": 0,
                "universe_size": 0,
                "historical_availability_coverage": 0.0,
                "historical_universe_known_coverage": 0.0,
                "historical_availability_used_for_model_selection": False,
                "ai_enabled": False,
                "model_status": "expert-fallback",
                "baseline_mode": "expert",
                "baseline_metrics": {},
                "split_boundaries": {},
                "universe_codes": [],
                "selection_dataset": "anchored development folds; untouched tail; production refit after freeze",
                "evaluation_model": {},
                "production_model": {},
                "survivorship_bias": True,
                "long_term_blend": 0.80,
                "target_spec": {},
                "engine": "anchored walk-forward long-horizon target search + LongTermQuality/EntryTiming + diversified Top10",
            }


    def _load_model(self) -> dict:
        model = _read_json(MODEL_PATH, self.default_model())
        if (
            model.get("version") != MODEL_VERSION
            or model.get("feature_names") != AdaptiveRanker.FEATURE_NAMES
            or len(model.get("linear_weights") or []) != len(AdaptiveRanker.FEATURE_NAMES)
        ):
            model = self.default_model()
        if not MODEL_PATH.exists():
            try:
                _write_json(MODEL_PATH, model)
            except OSError as exc:
                raise DataError(
                    f"无法在脚本目录创建 AI：{MODEL_PATH}\n"
                    f"请将程序解压到具有写权限的文件夹。\n{exc}"
                ) from exc
        return model

    def save_cache(self) -> None:
        try:
            connection = sqlite3.connect(CACHE_PATH, timeout=30)
            try:
                connection.execute("PRAGMA journal_mode=WAL")
                connection.execute("PRAGMA synchronous=NORMAL")
                connection.executescript(
                    """
                    CREATE TABLE IF NOT EXISTS runtime_state (key TEXT PRIMARY KEY, value_json TEXT NOT NULL);
                    CREATE TABLE IF NOT EXISTS fund_master (code TEXT PRIMARY KEY, payload_json TEXT NOT NULL);
                    CREATE TABLE IF NOT EXISTS nav_returns (
                        code TEXT NOT NULL, nav_date TEXT NOT NULL, daily_return REAL NOT NULL,
                        PRIMARY KEY (code, nav_date)
                    );
                    CREATE INDEX IF NOT EXISTS idx_nav_returns_code_date ON nav_returns(code, nav_date);
                    CREATE TABLE IF NOT EXISTS metadata (code TEXT PRIMARY KEY, payload_json TEXT NOT NULL);
                    CREATE TABLE IF NOT EXISTS availability_history (
                        code TEXT NOT NULL, span_from TEXT NOT NULL, span_to TEXT NOT NULL DEFAULT '',
                        purchasable INTEGER NOT NULL, payload_json TEXT NOT NULL,
                        PRIMARY KEY (code, span_from, span_to, purchasable)
                    );
                    """
                )
                last_dates = {
                    row[0]: row[1]
                    for row in connection.execute(
                        "SELECT code, MAX(nav_date) FROM nav_returns GROUP BY code"
                    )
                }
                with connection:
                    connection.executemany(
                        "INSERT INTO runtime_state(key,value_json) VALUES(?,?) "
                        "ON CONFLICT(key) DO UPDATE SET value_json=excluded.value_json",
                        [
                            ("version", json.dumps(CACHE_VERSION)),
                            ("updated_at", json.dumps(self.cache.get("updated_at"))),
                        ],
                    )
                    for code, item in (self.cache.get("funds") or {}).items():
                        if not isinstance(item, dict):
                            continue

                        dates = item.get("dates") or []
                        returns = item.get("returns") or []
                        if len(dates) == len(returns) and dates:
                            last_date = str(last_dates.get(code) or "")
                            start = bisect.bisect_right(dates, last_date) if last_date else 0
                            if start < len(dates):
                                connection.executemany(
                                    "INSERT OR IGNORE INTO nav_returns(code,nav_date,daily_return) VALUES(?,?,?)",
                                    [
                                        (code, str(day)[:10], float(ret))
                                        for day, ret in zip(dates[start:], returns[start:])
                                    ],
                                )

                        metadata = {
                            key: value
                            for key, value in item.items()
                            if key not in ("dates", "returns", "availability_history")
                        }
                        connection.execute(
                            "INSERT INTO metadata(code,payload_json) VALUES(?,?) "
                            "ON CONFLICT(code) DO UPDATE SET payload_json=excluded.payload_json",
                            (
                                code,
                                json.dumps(
                                    metadata,
                                    ensure_ascii=False,
                                    separators=(",", ":"),
                                ),
                            ),
                        )

                        for span in item.get("availability_history") or []:
                            if not isinstance(span, dict):
                                continue
                            start_date = str(span.get("from") or "")[:10]
                            finish_date = str(span.get("to") or "")[:10]
                            if not start_date:
                                continue
                            connection.execute(
                                "INSERT OR REPLACE INTO availability_history"
                                "(code,span_from,span_to,purchasable,payload_json) VALUES(?,?,?,?,?)",
                                (
                                    code,
                                    start_date,
                                    finish_date,
                                    1 if span.get("purchasable", True) is True else 0,
                                    json.dumps(
                                        span,
                                        ensure_ascii=False,
                                        separators=(",", ":"),
                                    ),
                                ),
                            )

                    for code, item in (self.cache.get("fund_master") or {}).items():
                        if isinstance(item, dict):
                            connection.execute(
                                "INSERT INTO fund_master(code,payload_json) VALUES(?,?) "
                                "ON CONFLICT(code) DO UPDATE SET payload_json=excluded.payload_json",
                                (
                                    code,
                                    json.dumps(
                                        item,
                                        ensure_ascii=False,
                                        separators=(",", ":"),
                                    ),
                                ),
                            )
            finally:
                connection.close()
        except (OSError, sqlite3.Error) as exc:
            raise DataError(
                f"无法在脚本目录写入 SQLite 缓存：{CACHE_PATH}\n{exc}"
            ) from exc



    def save_model(self, model: dict) -> None:
        try:
            _write_json(MODEL_PATH, model)
        except OSError as exc:
            raise DataError(f"无法在脚本目录写入 AI：{MODEL_PATH}\n{exc}") from exc
        self.model = model


# ===== 排名器 / AI =====

class AdaptiveRanker:
    FEATURE_NAMES = [
        "return_6m", "return_1y", "return_3y_ann", "sharpe_3y", "sortino_3y",
        "calmar_3y", "drawdown_quality", "volatility_quality", "worst_year",
        "positive_months", "trend_quality", "tail_quality", "stability_quality",
        "recovery_quality", "transaction_cost_3y_quality", "transaction_cost_5y_quality",
        "transaction_cost_10y_quality",
        "return_5y_ann", "return_7y_ann", "return_10y_ann", "drawdown_5y_quality",
        "rolling_3y_worst", "rolling_5y_worst", "recovery_time_quality", "ulcer_quality",
        "bear_stress_quality", "regime_stability_quality", "long_evidence_strength",
    ]
    EXPERT_WEIGHTS = [
        0.28, 0.42, 0.55, 0.68, 0.52, 0.58, 0.78, 0.40, 0.55,
        0.34, 0.22, 0.42, 0.46, 0.22, 0.24, 0.38, 0.34,
        0.95, 0.72, 0.52, 0.88, 0.74, 0.82, 0.48, 0.62, 0.55, 0.58, 0.70,
    ]
    NONLINEAR_SEEDS = (20260816, 27182818, 31415926)
    LIGHTGBM_DEV_GRID = (
        {"learning_rate":0.050,"num_leaves":7,"max_depth":3,"lambda_l1":0.05,"lambda_l2":0.8},
        {"learning_rate":0.035,"num_leaves":15,"max_depth":5,"lambda_l1":0.15,"lambda_l2":1.2},
        {"learning_rate":0.025,"num_leaves":31,"max_depth":5,"lambda_l1":0.30,"lambda_l2":2.0},
    )
    XGBOOST_DEV_GRID = (
        {"eta":0.050,"max_depth":3,"min_child_weight":3.0,"lambda":0.8,"alpha":0.05},
        {"eta":0.035,"max_depth":5,"min_child_weight":4.0,"lambda":1.2,"alpha":0.10},
        {"eta":0.025,"max_depth":5,"min_child_weight":6.0,"lambda":2.0,"alpha":0.20},
    )
    RANDOM_FEATURE_COUNT = 28
    _RANDOM_RECIPES = {}

    @staticmethod
    def features(
        returns: list[float], end: int | None = None, fees: dict | None = None,
        dates: list[str] | None = None,
    ) -> tuple[list[float], dict] | None:
        end = len(returns) if end is None else min(end, len(returns))
        if end < MIN_HISTORY_POINTS or not dates or len(dates) != len(returns):
            return None
        clean = [_clamp(_finite(value), -0.8, 2.0) for value in returns[:end]]
        date_values = [str(value)[:10] for value in dates[:end]]
        if any(not re.fullmatch(r"\d{4}-\d{2}-\d{2}", value) for value in date_values):
            return None
        try:
            history_start_day = _dt.date.fromisoformat(date_values[0])
            feature_day = _dt.date.fromisoformat(date_values[-1])
        except ValueError:
            return None
        long_n = min(756, len(clean) - 1)
        long_values = clean[-long_n:]
        ret_6m = _compound(clean[-min(126, len(clean)):])
        ret_1y = _compound(clean[-min(252, len(clean)):])
        total_long = _compound(long_values)
        years = max(long_n / 252.0, 0.25)
        ann = max(0.01, 1.0 + total_long) ** (1.0 / years) - 1.0
        daily_mean = sum(long_values) / len(long_values)
        daily_std = statistics.pstdev(long_values) if len(long_values) > 1 else 0.0
        volatility = daily_std * math.sqrt(252)
        risk_free = _risk_free_rate()
        sharpe = (daily_mean * 252 - risk_free) / max(volatility, 0.015)
        downside = math.sqrt(sum(min(0.0, r - risk_free / 252) ** 2 for r in long_values) / len(long_values)) * math.sqrt(252)
        sortino = (daily_mean * 252 - risk_free) / max(downside, 0.01)
        max_dd = _max_drawdown(long_values)
        calmar = (ann - risk_free) / max(abs(max_dd), 0.035)
        month_returns = []
        for start in range(max(0, len(long_values) - 504), len(long_values), 21):
            segment = long_values[start:min(start + 21, len(long_values))]
            if len(segment) >= 12:
                month_returns.append(_compound(segment))
        positive_months = sum(value > 0 for value in month_returns) / max(1, len(month_returns))
        rolling_year = []
        recent = long_values[-min(756, len(long_values)):]
        if len(recent) >= 252:
            for finish in range(252, len(recent) + 1, 21):
                rolling_year.append(_compound(recent[finish - 252:finish]))
        worst_year = min(rolling_year) if rolling_year else ret_1y
        rolling_quarter = []
        if len(recent) >= 63:
            for finish in range(63, len(recent) + 1, 21):
                rolling_quarter.append(_compound(recent[finish - 63:finish]))
        stability = -(statistics.pstdev(rolling_quarter) if len(rolling_quarter) > 1 else 0.0)
        trend_values = clean[-min(252, len(clean)):]
        logs, wealth = [], 1.0
        for value in trend_values:
            wealth *= max(0.01, 1.0 + value)
            logs.append(math.log(max(wealth, 1e-9)))
        n = len(logs); x_mean = (n - 1) / 2.0; y_mean = sum(logs) / n
        xx = sum((i - x_mean) ** 2 for i in range(n))
        xy = sum((i - x_mean) * (logs[i] - y_mean) for i in range(n))
        slope = xy / max(xx, 1e-12)
        fitted_var = sum((slope * (i - x_mean)) ** 2 for i in range(n))
        total_var = sum((value - y_mean) ** 2 for value in logs)
        r2 = _clamp(fitted_var / max(total_var, 1e-12), 0.0, 1.0)
        trend_quality = _clamp(slope * 252, -1.0, 1.5) * (0.35 + 0.65 * r2)
        sorted_returns = sorted(long_values); tail_count = max(5, int(len(sorted_returns) * 0.05))
        cvar = sum(sorted_returns[:tail_count]) / tail_count
        recent_year = clean[-min(252, len(clean)):]; wealth = peak = 1.0
        for value in recent_year:
            wealth *= max(0.01, 1.0 + value); peak = max(peak, wealth)
        recovery = wealth / peak - 1.0

        log_prefix = [0.0]
        for value in clean:
            log_prefix.append(log_prefix[-1] + math.log(max(0.01, 1.0 + value)))

        def compound_range(start: int, finish: int) -> float:
            return math.exp(log_prefix[finish] - log_prefix[start]) - 1.0

        def calendar_window(years: int) -> tuple[int, list[float], float, bool]:
            cutoff = _years_before(feature_day, years)
            start_index = bisect.bisect_left(date_values, cutoff.isoformat())
            if start_index >= len(clean) - 1:
                return start_index, [], 0.0, False
            try:
                actual_days = (feature_day - _dt.date.fromisoformat(date_values[start_index])).days
            except ValueError:
                return start_index, [], 0.0, False
            complete = actual_days >= 365 * years - 45
            return start_index, clean[start_index:], actual_days / 365.2425, complete

        def ann_window_years(years: int) -> float:
            start_index, values, actual_years, complete = calendar_window(years)
            if not values or not complete or actual_years <= 0:
                return 0.0
            total = compound_range(start_index, len(clean))
            return max(0.01, 1.0 + total) ** (1.0 / actual_years) - 1.0

        ret_5y_ann = ann_window_years(5)
        ret_7y_ann = ann_window_years(7)
        ret_10y_ann = ann_window_years(10)
        five_start, five_values, _five_years, _five_complete = calendar_window(5)
        max_dd_5y = _max_drawdown(five_values) if five_values else 0.0

        def worst_rolling_years(years: int) -> float:
            values = []
            for finish in range(MIN_HISTORY_POINTS, len(clean) + 1, 21):
                try:
                    finish_day = _dt.date.fromisoformat(date_values[finish - 1])
                except ValueError:
                    continue
                cutoff = _years_before(finish_day, years)
                start_index = bisect.bisect_left(date_values, cutoff.isoformat(), 0, finish)
                if start_index >= finish - 1:
                    continue
                try:
                    span = (finish_day - _dt.date.fromisoformat(date_values[start_index])).days
                except ValueError:
                    continue
                if span >= 365 * years - 45:
                    values.append(compound_range(start_index, finish))
            return min(values) if values else 0.0

        rolling_3y_worst = worst_rolling_years(3)
        rolling_5y_worst = worst_rolling_years(5)
        wealth = peak = 1.0; peak_index = 0; longest_recovery_days = 0; drawdowns = []
        for idx, value in enumerate(five_values):
            wealth *= max(0.01, 1.0 + value)
            if wealth >= peak:
                peak = wealth; peak_index = idx
            else:
                try:
                    recovery_days = (
                        _dt.date.fromisoformat(date_values[five_start + idx])
                        - _dt.date.fromisoformat(date_values[five_start + peak_index])
                    ).days
                except (ValueError, IndexError):
                    recovery_days = idx - peak_index
                longest_recovery_days = max(longest_recovery_days, recovery_days)
            drawdowns.append(wealth / max(peak, 1e-12) - 1.0)
        ulcer = math.sqrt(sum(dd*dd for dd in drawdowns) / max(1, len(drawdowns)))
        sorted_five = sorted(five_values)
        stress_n = max(5, int(len(sorted_five) * 0.05)) if sorted_five else 1
        bear_stress = abs(sum(sorted_five[:stress_n]) / stress_n) * math.sqrt(252) if sorted_five else 0.0
        annual_blocks = []
        for end_pos in range(252, len(five_values)+1, 252):
            annual_blocks.append(_compound(five_values[end_pos-252:end_pos]))
        regime_stability = -(statistics.pstdev(annual_blocks) if len(annual_blocks) > 1 else 0.0)
        history_years = max(0.0, (feature_day - history_start_day).days / 365.2425)
        long_evidence = _clamp((history_years - 3.0) / 7.0, 0.0, 1.0)
        costs = _holding_costs(fees)
        if fees is None:
            model_cost_3y, model_cost_5y, model_cost_10y = 0.20, 0.30, 0.45
        else:
            model_cost_3y, model_cost_5y, model_cost_10y = costs["transaction_cost_3y"], costs["transaction_cost_5y"], costs["transaction_cost_10y"]
        vector = [
            ret_6m, ret_1y, ann, _clamp(sharpe, -5, 8), _clamp(sortino, -5, 12), _clamp(calmar, -5, 10),
            max_dd, -volatility, worst_year, positive_months, trend_quality, -abs(cvar) * math.sqrt(252), stability,
            recovery, -model_cost_3y, -model_cost_5y, -model_cost_10y,
            ret_5y_ann, ret_7y_ann, ret_10y_ann, max_dd_5y,
            rolling_3y_worst, rolling_5y_worst, -longest_recovery_days / (5.0 * 365.2425), -ulcer,
            -bear_stress, regime_stability, long_evidence,
        ]
        sensitivity = {}
        for rf in (0.0, DEFAULT_RISK_FREE_RATE, 0.03):
            s = (daily_mean * 252 - rf) / max(volatility, 0.015)
            d = math.sqrt(sum(min(0.0, r - rf / 252) ** 2 for r in long_values) / len(long_values)) * math.sqrt(252)
            sensitivity[f"{rf:.3f}"] = {"sharpe": s, "sortino": (daily_mean * 252 - rf) / max(d, 0.01)}
        stats = {
            "return_6m": ret_6m, "return_1y": ret_1y, "return_3y_ann": ann, "volatility": volatility,
            "max_drawdown": max_dd, "sharpe": sharpe, "sortino": sortino, "calmar": calmar,
            "positive_months": positive_months, "worst_year": worst_year, "current_drawdown": recovery,
            "return_5y_ann": ret_5y_ann, "return_7y_ann": ret_7y_ann, "return_10y_ann": ret_10y_ann,
            "max_drawdown_5y": max_dd_5y, "rolling_3y_worst": rolling_3y_worst, "rolling_5y_worst": rolling_5y_worst,
            "recovery_days_5y": longest_recovery_days, "ulcer_index_5y": ulcer, "bear_stress_5y": bear_stress,
            "regime_stability_5y": regime_stability, "long_evidence_strength": long_evidence,
            "observations": end, "history_years": history_years, "feature_date": date_values[-1],
            "risk_free_rate": risk_free, "risk_free_sensitivity": sensitivity, **costs,
        }
        return vector, stats

    @staticmethod
    def _solve_ridge(xs: list[list[float]], ys: list[float], sample_weights: list[float], lam: float) -> list[float]:
        if not xs:
            return []
        columns = len(xs[0])
        matrix = [[0.0] * columns for _ in range(columns)]
        target = [0.0] * columns
        for row, y, weight in zip(xs, ys, sample_weights):
            for i in range(columns):
                target[i] += weight * row[i] * y
                for j in range(i, columns):
                    matrix[i][j] += weight * row[i] * row[j]
        for i in range(columns):
            matrix[i][i] += lam
            for j in range(i):
                matrix[i][j] = matrix[j][i]
        augmented = [matrix[i][:] + [target[i]] for i in range(columns)]
        for pivot in range(columns):
            best = max(range(pivot, columns), key=lambda row: abs(augmented[row][pivot]))
            augmented[pivot], augmented[best] = augmented[best], augmented[pivot]
            divisor = augmented[pivot][pivot]
            if abs(divisor) < 1e-12:
                continue
            for column in range(pivot, columns + 1):
                augmented[pivot][column] /= divisor
            for row in range(columns):
                if row == pivot:
                    continue
                factor = augmented[row][pivot]
                if abs(factor) < 1e-15:
                    continue
                for column in range(pivot, columns + 1):
                    augmented[row][column] -= factor * augmented[pivot][column]
        return [augmented[i][-1] for i in range(columns)]

    @classmethod
    def _random_features(cls, row: list[float], seed: int) -> list[float]:
        n = len(row)
        key = (seed, n, cls.RANDOM_FEATURE_COUNT)
        recipes = cls._RANDOM_RECIPES.get(key)
        if recipes is None:
            rng = random.Random(seed)
            recipes = tuple((rng.randrange(n), rng.randrange(n), rng.randrange(n), rng.randrange(5)) for _ in range(cls.RANDOM_FEATURE_COUNT))
            cls._RANDOM_RECIPES[key] = recipes
        result = []
        for a, b, c, mode in recipes:
            if mode == 0: value = row[a] * row[b]
            elif mode == 1: value = abs(row[a] - row[b])
            elif mode == 2: value = row[a] * row[a] * (1.0 if row[a] >= 0 else -1.0)
            elif mode == 3: value = max(row[a], 0.0) + min(row[b], 0.0)
            else: value = math.tanh(1.25 * row[a] - 0.75 * row[b] + 0.50 * row[c])
            result.append(_clamp(value, -2.0, 2.0))
        return result

    @staticmethod
    def _universe_membership_at(fund: dict, as_of_date: str) -> tuple[bool, bool]:
        date = str(as_of_date or "")[:10]
        inception = str(fund.get("inception_date") or "")[:10]
        termination = str(fund.get("termination_date") or "")[:10]
        if inception and date < inception:
            return False, True
        if termination and re.fullmatch(r"\d{4}-\d{2}-\d{2}", termination) and date > termination:
            return False, True
        history = [row for row in (fund.get("catalog_history") or []) if isinstance(row, dict)]
        if history:
            for span in history:
                start = str(span.get("from") or "0000-00-00")[:10]
                finish = str(span.get("to") or span.get("last_observed") or "9999-99-99")[:10]
                if start <= date <= finish:
                    return span.get("active") is not False, True
            # Before the first local observation (or in a gap) is deliberately unknown.
            return True, False
        # Inception proves the fund existed, but not that it belonged to the investable point-in-time universe.
        return True, False

    @staticmethod
    def _eligibility_at(fund: dict, end: int, as_of_date: str | None = None) -> tuple[bool, bool]:
        dates = fund.get("dates") or []
        if end <= 0 or end > len(dates):
            return False, False
        date = str(as_of_date or dates[end - 1])[:10]
        try:
            feature_day = _dt.date.fromisoformat(date)
            observation_day = _dt.date.fromisoformat(str(dates[end - 1])[:10])
        except ValueError:
            return False, False
        if observation_day > feature_day or (feature_day - observation_day).days > 31:
            return False, False
        inception = str(fund.get("inception_date") or dates[0])[:10]
        termination = str(fund.get("termination_date") or "")[:10]
        if inception and date < inception:
            return False, False
        if termination and re.fullmatch(r"\d{4}-\d{2}-\d{2}", termination) and date > termination:
            return False, False
        history = fund.get("availability_history") or []
        if history:
            for span in history:
                if not isinstance(span, dict):
                    continue
                start = str(span.get("from") or "0000-00-00")[:10]
                finish = str(span.get("to") or "9999-99-99")[:10]
                if start <= date <= finish:
                    return span.get("purchasable") is not False, True
            # 有历史记录但该日期不在任何覆盖区间：状态未知，而不是默认“已知可购”。
            return True, False
        return True, False

    @staticmethod
    def _eligible_at(fund: dict, end: int, as_of_date: str | None = None) -> bool:
        return AdaptiveRanker._eligibility_at(fund, end, as_of_date)[0]

    @staticmethod
    def _aggregate_underlyings(funds: list[dict]) -> list[dict]:
        groups: dict[str, list[dict]] = {}
        for fund in funds:
            groups.setdefault(_underlying_key(fund), []).append(fund)
        output = []
        for key, shares in groups.items():
            representative = max(
                shares,
                key=lambda fund: (
                    len(fund.get("returns") or []),
                    _share_preference(str(fund.get("name") or "")),
                    -int(str(fund.get("code") or "999999")) if str(fund.get("code") or "").isdigit() else 0,
                ),
            )
            clone = dict(representative)
            clone["underlying_fund_id"] = key
            clone["share_codes"] = sorted(str(row.get("code") or "") for row in shares)
            clone["share_count"] = len(shares)
            output.append(clone)
        output.sort(key=lambda fund: str(fund.get("code") or ""))
        return output

    @staticmethod
    def _quarterly_rebalance_dates(funds: list[dict], horizon_days: int = TARGET_THREE_YEAR_DAYS) -> list[str]:
        first_dates, last_dates = [], []
        for fund in funds:
            dates = fund.get("dates") or []
            if dates and re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(dates[0])[:10]) and re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(dates[-1])[:10]):
                first_dates.append(str(dates[0])[:10]); last_dates.append(str(dates[-1])[:10])
        if not first_dates or not last_dates:
            return []
        start = _dt.date.fromisoformat(min(first_dates))
        finish = _dt.date.fromisoformat(max(last_dates)) - _dt.timedelta(days=horizon_days)
        output = []
        for year in range(start.year, finish.year + 1):
            for month in (3, 6, 9, 12):
                day = _dt.date(year, month, calendar.monthrange(year, month)[1])
                while day.weekday() >= 5:
                    day -= _dt.timedelta(days=1)
                if start <= day <= finish:
                    output.append(day.isoformat())
        return output[-72:]

    def _build_snapshots(self, funds: list[dict], target_spec: dict | None = None) -> tuple[list[dict], dict]:
        spec = dict(target_spec or TARGET_SPECS[1])
        weights = dict(spec.get("weights") or {})
        horizon = str(spec.get("horizon") or "3y")
        horizon_days = TARGET_FIVE_YEAR_DAYS if horizon == "5y" else TARGET_THREE_YEAR_DAYS
        underlying_funds = self._aggregate_underlyings(funds)
        snapshots, feature_memo = [], {}
        availability_checks = availability_known = 0
        universe_checks = universe_known = 0
        for rebalance_date in self._quarterly_rebalance_dates(underlying_funds, horizon_days):
            day = _dt.date.fromisoformat(rebalance_date)
            endpoint_dates = {
                "6m": (day + _dt.timedelta(days=TARGET_HALF_YEAR_DAYS)).isoformat(),
                "1y": (day + _dt.timedelta(days=TARGET_ONE_YEAR_DAYS)).isoformat(),
                "3y": (day + _dt.timedelta(days=TARGET_THREE_YEAR_DAYS)).isoformat(),
                "5y": (day + _dt.timedelta(days=TARGET_FIVE_YEAR_DAYS)).isoformat(),
            }
            rows = []
            for fund in underlying_funds:
                returns = fund.get("returns") or []
                dates = fund.get("dates") or []
                if len(dates) != len(returns):
                    continue
                end = bisect.bisect_right(dates, rebalance_date)
                if end < MIN_HISTORY_POINTS:
                    continue
                endpoint_indices = {key: bisect.bisect_right(dates, value) for key, value in endpoint_dates.items()}
                required = set(weights)
                if any(endpoint_indices[key] <= end for key in required):
                    continue
                required_obs = {"6m":MIN_HALF_YEAR_OBSERVATIONS, "1y":MIN_ONE_YEAR_OBSERVATIONS,
                                "3y":MIN_THREE_YEAR_OBSERVATIONS, "5y":MIN_FIVE_YEAR_OBSERVATIONS}
                segments = {key: returns[end:endpoint_indices[key]] for key in required}
                if any(len(segments[key]) < required_obs[key] for key in required):
                    continue
                universe_checks += 1
                universe_eligible, universe_is_known = self._universe_membership_at(fund, rebalance_date)
                universe_known += int(universe_is_known)
                if not universe_eligible:
                    continue
                availability_checks += 1
                eligible, known = self._eligibility_at(fund, end, rebalance_date)
                availability_known += int(known)
                if not eligible:
                    continue
                _pit_product, pit_fees, pit_fees_verified = self._pit_fields(fund, rebalance_date)
                fee_fingerprint = json.dumps(pit_fees if pit_fees_verified else {}, sort_keys=True,
                                             ensure_ascii=True, separators=(",", ":"))
                memo_key = (fund["code"], end, fee_fingerprint)
                feature_result = feature_memo.get(memo_key)
                if feature_result is None:
                    feature_result = self.features(returns, end, pit_fees if pit_fees_verified else None, dates=dates)
                    feature_memo[memo_key] = feature_result
                if not feature_result:
                    continue
                utilities, drawdowns = {}, {}
                for key, values in segments.items():
                    years = {"6m":0.5,"1y":1.0,"3y":3.0,"5y":5.0}[key]
                    total = _compound(values)
                    ann = max(0.01, 1.0 + total) ** (1.0 / years) - 1.0
                    dd = abs(_max_drawdown(values))
                    vol = statistics.pstdev(values) * math.sqrt(252) if len(values) > 1 else 0.0
                    utilities[key] = ann - (0.42 + 0.05 * min(years, 5.0)) * dd - 0.08 * vol
                    drawdowns[key] = dd
                final_index = endpoint_indices[horizon]
                rows.append({
                    "code":fund["code"], "features":feature_result[0], "utilities":utilities,
                    "drawdown":drawdowns[horizon], "end":end, "future_end":endpoint_dates[horizon],
                    "observation_date":str(dates[end-1])[:10], "name":fund.get("name", ""),
                    "type":fund.get("type", ""), "underlying":fund.get("underlying_fund_id") or _underlying_key(fund),
                })
            if len(rows) < 24:
                continue
            component_ranks = {key:_rank_scale([row["utilities"][key] for row in rows]) for key in weights}
            combined = [sum(_finite(weight) * component_ranks[key][i] for key, weight in weights.items())
                        for i in range(len(rows))]
            raw_rows = [row["features"] for row in rows]
            buckets = [_asset_bucket(row["name"], row["type"]) for row in rows]
            snapshots.append({
                "rows": self._scale_feature_rows(raw_rows, buckets),
                "targets": _rank_scale(combined),
                "target_components": {key:component_ranks[key] for key in weights},
                "target_weights": weights,
                "target_spec": spec.get("name", horizon),
                "codes":[row["code"] for row in rows], "drawdowns":[row["drawdown"] for row in rows],
                "ends":[row["end"] for row in rows], "future_ends":[row["future_end"] for row in rows],
                "feature_observation_dates":[row["observation_date"] for row in rows],
                "underlying_keys":[row["underlying"] for row in rows],
                "buckets": buckets,
                "regime":self._regime_from_rows(raw_rows), "feature_date":rebalance_date,
                "target_end_date":endpoint_dates[horizon], "cross_section_synchronized":True,
            })
        snapshots.sort(key=lambda snap: snap["feature_date"])
        return snapshots, {
            "historical_availability_coverage":availability_known/max(1,availability_checks),
            "historical_universe_known_coverage":universe_known/max(1,universe_checks),
            "source_share_count":len(funds), "underlying_count":len(underlying_funds),
            "duplicate_shares_removed":max(0,len(funds)-len(underlying_funds)), "funds":underlying_funds,
            "target_spec":spec,
        }

    @staticmethod
    def _non_overlapping_tail(snapshots: list[dict], limit: int) -> list[dict]:
        chosen = []
        next_feature_start = ""
        for snap in reversed(snapshots):
            if not next_feature_start or str(snap.get("target_end_date") or "") <= next_feature_start:
                chosen.append(snap)
                next_feature_start = str(snap.get("feature_date") or "")
                if len(chosen) >= limit:
                    break
        return list(reversed(chosen))

    @staticmethod
    def _regime_from_rows(rows: list[list[float]]) -> str:
        if not rows:
            return "range"
        ret6 = _median([row[0] for row in rows])
        vol = _median([-row[7] for row in rows])
        trend = _median([row[10] for row in rows])
        if ret6 < -0.08 or (ret6 < 0 and vol > 0.24):
            return "risk_off"
        if vol > 0.28:
            return "high_vol"
        if ret6 > 0.12 and trend > 0.08:
            return "trend"
        if ret6 > 0.05:
            return "risk_on"
        return "range"

    @staticmethod
    def _scale_feature_rows(rows: list[list[float]], buckets: list[str]) -> list[list[float]]:
        if not rows:
            return []
        groups = {}
        for i, bucket in enumerate(buckets):
            groups.setdefault(bucket, []).append(i)
        global_columns = list(zip(*rows))
        global_scaled = [_rank_scale(list(column)) for column in global_columns]
        output = [[0.0] * len(rows[0]) for _ in rows]
        for indexes in groups.values():
            if len(indexes) < 4:
                for i in indexes:
                    output[i] = [global_scaled[j][i] for j in range(len(global_columns))]
                continue
            for j in range(len(global_columns)):
                scaled = _rank_scale([rows[i][j] for i in indexes])
                for local, i in enumerate(indexes):
                    output[i][j] = scaled[local]
        return output

    def _fit_hierarchical_linear(self, xs: list[list[float]], ys: list[float], weights: list[float], buckets: list[str]) -> tuple[list[float], dict]:
        global_weights = self._solve_ridge(xs, ys, weights, 0.9) if xs else [0.0] * len(self.FEATURE_NAMES)
        global_weights = self._normalized_linear_weights(global_weights)
        asset_models = {}
        for bucket in sorted(set(buckets)):
            indexes = [i for i, value in enumerate(buckets) if value == bucket]
            if len(indexes) < ASSET_MODEL_MIN_SAMPLES:
                continue
            bx = [xs[i] for i in indexes]; by = [ys[i] for i in indexes]; bw = [weights[i] for i in indexes]
            asset_models[bucket] = {
                "linear_weights": self._normalized_linear_weights(self._solve_ridge(bx, by, bw, 1.05)),
                "training_samples": len(indexes),
            }
        return global_weights, asset_models

    @staticmethod
    def _hierarchical_linear_predict(row: list[float], bucket: str, global_weights: list[float], asset_models: dict | None) -> float:
        global_value = sum(a*b for a,b in zip(global_weights or [], row))
        spec = (asset_models or {}).get(bucket) if isinstance(asset_models, dict) else None
        asset_weights = spec.get("linear_weights") if isinstance(spec, dict) else None
        if not asset_weights:
            return global_value
        asset_value = sum(a*b for a,b in zip(asset_weights, row))
        return GLOBAL_ASSET_BLEND * global_value + ASSET_SPECIFIC_BLEND * asset_value

    @staticmethod
    def _normalized_linear_weights(weights: list[float]) -> list[float]:
        scale = sum(abs(v) for v in weights) or 1.0
        return [_clamp(v/scale, -1.5, 1.5) for v in weights]

    @classmethod
    def _normalized_asset_models(cls, models: dict) -> dict:
        output = {}
        for bucket, spec in (models or {}).items():
            if not isinstance(spec, dict) or not spec.get("linear_weights"):
                continue
            output[bucket] = {
                **spec,
                "linear_weights": cls._normalized_linear_weights(list(spec.get("linear_weights") or [])),
            }
        return output

    @staticmethod
    def _history_snapshot(history, as_of_date: str, value_keys: tuple[str, ...]) -> dict:
        if not isinstance(history, list) or not as_of_date:
            return {}
        best_date, best = "", {}
        for row in history:
            if not isinstance(row, dict):
                continue
            date = str(row.get("feature_date") or row.get("effective_date") or row.get("date") or "")[:10]
            if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date) or date > as_of_date[:10] or date < best_date:
                continue
            value = None
            for key in value_keys:
                if isinstance(row.get(key), dict):
                    value = row.get(key); break
            if value is None and isinstance(row.get("values"), dict):
                value = row.get("values")
            if value is not None:
                best_date, best = date, dict(value)
        return best

    @classmethod
    def _pit_fields(cls, fund: dict, as_of_date: str) -> tuple[dict, dict, bool]:
        product = cls._history_snapshot(fund.get("product_features_history"), as_of_date, ("product_features", "features"))
        fees = cls._history_snapshot(fund.get("fees_history"), as_of_date, ("fees",))
                                                                                               
                                                                                         
        fee_verified = bool(fees)
        return product, fees, fee_verified

    @staticmethod
    def _product_quality(fund: dict, profile: str, as_of_date: str | None = None) -> float:
        f = fund.get("product_features") if isinstance(fund.get("product_features"), dict) else {}
        if not f:
            return 0.0
        bucket = _asset_bucket(fund.get("name", ""), fund.get("type", ""))
        score = 0.0
        inception = str(fund.get("inception_date") or "")[:10]
        age_years = float("nan")
        try:
            reference_day = _dt.date.fromisoformat(str(as_of_date)[:10]) if as_of_date else _china_today()
            inception_day = _dt.date.fromisoformat(inception)
            if inception_day <= reference_day:
                age_years = max(0.0, (reference_day - inception_day).days / 365.2425)
        except (ValueError, TypeError):
            pass
        if bucket in {"指数", "QDII/海外"}:
            te = _finite(f.get("tracking_error_annual"), float("nan"))
            size = _finite(f.get("fund_size_billion"), float("nan"))
            if math.isfinite(te): score += _clamp(0.03 - te, -0.04, 0.03)
            if math.isfinite(size): score += 0.012 * _clamp(math.log1p(max(0.0, size)) / 4.0, 0.0, 1.0)
            if math.isfinite(age_years): score += 0.008 * _clamp((age_years - 2.0) / 8.0, -0.5, 1.0)
        elif bucket == "主动权益":
            size = _finite(f.get("fund_size_billion"), float("nan"))
            tenure = _finite(f.get("manager_tenure_years"), float("nan"))
            changes = _finite(f.get("manager_changes_3y"), float("nan"))
            alpha = _finite(f.get("benchmark_alpha_3y"), float("nan"))
            drift = _finite(f.get("style_drift"), float("nan"))
            if math.isfinite(size): score += 0.006 * _clamp(math.log1p(max(0.0, size)) / 4.0, 0.0, 1.0)
            if math.isfinite(age_years): score += 0.006 * _clamp((age_years - 3.0) / 8.0, -0.5, 1.0)
            if math.isfinite(tenure): score += 0.012 * _clamp((tenure - 2.0) / 5.0, -1.0, 1.0)
            if math.isfinite(changes): score -= 0.010 * _clamp(changes / 3.0, 0.0, 1.5)
            if math.isfinite(alpha): score += 0.025 * _clamp(alpha / 0.10, -1.0, 1.0)
            if math.isfinite(drift): score -= 0.015 * _clamp(drift, 0.0, 1.0)
        elif bucket == "债券":
            size = _finite(f.get("fund_size_billion"), float("nan"))
            credit = _finite(f.get("credit_risk_score"), float("nan"))
            equity = _finite(f.get("equity_exposure"), float("nan"))
            if math.isfinite(size): score += 0.005 * _clamp(math.log1p(max(0.0, size)) / 4.0, 0.0, 1.0)
            if math.isfinite(age_years): score += 0.005 * _clamp((age_years - 2.0) / 8.0, -0.5, 1.0)
            if math.isfinite(credit): score -= 0.020 * _clamp(credit, 0.0, 1.0)
            if profile == "稳健" and math.isfinite(equity): score -= 0.020 * _clamp(equity / 0.20, 0.0, 1.0)
        return score

    _OPTIONAL_ML_LAST_STATUS = "not-attempted"
    _OPTIONAL_TREE2_LAST_STATUS = "not-attempted"

    @staticmethod
    def _ranking_labels(ys: list[float], group_sizes: list[int] | None, levels: int = 16):
        if not group_sizes or sum(int(v) for v in group_sizes) != len(ys) or any(int(v) < 2 for v in group_sizes):
            return None
        labels = []
        cursor = 0
        for size in group_sizes:
            size = int(size)
            segment = ys[cursor:cursor + size]
            scaled = _rank_scale(segment)
            labels.extend(int(round(_clamp(value, 0.0, 1.0) * (levels - 1))) for value in scaled)
            cursor += size
        return labels

    @classmethod
    def _ensure_lightgbm(cls):
        settings = _load_install_settings()
        if settings.get("lightgbm") is not True:
            cls._OPTIONAL_ML_LAST_STATUS = "disabled-by-install-profile"
            return None
        _activate_local_dependencies()
        try:
            import lightgbm as lgb
            module_path = Path(getattr(lgb, "__file__", "")).resolve()
            if DEPS_DIR not in module_path.parents:
                cls._OPTIONAL_ML_LAST_STATUS = "refused-nonlocal-lightgbm"
                return None
            cls._OPTIONAL_ML_LAST_STATUS = f"available-local:{getattr(lgb, '__version__', 'unknown')}"
            return lgb
        except Exception as exc:
            cls._OPTIONAL_ML_LAST_STATUS = f"unavailable-local:{type(exc).__name__}"
            return None

    @classmethod
    def _ensure_xgboost(cls):
        settings = _load_install_settings()
        if settings.get("advanced_tree") is not True:
            cls._OPTIONAL_TREE2_LAST_STATUS = "disabled-by-install-profile"
            return None
        _activate_local_dependencies()
        try:
            import xgboost as xgb
            module_path = Path(getattr(xgb, "__file__", "")).resolve()
            if DEPS_DIR not in module_path.parents:
                cls._OPTIONAL_TREE2_LAST_STATUS = "refused-nonlocal-xgboost"
                return None
            cls._OPTIONAL_TREE2_LAST_STATUS = f"available-local:{getattr(xgb, '__version__', 'unknown')}"
            return xgb
        except Exception as exc:
            cls._OPTIONAL_TREE2_LAST_STATUS = f"unavailable-local:{type(exc).__name__}"
            return None

    @classmethod
    def _train_optional_lightgbm(cls, xs: list[list[float]], ys: list[float], weights: list[float], group_sizes: list[int] | None = None, hyperparams: dict | None = None, num_boost_round: int = 110):
        lgb = cls._ensure_lightgbm()
        labels = cls._ranking_labels(ys, group_sizes)
        if lgb is None or len(xs) < 180 or labels is None:
            if lgb is not None:
                cls._OPTIONAL_ML_LAST_STATUS = f"insufficient-ranking-data:{len(xs)}"
            return None, None
        try:
            import numpy as np
            matrix = np.asarray(xs, dtype=float)
            sample_weights = np.asarray(weights, dtype=float) if weights else None
            dataset = lgb.Dataset(
                matrix, label=np.asarray(labels, dtype=int), weight=sample_weights,
                group=[int(value) for value in group_sizes], free_raw_data=True,
            )
            params = {
                "objective":"lambdarank", "metric":"ndcg", "ndcg_eval_at":[5,10],
                "label_gain":list(range(16)), "learning_rate":0.035,
                "num_leaves":15, "max_depth":5, "min_data_in_leaf":20,
                "feature_fraction":0.90, "bagging_fraction":0.90, "bagging_freq":1,
                "lambda_l1":0.15, "lambda_l2":1.2, "verbosity":-1,
                "seed":20260817, "feature_fraction_seed":20260817, "bagging_seed":20260817,
                "deterministic":True, "force_col_wise":True,
                "num_threads":max(1,min(4,os.cpu_count() or 2)),
            }
            if hyperparams:
                params.update({key:value for key,value in hyperparams.items() if key in {"learning_rate","num_leaves","max_depth","lambda_l1","lambda_l2"}})
            booster = lgb.train(params, dataset, num_boost_round=max(40, int(num_boost_round)))
            spec = {
                "backend":"lightgbm-lambdarank", "model_string":booster.model_to_string(),
                "params":params, "training_samples":len(xs), "groups":len(group_sizes),
                "ranking_label_levels":16, "weight_semantics":"query-group-mean-of-row-time-weights",
            }
            cls._OPTIONAL_ML_LAST_STATUS = f"trained-lambdarank:{len(xs)}:{len(group_sizes)}groups"
            return spec, (lambda row, b=booster, np=np: float(b.predict(np.asarray([row], dtype=float))[0]))
        except Exception as exc:
            cls._OPTIONAL_ML_LAST_STATUS = f"train-failed:{type(exc).__name__}"
            return None, None

    @classmethod
    def _train_optional_xgboost(cls, xs: list[list[float]], ys: list[float], weights: list[float], group_sizes: list[int] | None = None, hyperparams: dict | None = None, num_boost_round: int = 110):
        xgb = cls._ensure_xgboost()
        labels = cls._ranking_labels(ys, group_sizes)
        if xgb is None or len(xs) < 180 or labels is None:
            if xgb is not None:
                cls._OPTIONAL_TREE2_LAST_STATUS = f"insufficient-ranking-data:{len(xs)}"
            return None, None
        try:
            import numpy as np
            matrix = np.asarray(xs, dtype=float)
            dtrain = xgb.DMatrix(matrix, label=np.asarray(labels, dtype=float))
            normalized_groups = [int(value) for value in group_sizes]
            dtrain.set_group(normalized_groups)
            if weights and len(weights) == len(xs) and sum(normalized_groups) == len(xs):
                group_weights = []
                offset = 0
                for size in normalized_groups:
                    chunk = [_finite(value, 1.0) for value in weights[offset:offset + size]]
                    group_weights.append(max(1e-6, statistics.fmean(chunk) if chunk else 1.0))
                    offset += size
                # XGBoost learning-to-rank defines weights per query/group, not per row.
                dtrain.set_weight(np.asarray(group_weights, dtype=float))
            params = {
                "objective":"rank:ndcg", "eval_metric":"ndcg@10", "eta":0.035,
                "max_depth":5, "min_child_weight":4.0, "subsample":0.90,
                "colsample_bytree":0.90, "lambda":1.2, "alpha":0.10,
                "tree_method":"hist", "seed":20260817, "nthread":max(1,min(4,os.cpu_count() or 2)),
            }
            if hyperparams:
                params.update({key:value for key,value in hyperparams.items() if key in {"eta","max_depth","min_child_weight","lambda","alpha"}})
            booster = xgb.train(params, dtrain, num_boost_round=max(40, int(num_boost_round)), verbose_eval=False)
            raw = bytes(booster.save_raw(raw_format="ubj"))
            spec = {
                "backend":"xgboost-rank-ndcg", "model_b64":base64.b64encode(raw).decode("ascii"),
                "params":params, "training_samples":len(xs), "groups":len(group_sizes),
                "ranking_label_levels":16,
            }
            cls._OPTIONAL_TREE2_LAST_STATUS = f"trained-rank-ndcg:{len(xs)}:{len(group_sizes)}groups"
            return spec, (lambda row, b=booster, xgb=xgb, np=np: float(b.predict(xgb.DMatrix(np.asarray([row], dtype=float)))[0]))
        except Exception as exc:
            cls._OPTIONAL_TREE2_LAST_STATUS = f"train-failed:{type(exc).__name__}"
            return None, None

    @staticmethod
    def _optional_predictor(spec: dict | None):
        if not isinstance(spec, dict):
            return None
        backend = str(spec.get("backend") or "")
        settings = _load_install_settings()
        try:
            _activate_local_dependencies()
            if backend == "lightgbm-lambdarank" and spec.get("model_string") and settings.get("lightgbm") is True:
                import lightgbm as lgb
                import numpy as np
                module_path = Path(getattr(lgb, "__file__", "")).resolve()
                if DEPS_DIR not in module_path.parents:
                    return None
                booster = lgb.Booster(model_str=spec["model_string"])
                return lambda row, b=booster, np=np: float(b.predict(np.asarray([row], dtype=float))[0])
            if backend == "xgboost-rank-ndcg" and spec.get("model_b64") and settings.get("advanced_tree") is True:
                import xgboost as xgb
                import numpy as np
                module_path = Path(getattr(xgb, "__file__", "")).resolve()
                if DEPS_DIR not in module_path.parents:
                    return None
                booster = xgb.Booster()
                booster.load_model(bytearray(base64.b64decode(spec["model_b64"])))
                return lambda row, b=booster, xgb=xgb, np=np: float(b.predict(xgb.DMatrix(np.asarray([row], dtype=float)))[0])
        except Exception:
            return None
        return None

    def _validation_metrics(self, snapshots: list[dict], predict) -> dict:
        rank_ics, top_utils, draw_quality, regimes, top_sets = [], [], [], [], []
        for snap in snapshots:
            preds = [predict(row) for row in snap["rows"]]; targets = snap["targets"]
            rank_ics.append(_spearman(preds, targets))
            k = min(10, len(preds))
            if k <= 0: continue
            order = sorted(range(len(preds)), key=lambda i: preds[i], reverse=True)[:k]
            top_utils.append(sum(targets[i] for i in order) / k)
            dd_scaled = _rank_scale([-snap["drawdowns"][i] for i in range(len(preds))])
            draw_quality.append(sum(dd_scaled[i] for i in order) / k)
            top_sets.append({snap["codes"][i] for i in order}); regimes.append((snap["regime"], rank_ics[-1]))
        rank_ic = sum(rank_ics) / max(1, len(rank_ics)); top10_utility = sum(top_utils) / max(1, len(top_utils))
        drawdown_quality = sum(draw_quality) / max(1, len(draw_quality))
        turnover_values = [1.0 - len(a & b) / max(1, len(a | b)) for a,b in zip(top_sets, top_sets[1:])]
        turnover = sum(turnover_values) / len(turnover_values) if turnover_values else 0.0
        per_regime = {}
        for regime, value in regimes: per_regime.setdefault(regime, []).append(value)
        regime_means = [sum(vs)/len(vs) for vs in per_regime.values()]
        worst_regime = min(regime_means) if regime_means else 0.0
        dispersion = statistics.pstdev(rank_ics) if len(rank_ics) > 1 else 0.0
        stability = 0.5 * (rank_ic - dispersion) + 0.5 * worst_regime
        quality = 0.30*rank_ic + 0.25*top10_utility + 0.20*drawdown_quality + 0.15*stability - 0.10*turnover
        return {
            "rank_ic": rank_ic, "median_rank_ic": statistics.median(rank_ics) if rank_ics else 0.0,
            "positive_rank_ic_ratio": sum(v > 0 for v in rank_ics)/max(1,len(rank_ics)),
            "worst_rank_ic": min(rank_ics) if rank_ics else 0.0, "rank_ic_std": dispersion,
            "top10_utility": top10_utility, "drawdown_quality": drawdown_quality,
            "regime_stability": stability, "worst_regime_rank_ic": worst_regime,
            "turnover": turnover, "model_quality": quality, "windows": len(rank_ics),
        }


    def _ensemble_validation_metrics(self, snapshots: list[dict], predictors: dict, weights: dict) -> dict:
        rank_ics, top_utils, draw_quality, regimes, top_sets = [], [], [], [], []
        for snap in snapshots:
            component_predictions = {}
            for name, predictor in predictors.items():
                values = [predictor(row) for row in snap["rows"]]
                ranks = _rank_scale(values)
                component_predictions[name] = [2.0 * value - 1.0 for value in ranks]
            predictions = []
            for index in range(len(snap["rows"])):
                predictions.append(sum(
                    max(0.0, _finite(weights.get(name))) * values[index]
                    for name, values in component_predictions.items()
                ))
            targets = snap["targets"]
            rank_ics.append(_spearman(predictions, targets))
            k = min(10, len(predictions))
            if k <= 0:
                continue
            order = sorted(range(len(predictions)), key=lambda i: predictions[i], reverse=True)[:k]
            top_utils.append(sum(targets[i] for i in order) / k)
            dd_scaled = _rank_scale([-snap["drawdowns"][i] for i in range(len(predictions))])
            draw_quality.append(sum(dd_scaled[i] for i in order) / k)
            top_sets.append({snap["codes"][i] for i in order})
            regimes.append((snap["regime"], rank_ics[-1]))
        rank_ic = sum(rank_ics) / max(1, len(rank_ics))
        top10_utility = sum(top_utils) / max(1, len(top_utils))
        drawdown_quality = sum(draw_quality) / max(1, len(draw_quality))
        turnover_values = [
            1.0 - len(left & right) / max(1, len(left | right))
            for left, right in zip(top_sets, top_sets[1:])
        ]
        turnover = sum(turnover_values) / len(turnover_values) if turnover_values else 0.0
        per_regime = {}
        for regime, value in regimes:
            per_regime.setdefault(regime, []).append(value)
        regime_means = [sum(values) / len(values) for values in per_regime.values()]
        worst_regime = min(regime_means) if regime_means else 0.0
        dispersion = statistics.pstdev(rank_ics) if len(rank_ics) > 1 else 0.0
        stability = 0.5 * (rank_ic - dispersion) + 0.5 * worst_regime
        quality = (
            0.30*rank_ic + 0.25*top10_utility + 0.20*drawdown_quality
            + 0.15*stability - 0.10*turnover
        )
        return {
            "rank_ic": rank_ic,
            "median_rank_ic": statistics.median(rank_ics) if rank_ics else 0.0,
            "positive_rank_ic_ratio": sum(value > 0 for value in rank_ics) / max(1, len(rank_ics)),
            "worst_rank_ic": min(rank_ics) if rank_ics else 0.0,
            "rank_ic_std": dispersion,
            "top10_utility": top10_utility,
            "drawdown_quality": drawdown_quality,
            "regime_stability": stability,
            "worst_regime_rank_ic": worst_regime,
            "turnover": turnover,
            "model_quality": quality,
            "windows": len(rank_ics),
        }

    def train(self, funds: list[dict]) -> dict:
        """Anchored walk-forward selection. Untouched tail is never used to choose model family/ML."""
        expert_scale = sum(abs(v) for v in self.EXPERT_WEIGHTS) or 1.0
        expert_weights = [v/expert_scale for v in self.EXPERT_WEIGHTS]
        baseline_predictors = {
            "expert": lambda row: sum(a*b for a,b in zip(expert_weights,row)),
            "defensive": lambda row: 0.34*row[6]+0.28*row[7]+0.16*row[8]+0.12*row[12]+0.10*row[15],
            "low_volatility": lambda row: 0.34*row[7]+0.24*row[6]+0.16*row[20]+0.14*row[24]+0.12*row[27],
            "quality_momentum": lambda row: 0.24*row[17]+0.18*row[2]+0.14*row[3]+0.12*row[6]+0.12*row[10]+0.10*row[21]+0.10*row[27],
        }

        def flatten(group):
            xs,ys,ws,buckets,group_sizes=[],[],[],[],[]
            latest=max((snap["feature_date"] for snap in group),default="")
            latest_day=_dt.date.fromisoformat(latest) if latest else _china_today()
            for snap in group:
                try: age=max(0.0,(latest_day-_dt.date.fromisoformat(snap["feature_date"])).days/365.25)
                except ValueError: age=0.0
                w=math.exp(-0.08*age)
                xs.extend(snap["rows"]); ys.extend(snap["targets"]); ws.extend([w]*len(snap["rows"]))
                group_sizes.append(len(snap["rows"]))
                snap_buckets=list(snap.get("buckets") or [])
                if len(snap_buckets) != len(snap["rows"]): snap_buckets=["其他"]*len(snap["rows"])
                buckets.extend(snap_buckets)
            return xs,ys,ws,buckets,group_sizes

        def entry_values(rows):
            return [0.32*r[1]+0.28*r[10]+0.20*r[6]+0.12*r[7]+0.08*r[13]-0.10*max(0.0,r[0]-1.0) for r in rows]

        def one_metrics(preds, snap):
            targets=snap["targets"]
            ric=_spearman(preds,targets) if len(preds)>=3 else 0.0
            k=min(10,len(preds)); order=sorted(range(len(preds)),key=lambda i:preds[i],reverse=True)[:k]
            top=sum(targets[i] for i in order)/max(1,k)
            ddq=_rank_scale([-v for v in snap["drawdowns"]]); draw=sum(ddq[i] for i in order)/max(1,k)
            return ric,top,draw

        def aggregate(records):
            if not records: return {"windows":0,"rank_ic_mean":0.0,"rank_ic_median":0.0,"rank_ic_positive_ratio":0.0,"rank_ic_worst":0.0,"rank_ic_p25":0.0,"model_quality":-9.0}
            rics=[r[0] for r in records]; tops=[r[1] for r in records]; draws=[r[2] for r in records]
            sr=sorted(rics); p25=sr[max(0,int(0.25*(len(sr)-1)))]
            med=statistics.median(rics); mean=sum(rics)/len(rics); pos=sum(v>0 for v in rics)/len(rics); worst=min(rics)
            quality=0.32*med+0.18*p25+0.18*mean+0.14*(2*pos-1)+0.10*(sum(tops)/len(tops))+0.08*(sum(draws)/len(draws))
            return {"windows":len(rics),"rank_ic_mean":mean,"rank_ic_median":med,"rank_ic_positive_ratio":pos,
                    "rank_ic_worst":worst,"rank_ic_p25":p25,"top10_utility":sum(tops)/len(tops),
                    "drawdown_quality":sum(draws)/len(draws),"model_quality":quality}

        def eligible_folds(snaps):
            folds=[]
            for idx,snap in enumerate(snaps):
                prior=[s for s in snaps[:idx] if str(s.get("target_end_date") or "") <= str(snap.get("feature_date") or "")]
                samples=sum(len(s["rows"]) for s in prior)
                if len(prior)>=3 and samples>=120:
                    folds.append((prior,snap))
            return folds[::2][-10:]

        # Target/blend search uses development folds only.
        target_trials=[]; horizon_cache={}
        for horizon in {str(spec.get("horizon") or "3y") for spec in TARGET_SPECS}:
            base_spec=next(spec for spec in TARGET_SPECS if str(spec.get("horizon") or "3y")==horizon)
            horizon_cache[horizon]=self._build_snapshots(funds,base_spec)
        for spec in TARGET_SPECS:
            horizon=str(spec.get("horizon") or "3y")
            base_snaps,info=horizon_cache[horizon]; weights=dict(spec.get("weights") or {}); snaps=[]
            for base in base_snaps:
                components=base.get("target_components") or {}
                if any(key not in components for key in weights): continue
                combined=[sum(_finite(weight)*components[key][i] for key,weight in weights.items()) for i in range(len(base["rows"]))]
                snap=dict(base); snap["targets"]=_rank_scale(combined); snap["target_weights"]=weights; snap["target_spec"]=spec.get("name",horizon); snaps.append(snap)
            folds=eligible_folds(snaps)
            if len(folds)<MIN_OOS_GATE_WINDOWS: continue
            holdout=min(OOS_UNTOUCHED_TEST_WINDOWS,max(1,len(folds)-MIN_OOS_GATE_WINDOWS)); dev=folds[:-holdout]
            if len(dev)<MIN_OOS_GATE_WINDOWS: continue
            cached=[]
            for prior,snap in dev:
                xs,ys,ws,bks,groups=flatten(prior); gw,am=self._fit_hierarchical_linear(xs,ys,ws,bks)
                sb=snap.get("buckets") or ["其他"]*len(snap["rows"])
                long_pred=[self._hierarchical_linear_predict(row,bucket,gw,am) for row,bucket in zip(snap["rows"],sb)]
                cached.append((snap,[2*v-1 for v in _rank_scale(long_pred)],[2*v-1 for v in _rank_scale(entry_values(snap["rows"]))]))
            for blend in LONG_TERM_BLEND_CANDIDATES:
                records=[one_metrics([blend*l+(1-blend)*e for l,e in zip(lr,er)],snap) for snap,lr,er in cached]
                metrics=aggregate(records); target_trials.append((metrics["model_quality"],metrics["rank_ic_median"],metrics["rank_ic_p25"],spec,blend,snaps,info,folds,metrics))

        if not target_trials:
            model=LocalStore.default_model(); model.update({
                "trained_at":_now_iso(),"universe_size":len(funds),"universe_codes":sorted(str(f.get("code") or "") for f in funds),
                "model_status":"expert-fallback-insufficient-long-horizon-folds","baseline_mode":"expert",
                "target":"long-horizon target unavailable: expert fallback","target_selection":"OOS target search attempted",
                "survivorship_bias":True,"engine":"anchored walk-forward long-horizon target search + diversified Top10",
            }); return model

        _,_,_,selected_spec,long_blend,snapshots,snapshot_info,folds,target_cv=max(target_trials,key=lambda x:(x[0],x[1],x[2]))
        training_funds=snapshot_info["funds"]
        untouched_count=min(OOS_UNTOUCHED_TEST_WINDOWS,max(1,len(folds)-MIN_OOS_GATE_WINDOWS))
        untouched_folds=folds[-untouched_count:]; development_folds=folds[:-untouched_count]
        first_test_feature=min((snap["feature_date"] for _,snap in untouched_folds),default="")
        evaluation_training=[snap for snap in snapshots if first_test_feature and snap["target_end_date"]<=first_test_feature]
        if not evaluation_training:
            evaluation_training=[snap for snap in snapshots[:-untouched_count] if snap not in [f[1] for f in untouched_folds]]

        family_names=[*baseline_predictors.keys(),"linear","nonlinear","ensemble","lightgbm","ensemble_ml","xgboost","ensemble_xgb","ensemble_dual_tree"]
        family_records={name:[] for name in family_names}
        family_top_counts={name:{} for name in family_names}; family_eligible_counts={name:{} for name in family_names}
        def record_family(name, preds, snap):
            family_records[name].append(one_metrics(preds, snap))
            codes=list(snap.get("codes") or [])
            for code in codes:
                family_eligible_counts[name][code]=family_eligible_counts[name].get(code,0)+1
            k=min(10,len(preds)); order=sorted(range(len(preds)),key=lambda i:preds[i],reverse=True)[:k]
            for i in order:
                if i < len(codes):
                    code=codes[i]; family_top_counts[name][code]=family_top_counts[name].get(code,0)+1
        def tune_tree_params(prior, trainer, grid):
            # Inner validation is strictly earlier than the outer development snapshot; untouched folds are never seen here.
            if len(prior) < 5:
                return dict(grid[min(1, len(grid)-1)])
            inner_train = prior[:-2]; inner_valid = prior[-2:]
            ix,iy,iw,ib,ig = flatten(inner_train)
            if len(ix) < 180:
                return dict(grid[min(1, len(grid)-1)])
            trials=[]
            for params in grid:
                _spec,predict = trainer(ix,iy,iw,ig,hyperparams=dict(params),num_boost_round=70)
                if predict is None:
                    continue
                records=[]
                for valid_snap in inner_valid:
                    long_rank=[2*v-1 for v in _rank_scale([predict(row) for row in valid_snap["rows"]])]
                    entry_rank=[2*v-1 for v in _rank_scale(entry_values(valid_snap["rows"]))]
                    preds=[long_blend*l+(1-long_blend)*e for l,e in zip(long_rank,entry_rank)]
                    records.append(one_metrics(preds,valid_snap))
                metrics=aggregate(records)
                trials.append((metrics.get("model_quality",-9.0),metrics.get("rank_ic_median",-9.0),dict(params)))
            return max(trials,key=lambda row:(row[0],row[1]))[2] if trials else dict(grid[min(1, len(grid)-1)])

        lgb_param_votes={}; xgb_param_votes={}
        ml_dev_windows=0; tree2_dev_windows=0
        for prior,snap in development_folds:
            xs,ys,ws,bks,groups=flatten(prior); gw,asset_models=self._fit_hierarchical_linear(xs,ys,ws,bks)
            nonlinear=[]
            for seed in self.NONLINEAR_SEEDS:
                rx=[self._random_features(row,seed) for row in xs]; nonlinear.append((seed,self._solve_ridge(rx,ys,ws,1.2)))
            sb=snap.get("buckets") or ["其他"]*len(snap["rows"])
            component={name:[fn(row) for row in snap["rows"]] for name,fn in baseline_predictors.items()}
            component["linear"]=[self._hierarchical_linear_predict(row,bucket,gw,asset_models) for row,bucket in zip(snap["rows"],sb)]
            component["nonlinear"]=[sum(sum(a*b for a,b in zip(w,self._random_features(row,seed))) for seed,w in nonlinear)/len(nonlinear) for row in snap["rows"]]
            lgb_params=tune_tree_params(prior,self._train_optional_lightgbm,self.LIGHTGBM_DEV_GRID)
            xgb_params=tune_tree_params(prior,self._train_optional_xgboost,self.XGBOOST_DEV_GRID)
            lgb_key=json.dumps(lgb_params,sort_keys=True,separators=(",",":")); xgb_key=json.dumps(xgb_params,sort_keys=True,separators=(",",":"))
            lgb_param_votes[lgb_key]=lgb_param_votes.get(lgb_key,0)+1; xgb_param_votes[xgb_key]=xgb_param_votes.get(xgb_key,0)+1
            ml_spec,ml_predict=self._train_optional_lightgbm(xs,ys,ws,groups,hyperparams=lgb_params)
            tree2_spec,tree2_predict=self._train_optional_xgboost(xs,ys,ws,groups,hyperparams=xgb_params)
            if ml_predict is not None:
                component["lightgbm"]=[ml_predict(row) for row in snap["rows"]]; ml_dev_windows+=1
            if tree2_predict is not None:
                component["xgboost"]=[tree2_predict(row) for row in snap["rows"]]; tree2_dev_windows+=1
            entry_rank=[2*v-1 for v in _rank_scale(entry_values(snap["rows"]))]
            for name in list(baseline_predictors)+["linear","nonlinear"]:
                lr=[2*v-1 for v in _rank_scale(component[name])]; record_family(name, [long_blend*l+(1-long_blend)*e for l,e in zip(lr,entry_rank)], snap)
            er=[2*v-1 for v in _rank_scale(component["expert"])]; lr=[2*v-1 for v in _rank_scale(component["linear"])]; nr=[2*v-1 for v in _rank_scale(component["nonlinear"])]
            mix=[0.30*a+0.40*b+0.30*c for a,b,c in zip(er,lr,nr)]
            record_family("ensemble", [long_blend*l+(1-long_blend)*e for l,e in zip(mix,entry_rank)], snap)
            mr=xr=None
            if ml_predict is not None:
                mr=[2*v-1 for v in _rank_scale(component["lightgbm"])]
                record_family("lightgbm", [long_blend*l+(1-long_blend)*e for l,e in zip(mr,entry_rank)], snap)
                mix_ml=[0.22*a+0.28*b+0.20*c+0.30*d for a,b,c,d in zip(er,lr,nr,mr)]
                record_family("ensemble_ml", [long_blend*l+(1-long_blend)*e for l,e in zip(mix_ml,entry_rank)], snap)
            if tree2_predict is not None:
                xr=[2*v-1 for v in _rank_scale(component["xgboost"])]
                record_family("xgboost", [long_blend*l+(1-long_blend)*e for l,e in zip(xr,entry_rank)], snap)
                mix_xgb=[0.22*a+0.28*b+0.20*c+0.30*d for a,b,c,d in zip(er,lr,nr,xr)]
                record_family("ensemble_xgb", [long_blend*l+(1-long_blend)*e for l,e in zip(mix_xgb,entry_rank)], snap)
            if mr is not None and xr is not None:
                mix_dual=[0.18*a+0.24*b+0.18*c+0.22*d+0.18*e for a,b,c,d,e in zip(er,lr,nr,mr,xr)]
                record_family("ensemble_dual_tree", [long_blend*l+(1-long_blend)*e for l,e in zip(mix_dual,entry_rank)], snap)

        def voted_params(votes, grid):
            if not votes:
                return dict(grid[min(1, len(grid)-1)])
            key=max(votes,key=lambda k:(votes[k],k))
            return json.loads(key)
        frozen_lgb_params=voted_params(lgb_param_votes,self.LIGHTGBM_DEV_GRID)
        frozen_xgb_params=voted_params(xgb_param_votes,self.XGBOOST_DEV_GRID)
        family_metrics={name:aggregate(rows) for name,rows in family_records.items()}
        best_baseline=max(baseline_predictors,key=lambda n:family_metrics[n]["model_quality"])
        ai_candidates=[name for name in ("ensemble","ensemble_ml","lightgbm","ensemble_xgb","xgboost","ensemble_dual_tree") if family_metrics[name]["windows"]>=MIN_OOS_GATE_WINDOWS]
        best_ai=max(ai_candidates,key=lambda n:family_metrics[n]["model_quality"]) if ai_candidates else "ensemble"
        candidate=family_metrics[best_ai]; baseline=family_metrics[best_baseline]
        ai_enabled=bool(candidate["windows"]>=MIN_OOS_GATE_WINDOWS and candidate["rank_ic_median"]>0 and candidate["rank_ic_positive_ratio"]>=0.55
                        and candidate["rank_ic_worst"]>-0.45 and candidate["model_quality"]>baseline["model_quality"]
                        and candidate["rank_ic_median"]>=baseline["rank_ic_median"])
        selected_mode=best_ai if ai_enabled else best_baseline
        selected_top10_stability={}
        for code, eligible in family_eligible_counts.get(selected_mode, {}).items():
            selected_top10_stability[code] = family_top_counts.get(selected_mode, {}).get(code, 0) / max(1, eligible)
        use_ml=bool(ai_enabled and best_ai in {"ensemble_ml","lightgbm","ensemble_dual_tree"})
        use_tree2=bool(ai_enabled and best_ai in {"ensemble_xgb","xgboost","ensemble_dual_tree"})

        # Freeze model family here, before untouched evaluation. Fit only on labels matured before untouched start.
        eval_x,eval_y,eval_w,eval_b,eval_groups=flatten(evaluation_training)
        eval_linear,eval_assets=self._fit_hierarchical_linear(eval_x,eval_y,eval_w,eval_b) if eval_x else ([0.0]*len(self.FEATURE_NAMES),{})
        eval_linear=self._normalized_linear_weights(eval_linear); eval_assets=self._normalized_asset_models(eval_assets)
        eval_nonlinear=[]
        if eval_x:
            for seed in self.NONLINEAR_SEEDS:
                rx=[self._random_features(row,seed) for row in eval_x]; w=self._solve_ridge(rx,eval_y,eval_w,1.2)
                eval_nonlinear.append({"seed":seed,"lambda":1.2,"weights":self._normalized_linear_weights(w)})
        eval_ml,_=self._train_optional_lightgbm(eval_x,eval_y,eval_w,eval_groups,hyperparams=frozen_lgb_params) if use_ml else (None,None)
        eval_tree2,_=self._train_optional_xgboost(eval_x,eval_y,eval_w,eval_groups,hyperparams=frozen_xgb_params) if use_tree2 else (None,None)
        if selected_mode=="ensemble_dual_tree":
            if eval_ml is None and eval_tree2 is not None:
                use_ml=False; selected_mode="ensemble_xgb"
            elif eval_tree2 is None and eval_ml is not None:
                use_tree2=False; selected_mode="ensemble_ml"
            elif eval_ml is None and eval_tree2 is None:
                use_ml=False; use_tree2=False; selected_mode="ensemble" if ai_enabled else best_baseline
        elif selected_mode in {"lightgbm","ensemble_ml"} and eval_ml is None:
            use_ml=False; selected_mode="ensemble" if ai_enabled else best_baseline
        elif selected_mode in {"xgboost","ensemble_xgb"} and eval_tree2 is None:
            use_tree2=False; selected_mode="ensemble" if ai_enabled else best_baseline
        selected_top10_stability={code: family_top_counts.get(selected_mode,{}).get(code,0)/max(1,eligible) for code,eligible in family_eligible_counts.get(selected_mode,{}).items()}
        if selected_mode=="lightgbm": eval_components={"expert":0.0,"linear":0.0,"nonlinear":0.0,"external":1.0,"tree2":0.0}
        elif selected_mode=="xgboost": eval_components={"expert":0.0,"linear":0.0,"nonlinear":0.0,"external":0.0,"tree2":1.0}
        elif selected_mode=="ensemble_ml": eval_components={"expert":0.22,"linear":0.28,"nonlinear":0.20,"external":0.30,"tree2":0.0}
        elif selected_mode=="ensemble_xgb": eval_components={"expert":0.22,"linear":0.28,"nonlinear":0.20,"external":0.0,"tree2":0.30}
        elif selected_mode=="ensemble_dual_tree": eval_components={"expert":0.18,"linear":0.24,"nonlinear":0.18,"external":0.22,"tree2":0.18}
        elif selected_mode=="ensemble": eval_components={"expert":0.30,"linear":0.40,"nonlinear":0.30,"external":0.0,"tree2":0.0}
        else: eval_components={"expert":1.0,"linear":0.0,"nonlinear":0.0,"external":0.0,"tree2":0.0}
        evaluation_model={"linear_weights":eval_linear,"asset_models":eval_assets,"asset_model_blend":{"global":GLOBAL_ASSET_BLEND,"asset_specific":ASSET_SPECIFIC_BLEND},
                          "nonlinear_models":eval_nonlinear if ai_enabled else [],"optional_ml":eval_ml if use_ml else None,
                          "optional_tree2":eval_tree2 if use_tree2 else None,
                          "optional_ml_status":self._OPTIONAL_ML_LAST_STATUS,"optional_tree2_status":self._OPTIONAL_TREE2_LAST_STATUS,"component_weights":eval_components,
                          "baseline_mode":selected_mode,"long_term_blend":long_blend,"training_samples":len(eval_x),
                          "fit_dataset":"all labels matured before untouched-tail start; family frozen on development OOS"}
        untouched_snaps=[snap for _,snap in untouched_folds]
        full_oos=self._full_pipeline_oos(training_funds,untouched_snaps,evaluation_model,"均衡")

        # Untouched metrics are audit-only. Production refit happens only after the selection above is frozen.
        prod_x,prod_y,prod_w,prod_b,prod_groups=flatten(snapshots)
        prod_linear,prod_assets=self._fit_hierarchical_linear(prod_x,prod_y,prod_w,prod_b)
        prod_linear=self._normalized_linear_weights(prod_linear); prod_assets=self._normalized_asset_models(prod_assets)
        prod_nonlinear=[]
        for seed in self.NONLINEAR_SEEDS:
            rx=[self._random_features(row,seed) for row in prod_x]; w=self._solve_ridge(rx,prod_y,prod_w,1.2)
            prod_nonlinear.append({"seed":seed,"lambda":1.2,"weights":self._normalized_linear_weights(w)})
        prod_ml,_=self._train_optional_lightgbm(prod_x,prod_y,prod_w,prod_groups,hyperparams=frozen_lgb_params) if use_ml else (None,None)
        prod_tree2,_=self._train_optional_xgboost(prod_x,prod_y,prod_w,prod_groups,hyperparams=frozen_xgb_params) if use_tree2 else (None,None)
        production_use_ml=bool(use_ml and prod_ml is not None)
        production_use_tree2=bool(use_tree2 and prod_tree2 is not None)
        if selected_mode=="lightgbm" and production_use_ml: components={"expert":0.0,"linear":0.0,"nonlinear":0.0,"external":1.0,"tree2":0.0}
        elif selected_mode=="xgboost" and production_use_tree2: components={"expert":0.0,"linear":0.0,"nonlinear":0.0,"external":0.0,"tree2":1.0}
        elif selected_mode=="ensemble_ml" and production_use_ml: components={"expert":0.22,"linear":0.28,"nonlinear":0.20,"external":0.30,"tree2":0.0}
        elif selected_mode=="ensemble_xgb" and production_use_tree2: components={"expert":0.22,"linear":0.28,"nonlinear":0.20,"external":0.0,"tree2":0.30}
        elif selected_mode=="ensemble_dual_tree" and production_use_ml and production_use_tree2: components={"expert":0.18,"linear":0.24,"nonlinear":0.18,"external":0.22,"tree2":0.18}
        elif ai_enabled: components={"expert":0.30,"linear":0.40,"nonlinear":0.30,"external":0.0,"tree2":0.0}
        else: components={"expert":1.0,"linear":0.0,"nonlinear":0.0,"external":0.0,"tree2":0.0}
        production_model={"linear_weights":prod_linear,"asset_models":prod_assets,"asset_model_blend":{"global":GLOBAL_ASSET_BLEND,"asset_specific":ASSET_SPECIFIC_BLEND},
                          "nonlinear_models":prod_nonlinear if ai_enabled else [],"optional_ml":prod_ml if production_use_ml else None,
                          "optional_tree2":prod_tree2 if production_use_tree2 else None,
                          "optional_ml_status":self._OPTIONAL_ML_LAST_STATUS,"optional_tree2_status":self._OPTIONAL_TREE2_LAST_STATUS,"component_weights":components,"baseline_mode":selected_mode,
                          "long_term_blend":long_blend,"training_samples":len(prod_x),
                          "fit_dataset":"all matured long-horizon labels after development selection and untouched audit freeze"}
        split_boundaries={"walk_forward_folds":len(folds),"development_folds":len(development_folds),"untouched_test_folds":len(untouched_folds),
                          "test_feature_start":first_test_feature,"train_target_end_max":max((s["target_end_date"] for s in evaluation_training),default=""),
                          "target_horizon":selected_spec["horizon"],"target_weights":selected_spec["weights"],
                          "oos_windows_non_overlapping":False,"purge_rule":"each fold trains only on labels whose target_end <= fold feature_date",
                          "ml_selection_rule":"LightGBM/XGBoost hyperparameters use inner validation strictly inside development folds; majority-frozen params are then used for untouched audit and production refit"}
        return {
            "version":MODEL_VERSION,"trained_at":_now_iso(),"feature_names":self.FEATURE_NAMES,"linear_weights":prod_linear,"asset_models":prod_assets,
            "asset_model_blend":{"global":GLOBAL_ASSET_BLEND,"asset_specific":ASSET_SPECIFIC_BLEND},
            "ridge_lambda":0.9,"nonlinear_models":prod_nonlinear if ai_enabled else [],"optional_ml":prod_ml if production_use_ml else None,"optional_tree2":prod_tree2 if production_use_tree2 else None,
            "optional_ml_status":self._OPTIONAL_ML_LAST_STATUS,"optional_ml_development_windows":ml_dev_windows,"optional_tree2_status":self._OPTIONAL_TREE2_LAST_STATUS,"optional_tree2_development_windows":tree2_dev_windows,"component_weights":components,
            "lightgbm_frozen_dev_params":frozen_lgb_params,"xgboost_frozen_dev_params":frozen_xgb_params,
            "baseline_mode":selected_mode,"long_term_blend":long_blend,"evaluation_model":evaluation_model,"production_model":production_model,
            "validation_ic":full_oos.get("rank_ic_median",full_oos.get("rank_ic_mean",0.0)),"model_quality":full_oos.get("quality",0.0),
            "validation_metrics":full_oos,"full_pipeline_oos":full_oos,"untouched_test_oos":full_oos,
            "candidate_deployment_oos":candidate,"baseline_deployment_oos":baseline,"expert_deployment_oos":family_metrics.get("expert",{}),
            "baseline_metrics":{"walk_forward":family_metrics,"selected":best_baseline,"selected_ai_family":best_ai,"target_cv":target_cv},
            "training_samples":sum(len(s["rows"]) for s in evaluation_training),"tuning_samples":sum(len(f[1]["rows"]) for f in development_folds),
            "deployment_validation_samples":sum(len(f[1]["rows"]) for f in development_folds[-OOS_DEPLOYMENT_WINDOWS:]),
            "validation_samples":sum(len(s["rows"]) for s in untouched_snaps),"production_training_samples":len(prod_x),
            "universe_size":len(training_funds),"source_share_count":snapshot_info["source_share_count"],"duplicate_shares_removed":snapshot_info["duplicate_shares_removed"],
            "universe_codes":sorted(f["code"] for f in training_funds),"historical_availability_coverage":snapshot_info["historical_availability_coverage"],
            "historical_universe_known_coverage":snapshot_info.get("historical_universe_known_coverage",0.0),"historical_availability_used_for_model_selection":False,
            "ai_enabled":ai_enabled,"model_status":f"{selected_mode}-anchored-walk-forward" if ai_enabled else f"{best_baseline}-fallback-anchored-walk-forward",
            "split_boundaries":split_boundaries,"selection_dataset":"development folds choose target/model/ML; untouched tail audit only; production refit after freeze",
            "survivorship_bias":True,"historical_universe_mode":"point-in-time inception/termination + current stale histories + persistent inactive archive; pre-first-observation gaps remain possible",
            "target":f"OOS-selected {selected_spec['name']} weights={selected_spec['weights']} risk-adjusted forward utility",
            "target_spec":selected_spec,"target_selection":"selected by development anchored walk-forward median/p25/mean RankIC and win stability",
            "development_top10_stability_by_code":selected_top10_stability,
            "development_top10_stability_windows":len(development_folds),
            "engine":"anchored walk-forward; LightGBM LambdaRank + optional XGBoost rank:ndcg; global+asset-specific Ridge; PIT product quality; LongTermQualityScore + EntryTimingScore; diversified Top10",
        }


    @staticmethod
    def _market_regime(usable: list[dict]) -> str:
        ret6 = _median([item["stats"]["return_6m"] for item in usable])
        vol = _median([item["stats"]["volatility"] for item in usable])
        trends = _median([item["feature_vector"][10] for item in usable])
        if ret6 < -0.08 or (ret6 < 0 and vol > 0.24):
            return "risk_off"
        if vol > 0.28:
            return "high_vol"
        if ret6 > 0.12 and trends > 0.08:
            return "trend"
        if ret6 > 0.05:
            return "risk_on"
        return "range"

    @staticmethod
    def _choose_share_classes(funds: list[dict], holding_years: int) -> list[dict]:
        years = _expected_holding_years(holding_years)
        groups: dict[str, list[dict]] = {}
        for fund in funds:
            groups.setdefault(_underlying_key(fund), []).append(fund)
        chosen = []
        for underlying, shares in groups.items():
            def preference(fund: dict):
                verified = fund.get("fees_verified") is True
                cost = _share_class_cost(fund, years) if verified else float("inf")
                return (
                    0 if verified else 1,
                    cost,
                    -len(fund.get("returns") or []),
                    -_share_preference(str(fund.get("name") or "")),
                    str(fund.get("code") or ""),
                )
            selected = dict(min(shares, key=preference))
            selected["underlying_fund_id"] = underlying
            selected["selected_holding_years"] = years
            selected["selected_share_class_cost"] = (
                _share_class_cost(selected, years) if selected.get("fees_verified") is True else None
            )
            selected["alternative_share_codes"] = sorted(
                str(row.get("code") or "") for row in shares
                if str(row.get("code") or "") != str(selected.get("code") or "")
            )
            chosen.append(selected)
        return chosen

    def score(
        self, funds: list[dict], model: dict, profile: str,
        feature_cache: dict | None = None, as_of_date: str | None = None,
        holding_years: int | None = None,
    ) -> list[dict]:
        usable = []
        feature_cache = feature_cache if feature_cache is not None else {}
        years = _expected_holding_years(holding_years)
        for fund in self._choose_share_classes(funds, years):
            availability_status = str(
                fund.get("availability_status")
                or ("confirmed_purchasable" if fund.get("availability_declared") is True else "unknown")
            )
            if availability_status in PURCHASE_UNAVAILABLE_STATUSES:
                continue
            if (
                fund.get("availability_declared") is True
                and as_of_date is None
                and _age_seconds(fund.get("availability_declared_at")) > _availability_max_age_seconds()
            ):
                continue
            returns = fund.get("returns") or []
            fees = fund.get("fees") if fund.get("fees_verified") else None
            dates = fund.get("dates") or []
            fingerprint = (
                len(returns), fund.get("latest_date"), str(dates[-1]) if dates else "",
                round(_finite(returns[-1]) if returns else 0.0, 12),
                json.dumps(fees or {}, sort_keys=True, ensure_ascii=True, separators=(",", ":")),
            )
            cached = feature_cache.get(fund["code"])
            if cached and cached.get("fingerprint") == fingerprint:
                result = (cached["vector"], cached["stats"])
            else:
                result = self.features(returns, fees=fees, dates=dates)
                if result:
                    feature_cache[fund["code"]] = {
                        "fingerprint": fingerprint, "vector": result[0], "stats": result[1]
                    }
            if result:
                asset_class = _asset_bucket(fund.get("name", ""), fund.get("type", ""))
                usable.append({
                    **fund,
                    "feature_vector": result[0],
                    "stats": result[1],
                    "asset_class": asset_class,
                    "asset_bucket": asset_class,
                    "wrapper": _wrapper_type(fund.get("type", "")),
                })
        if len(usable) < 10:
            return []

        scaled_rows = self._scale_feature_rows(
            [item["feature_vector"] for item in usable],
            [item["asset_class"] for item in usable],
        )
        for item, scaled in zip(usable, scaled_rows):
            item["scaled"] = scaled

        regime = self._market_regime(usable)
        expert_weights = self.EXPERT_WEIGHTS[:]
        if profile == "稳健":
            expert_weights = [0.12,0.24,0.38,0.68,0.64,0.76,1.18,0.94,0.92,0.48,0.16,0.72,0.72,0.42,0.38,0.58,0.52,0.72,0.62,0.48,1.18,0.96,1.06,0.72,0.92,0.82,0.78,0.82]
        elif profile == "进取":
            expert_weights = [0.52,0.72,0.88,0.62,0.38,0.38,0.42,0.18,0.28,0.26,0.58,0.22,0.26,0.12,0.18,0.26,0.22,1.08,0.82,0.62,0.52,0.62,0.68,0.28,0.36,0.42,0.54,0.62]
        if regime == "risk_off":
            for idx in (6,7,8,11,12,13,15,16):
                expert_weights[idx] *= 1.25
            for idx in (0,1,2,10):
                expert_weights[idx] *= 0.75
        elif regime == "trend":
            for idx in (2,3,10):
                expert_weights[idx] *= 1.20
        elif regime == "high_vol":
            for idx in (6,7,11,12):
                expert_weights[idx] *= 1.20
        expert_scale = sum(abs(value) for value in expert_weights) or 1.0
        expert_weights = [value / expert_scale for value in expert_weights]

        linear_weights = model.get("linear_weights") or [0.0] * len(self.FEATURE_NAMES)
        asset_models = model.get("asset_models") if isinstance(model.get("asset_models"), dict) else {}
        nonlinear_models = model.get("nonlinear_models") or []
        optional_predict = self._optional_predictor(model.get("optional_ml"))
        tree2_predict = self._optional_predictor(model.get("optional_tree2"))
        components = dict(
            model.get("component_weights")
            or {"expert":1.0, "linear":0.0, "nonlinear":0.0, "external":0.0, "tree2":0.0}
        )
        if optional_predict is None:
            components["external"] = 0.0
        if tree2_predict is None:
            components["tree2"] = 0.0
        if regime == "risk_off":
            components["expert"] = components.get("expert", 0.0) * 1.20
            components["nonlinear"] = components.get("nonlinear", 0.0) * 0.90
        component_total = sum(max(0.0, value) for value in components.values()) or 1.0
        components = {key: max(0.0, value) / component_total for key, value in components.items()}

        raw_components = {"expert": [], "linear": [], "nonlinear": [], "external": [], "tree2": []}
        for item in usable:
            vector = item["scaled"]
            raw_components["expert"].append(sum(w*x for w, x in zip(expert_weights, vector)))
            raw_components["linear"].append(self._hierarchical_linear_predict(vector, item.get("asset_class", "其他"), linear_weights, asset_models))
            nonlinear_values = []
            for model_row in nonlinear_models:
                rf = self._random_features(vector, int(model_row.get("seed", 0)))
                nonlinear_values.append(
                    sum(w*x for w, x in zip(model_row.get("weights") or [], rf))
                )
            raw_components["nonlinear"].append(
                sum(nonlinear_values) / len(nonlinear_values) if nonlinear_values else 0.0
            )
            raw_components["external"].append(
                optional_predict(vector) if optional_predict is not None else 0.0
            )
            raw_components["tree2"].append(
                tree2_predict(vector) if tree2_predict is not None else 0.0
            )

        scaled_components = {}
        for key, values in raw_components.items():
            if (key == "external" and optional_predict is None) or (key == "tree2" and tree2_predict is None) or (key == "nonlinear" and not nonlinear_models):
                scaled_components[key] = [0.0] * len(values)
            else:
                ranks = _rank_scale(values)
                scaled_components[key] = [2.0 * value - 1.0 for value in ranks]

        baseline_mode = str(model.get("baseline_mode") or "ensemble")
        for index, item in enumerate(usable):
            vector = item["scaled"]
            if baseline_mode == "defensive":
                raw = 0.34*vector[6] + 0.28*vector[7] + 0.16*vector[8] + 0.12*vector[12] + 0.10*vector[15]
            elif baseline_mode == "low_volatility":
                raw = 0.34*vector[7] + 0.24*vector[6] + 0.16*vector[20] + 0.14*vector[24] + 0.12*vector[27]
            elif baseline_mode == "quality_momentum":
                raw = 0.24*vector[17] + 0.18*vector[2] + 0.14*vector[3] + 0.12*vector[6] + 0.12*vector[10] + 0.10*vector[21] + 0.10*vector[27]
            elif baseline_mode == "expert":
                raw = scaled_components["expert"][index]
            else:
                raw = sum(
                    components.get(key, 0.0) * scaled_components[key][index]
                    for key in scaled_components
                )

            long_raw = raw + self._product_quality(item, profile, as_of_date)
            if item["stats"]["return_6m"] > 0.50 and item["stats"]["volatility"] > 0.25:
                long_raw -= 0.03
            timing_raw = 0.31*vector[1] + 0.27*vector[10] + 0.19*vector[6] + 0.11*vector[7] + 0.07*vector[13]
            valuation_signal = _valuation_entry_signal(item) if as_of_date is None else 0.0
            timing_raw += 0.05 * valuation_signal
            item["ValuationTimingSignal"] = round(100.0 * valuation_signal, 1)
            if item["stats"]["return_6m"] > 0.45:
                timing_raw -= 0.18 * _clamp((item["stats"]["return_6m"]-0.45)/0.35,0.0,1.0)
            item["long_raw_score"] = long_raw
            item["entry_raw_score"] = timing_raw
            item["raw_score"] = long_raw
            item["market_regime"] = regime
            item["theme_label"] = _theme(item.get("name", ""))

            component_values = [
                scaled_components["expert"][index],
                scaled_components["linear"][index],
            ]
            if nonlinear_models:
                component_values.append(scaled_components["nonlinear"][index])
            if optional_predict is not None:
                component_values.append(scaled_components["external"][index])
            if tree2_predict is not None:
                component_values.append(scaled_components["tree2"][index])
            disagreement = statistics.pstdev(component_values) if len(component_values) > 1 else 0.0
            history_factor = (
                0.65 * min(1.0, _finite(item["stats"].get("history_years")) / 10.0)
                + 0.35 * _clamp(_finite(item["stats"].get("long_evidence_strength")), 0.0, 1.0)
            )
            evidence_factor, evidence_inputs = _model_evidence_factor(model, item)
            metadata_factor = 1.0 if item.get("fees_verified") is True else 0.92
            consistency = _clamp(
                0.58 + 0.32*history_factor - 0.35*disagreement, 0.25, 0.95
            )
            item["model_evidence_factor"] = round(100.0 * evidence_factor, 1)
            item["model_evidence_inputs"] = evidence_inputs
            item["model_consistency"] = round(
                100.0 * _clamp(consistency * evidence_factor * metadata_factor, 0.15, 0.95),
                0,
            )
            stability_map = model.get("development_top10_stability_by_code") or {}
            stability = _clamp(_finite(stability_map.get(str(item.get("code") or "")), 0.0), 0.0, 1.0)
            item["Top10SelectionStability"] = round(100.0 * stability, 1)

        long_ranks = _rank_scale([item["long_raw_score"] for item in usable])
        entry_ranks = _rank_scale([item["entry_raw_score"] for item in usable])
        blend = _clamp(_finite(model.get("long_term_blend"), 0.80), 0.65, 0.95)
        for item, long_pct, entry_pct in zip(usable, long_ranks, entry_ranks):
            item["LongTermQualityScore"] = round(100.0 * long_pct, 1)
            item["EntryTimingScore"] = round(100.0 * entry_pct, 1)
            item["long_term_quality_score"] = item["LongTermQualityScore"]
            item["entry_timing_score"] = item["EntryTimingScore"]
            item["score_blend"] = {"long_term":blend, "entry_timing":1.0-blend}
            item["raw_score"] = blend * (2.0*long_pct-1.0) + (1.0-blend) * (2.0*entry_pct-1.0)

        by_class = {}
        for item in usable:
            by_class.setdefault(item["asset_class"], []).append(item)
        for rows in by_class.values():
            percentiles = _rank_scale([row["raw_score"] for row in rows])
            for item, pct in zip(rows, percentiles):
                item["category_percentile"] = round(100.0 * pct, 0)

        overall = _rank_scale([item["raw_score"] for item in usable])
        for item, pct in zip(usable, overall):
            item["overall_percentile"] = round(100.0 * pct, 0)
            item["score"] = item["overall_percentile"]
            # Current purchasability/completeness affects today's Top10 only; historical OOS remains PIT/performance-only.
            if as_of_date is None:
                availability_confidence = _alipay_availability_confidence(item)
                integrity_score = _product_integrity_score(item)
                availability_adjustment = 0.78 + 0.22 * availability_confidence / 100.0
                integrity_adjustment = 0.90 + 0.10 * integrity_score / 100.0
            else:
                availability_confidence = 100
                integrity_score = 100.0
                availability_adjustment = 1.0
                integrity_adjustment = 1.0
            item["AlipayAvailabilityConfidence"] = availability_confidence
            item["product_integrity_score"] = round(integrity_score, 1)
            item["availability_adjustment"] = round(availability_adjustment, 4)
            item["product_integrity_adjustment"] = round(integrity_adjustment, 4)
            item["final_ranking_utility"] = (
                _finite(item["overall_percentile"], 50.0) / 100.0
                * availability_adjustment
                * integrity_adjustment
            )
            stats = item["stats"]
            qscore = _finite(item.get("LongTermQualityScore"))
            item["long_term_quality"] = "优秀" if qscore >= 85 else "良好" if qscore >= 65 else "一般" if qscore >= 40 else "偏弱"
            six_month = stats.get("return_6m", 0.0)
            tscore = _finite(item.get("EntryTimingScore"))
            item["timing_view"] = "偏热" if six_month > 0.45 and tscore < 70 else "积极" if tscore >= 70 else "偏弱" if tscore < 30 else "中性"
            if qscore >= 85 and tscore >= 55 and not (six_month > 0.45 and tscore < 70):
                item["absolute_buy_rating"] = "长期核心持有"
            elif qscore >= 70 and tscore >= 45:
                item["absolute_buy_rating"] = "值得分批买入"
            elif six_month > 0.45 or (qscore >= 55 and tscore < 30):
                item["absolute_buy_rating"] = "当前偏贵/偏热"
            elif qscore >= 55 and tscore >= 35:
                item["absolute_buy_rating"] = "可观察"
            else:
                item["absolute_buy_rating"] = "仅为相对Top10，不建议现在买入"
            if as_of_date is None:
                pit_cov = _clamp(_finite(model.get("historical_universe_known_coverage"), 0.0), 0.0, 1.0)
                pit_windows = int(_finite((model.get("full_pipeline_oos") or {}).get("windows"), 0))
                if pit_cov < PIT_RATING_MIN_UNIVERSE_COVERAGE or pit_windows < PIT_RATING_MIN_OOS_WINDOWS:
                    item["absolute_buy_rating"] = "值得关注（PIT/OOS证据积累中）"
                    item["pit_rating_capped"] = True
            item["risk"] = self._risk_label(item)
            item["reason"] = self._reason(item)

        usable.sort(
            key=lambda item: (item.get("final_ranking_utility", 0.0), item["model_consistency"], item["raw_score"]),
            reverse=True,
        )
        return usable


    @staticmethod
    def _return_correlation(left: dict, right: dict, lookback: int = 504) -> float:
        ld, lr = left.get("dates") or [], left.get("returns") or []; rd, rr = right.get("dates") or [], right.get("returns") or []
        if len(ld) != len(lr) or len(rd) != len(rr): return 0.0
        lmap=dict(zip(ld[-lookback:],lr[-lookback:])); rmap=dict(zip(rd[-lookback:],rr[-lookback:])); common=sorted(set(lmap)&set(rmap))
        if len(common) < 126: return 0.0
        return _clamp(_pearson([lmap[d] for d in common],[rmap[d] for d in common]),-1.0,1.0)

    def select_portfolio(self, scored: list[dict], profile: str) -> list[dict]:
        self.last_constraint_error = ""
        if not scored:
            return []
        correlation_lambda = {"稳健":0.24,"均衡":0.17,"进取":0.11}.get(profile,0.17)
        max_asset = {"稳健":5,"均衡":6,"进取":7}.get(profile,6)
        selected=[]; theme_counts={}; company_counts={}; asset_counts={}; used_underlying=set()
        pool=[dict(item, ai_raw_rank=i+1) for i,item in enumerate(scored)]

        def allowed(item, relaxed=False):
            underlying=_underlying_key(item)
            if underlying in used_underlying: return False
            theme=str(item.get("theme") or item.get("theme_label") or _theme(item.get("name", "")))
            company=str(item.get("fund_company") or "").strip()
            asset=str(item.get("asset_bucket") or item.get("asset_class") or "其他")
            specific_theme=theme not in ("", "宽基/全市场", "其他")
            if not relaxed and specific_theme and theme_counts.get(theme,0)>=2: return False
            if not relaxed and company and company_counts.get(company,0)>=2: return False
            if not relaxed and asset_counts.get(asset,0)>=max_asset: return False
            return True

        while len(selected)<10:
            candidates=[]
            for item in pool:
                if not allowed(item,False) or any(x["code"]==item["code"] for x in selected): continue
                max_corr=max((max(0.0,self._return_correlation(item,x)) for x in selected),default=0.0)
                base=_finite(item.get("final_ranking_utility"), _finite(item.get("overall_percentile"),50.0)/100.0)
                objective=base-correlation_lambda*max_corr
                candidates.append((objective,base,-max_corr,-int(item.get("ai_raw_rank",9999)),item,max_corr))
            if not candidates:
                break
            _,_,_,_,item,max_corr=max(candidates,key=lambda x:x[:4])
            item=dict(item); item["portfolio_max_correlation"]=max_corr
            item["portfolio_selection_score"]=_finite(item.get("final_ranking_utility"), _finite(item.get("overall_percentile"))/100.0)-correlation_lambda*max_corr
            selected.append(item); used_underlying.add(_underlying_key(item))
            theme=str(item.get("theme") or item.get("theme_label") or _theme(item.get("name", "")))
            company=str(item.get("fund_company") or "").strip(); asset=str(item.get("asset_bucket") or item.get("asset_class") or "其他")
            theme_counts[theme]=theme_counts.get(theme,0)+1
            if company: company_counts[company]=company_counts.get(company,0)+1
            asset_counts[asset]=asset_counts.get(asset,0)+1
        if len(selected)<10:
            for item in pool:
                if len(selected)>=10: break
                if not allowed(item,True) or any(x["code"]==item["code"] for x in selected): continue
                clone=dict(item); clone["portfolio_max_correlation"]=max((max(0.0,self._return_correlation(clone,x)) for x in selected),default=0.0)
                selected.append(clone); used_underlying.add(_underlying_key(clone))
        if len(selected)<10:
            self.last_constraint_error=f"组合约束后仅选出 {len(selected)} 只不同底层基金"
        for rank,item in enumerate(selected,1): item["ranking_rank"]=rank
        return selected[:10]



    @staticmethod
    def _fixed_weight_portfolio_path(paths: list[dict]) -> tuple[float, list[float]]:
        clean_paths = []
        for path in paths:
            dates, returns = path.get("dates") or [], path.get("returns") or []
            if len(dates) == len(returns) and dates:
                clean_paths.append(dict(zip(dates, returns)))
        if not clean_paths:
            return 0.0, []
        calendar_dates = sorted(set().union(*(set(path) for path in clean_paths)))
        wealth = [1.0] * len(clean_paths)
        previous_nav = 1.0
        portfolio_returns = []
        for day in calendar_dates:
            for index, path in enumerate(clean_paths):
                if day in path:
                    wealth[index] *= max(0.01, 1.0 + _clamp(_finite(path[day]), -0.95, 3.0))
            nav = sum(wealth) / len(wealth)
            portfolio_returns.append(nav / max(previous_nav, 1e-12) - 1.0)
            previous_nav = nav
        return previous_nav - 1.0, portfolio_returns

    def _full_pipeline_oos(self, funds: list[dict], snapshots: list[dict], model: dict, profile: str = "均衡") -> dict:
        fund_map={f["code"]:f for f in funds}; rank_ics=[]; regime_ics=[]; excess=[]; dds=[]; sortinos=[]; corrs=[]; top_sets=[]; constraint_failures=[]
        for snap in snapshots:
            hist=[]; forward={}; all_forward=[]
            for code,end,future_end in zip(snap.get("codes",[]),snap.get("ends",[]),snap.get("future_ends",[])):
                fund=fund_map.get(code);
                if not fund: continue
                dates=fund.get("dates") or []; returns=fund.get("returns") or []
                final_index=bisect.bisect_right(dates,str(future_end)[:10])
                fwd=returns[end:final_index]; fwd_dates=dates[end:final_index]
                if len(fwd)<MIN_ONE_YEAR_OBSERVATIONS: continue
                feature_date=str(snap.get("feature_date") or "")[:10]
                pit_product,pit_fees,pit_fees_verified=self._pit_fields(fund,feature_date)
                clone={**fund,"returns":list(returns[:end]),"dates":list(dates[:end]),
                       "latest_date":feature_date,"availability_declared":True,"availability_declared_at":feature_date,
                       "product_features":pit_product,"fees":pit_fees,"fees_verified":pit_fees_verified}
                                                                                                    
                clone.pop("display_nav",None); clone.pop("display_nav_date",None)
                hist.append(clone); forward[code]={"dates":fwd_dates,"returns":fwd}; all_forward.append(forward[code])
            scored=self.score(hist,model,profile,{},as_of_date=str(snap.get("feature_date") or ""))
            chosen=self.select_portfolio(scored,profile)
            chosen=[x for x in chosen if x["code"] in forward]
            if len(chosen) != 10:
                constraint_failures.append(self.last_constraint_error or f"{snap.get('feature_date')} 未选满10只")
                continue
            pred={x["code"]:x["raw_score"] for x in scored}; target_map={c:t for c,t in zip(snap["codes"],snap["targets"])}; common=[c for c in pred if c in target_map]
            rank_ics.append(_spearman([pred[c] for c in common],[target_map[c] for c in common]) if len(common)>=3 else 0.0)
            regime_ics.append((str(snap.get("regime") or "unknown"), rank_ics[-1]))
            top_sets.append({x["code"] for x in chosen}); selected=[forward[x["code"]] for x in chosen]
            top_return,portfolio_daily=self._fixed_weight_portfolio_path(selected)
            bench,_bench_daily=self._fixed_weight_portfolio_path(all_forward); excess.append(top_return-bench)
            dds.append(abs(_max_drawdown(portfolio_daily))); rf=_risk_free_rate()/252; downside=math.sqrt(sum(min(0.0,r-rf)**2 for r in portfolio_daily)/max(1,len(portfolio_daily)))*math.sqrt(252)
            sortinos.append((sum(portfolio_daily)/max(1,len(portfolio_daily))*252-_risk_free_rate())/max(downside,0.01))
            pair=[]
            for i in range(len(chosen)):
                for j in range(i+1,len(chosen)): pair.append(max(0.0,self._return_correlation(chosen[i],chosen[j])))
            corrs.append(sum(pair)/len(pair) if pair else 0.0)
        turnovers=[1.0-len(a&b)/max(1,len(a|b)) for a,b in zip(top_sets,top_sets[1:])]; mean=lambda xs: sum(xs)/max(1,len(xs))
        ric=mean(rank_ics); ex=mean(excess); win=sum(v>0 for v in excess)/max(1,len(excess)); dd=max(dds) if dds else 0.0; so=mean(sortinos); turn=mean(turnovers); corr=mean(corrs)
        by_regime={}
        for regime,value in regime_ics: by_regime.setdefault(regime,[]).append(value)
        worst_regime=min((mean(values) for values in by_regime.values()), default=0.0)
        median_ric=statistics.median(rank_ics) if rank_ics else 0.0
        sorted_ric=sorted(rank_ics); p25=sorted_ric[max(0,int(0.25*(len(sorted_ric)-1)))] if sorted_ric else 0.0
        quality=0.24*median_ric+0.14*p25+0.12*ric+0.22*ex+0.10*(2*win-1)+0.07*_clamp(so/3.0,-1,1)-0.06*dd-0.03*turn-0.06*corr
        non_overlapping=all(str(left.get("target_end_date") or "") <= str(right.get("feature_date") or "") for left,right in zip(snapshots,snapshots[1:]))
        return {"windows":len(rank_ics),"rank_ic_mean":ric,"rank_ic_median":median_ric,"rank_ic_p25":p25,"rank_ic_positive_ratio":sum(v>0 for v in rank_ics)/max(1,len(rank_ics)),"rank_ic_worst":min(rank_ics) if rank_ics else 0.0,"worst_regime_rank_ic":worst_regime,"top10_excess_return":ex,"oos_annual_excess_return":ex,"top10_benchmark_win_rate":win,"max_oos_drawdown":dd,"oos_sortino":so,"turnover":turn,"portfolio_correlation":corr,"quality":quality,"portfolio_assumption":"initial-equal-weight-buy-and-hold","windows_non_overlapping":non_overlapping,"fold_purge_rule":"training labels mature before each evaluation feature date","constraint_failures":constraint_failures}

    @staticmethod
    def _risk_label(item: dict) -> str:
        volatility = item["stats"]["volatility"]
        coarse = _coarse_type(item["type"])
        if coarse == "债券" and volatility < 0.07:
            return "中低"
        if volatility < 0.10:
            return "中"
        if volatility < 0.20:
            return "中高"
        return "高"

    @staticmethod
    def _reason(item: dict) -> str:
        stats = item["stats"]
        strengths = []
        if stats["sharpe"] >= 1.0:
            strengths.append("风险调整收益较强")
        if stats["max_drawdown"] > -0.16:
            strengths.append("长期回撤较低")
        cost_5y = stats.get("transaction_cost_5y")
        if cost_5y is not None and cost_5y <= 0.06 and item.get("fees_verified"):
            strengths.append("长期额外交易成本较低")
        if stats["positive_months"] >= 0.60:
            strengths.append("月度胜率较稳")
        if stats["return_3y_ann"] >= 0.10:
            strengths.append("三年复利靠前")
        if stats["current_drawdown"] < -0.16:
            strengths.append("当前仍在回撤")
        if stats["return_6m"] > 0.50:
            strengths.append("近期涨幅偏热")
        if not strengths:
            strengths.append("多周期综合均衡")
        return "；".join(strengths[:2])


# ===== 分析引擎 =====

class AnalysisEngine:
    def __init__(self, source=None, availability=None, store=None):
            self.source = source or FundDataSource()
            self.availability = availability or AlipayAvailabilitySource()
            self.store = store or LocalStore()
            self.ranker = AdaptiveRanker()
            self.funds: list[dict] = []
            self.market_funds: list[dict] = []
            self.feature_cache: dict[str, dict] = {}
            self.last_refresh_status = {}
            self.last_cross_check = {}
            self._cross_check_cache: dict[tuple[str,str], dict] = {}
            self.lock = threading.RLock()
            self._availability_cache = None
            self._availability_cache_at = 0.0
            self._last_full_nav_refresh_at = 0.0
            self.last_freshness_gate = {"ok": False, "reason": "尚未执行正式结果新鲜度门控"}

    def ensure_source_contract(self) -> dict:
            if hasattr(self.source, "startup_contract_test"):
                return self.source.startup_contract_test()
            return {"checked": False, "details": {}}


    def _availability_snapshot(self, force: bool = False) -> dict[str, dict]:
        now_mono = time.monotonic()
        if (
            not force
            and isinstance(self._availability_cache, dict)
            and now_mono - self._availability_cache_at < AVAILABILITY_REFRESH_SECONDS
        ):
            return {code: dict(row) for code, row in self._availability_cache.items()}
        try:
            snapshot = self.availability.snapshot()
            before = len(snapshot)
            if hasattr(self.source, "structural_prefilter"):
                snapshot = self.source.structural_prefilter(snapshot)
            self.last_availability_mode = "signed-alipay"
            self.last_availability_error = ""
            self.last_candidate_prefilter = {"before": before, "after": len(snapshot), "performance_blind": True}
        except DataError as exc:
            if not hasattr(self.source, "public_fallback_universe"):
                raise
            snapshot = self.source.public_fallback_universe()
            self.last_availability_mode = "public-fallback-alipay-unknown"
            self.last_availability_error = str(exc)
            self.last_candidate_prefilter = {"before": None, "after": len(snapshot), "performance_blind": True}
        self._availability_cache = {code: dict(row) for code, row in snapshot.items()}
        self._availability_cache_at = now_mono
        return snapshot


    def cache_age_hours(self) -> float:
        stamp = _parse_iso(self.store.cache.get("updated_at"))
        if stamp is None:
            return float("inf")
        if stamp.tzinfo is None:
            stamp = stamp.replace(tzinfo=_dt.datetime.now().astimezone().tzinfo)
        return max(0.0, (_dt.datetime.now().astimezone() - stamp).total_seconds() / 3600)

    def load_cached(self) -> bool:
        self.last_freshness_gate = {"ok": False, "reason": "本地缓存尚未完成本次启动的强制新鲜度复核"}
        availability = self._availability_snapshot()
        archive = (
            self.store.cache.get("funds", {})
            if isinstance(self.store.cache.get("funds", {}), dict)
            else {}
        )
        active = []
        market_cached = []

        for code, item in archive.items():
            if not isinstance(item, dict):
                continue
            returns, dates = item.get("returns") or [], item.get("dates") or []
            if (
                item.get("training_representative") is True
                and len(returns) >= MIN_HISTORY_POINTS
                and len(returns) == len(dates)
            ):
                market_cached.append({"code": code, **item})

        for code, item in archive.items():
            if not isinstance(item, dict) or item.get("ranking_candidate") is not True:
                continue
            if code not in availability:
                continue
            declared = availability[code]
            returns, dates = item.get("returns") or [], item.get("dates") or []
            if len(returns) < MIN_HISTORY_POINTS or len(returns) != len(dates):
                continue
            if not self._history_recent_enough(item, max_days=5):
                continue
            merged = {"code": code, **item}
            merged.update(self._availability_fields(declared))
            merged["availability_history"] = self._merge_observed_availability(
                declared, item
            )
            active.append(merged)

        with self.lock:
            self.funds = active
            self.market_funds = market_cached or active
            self.feature_cache.clear()
        return len({_underlying_key(item) for item in active}) >= 10


    @staticmethod
    def _history_fresh(item: dict) -> bool:
        stamp = _parse_iso(item.get("updated_at"))
        if stamp is None:
            return False
        if stamp.tzinfo is None:
            stamp = stamp.replace(tzinfo=_dt.datetime.now().astimezone().tzinfo)
        return (_dt.datetime.now().astimezone() - stamp).total_seconds() < 14 * 3600

    @staticmethod
    def _history_recent_enough(item: dict, max_days: int = 5) -> bool:
        try:
            latest = _dt.date.fromisoformat(str(item.get("latest_date") or "")[:10])
        except ValueError:
            return False
                                                                                                  
                                                                                                   
                                         
        return _expected_market_sessions(latest, _china_today()) <= max_days

    @staticmethod
    def _cache_item(item: dict) -> dict:
        keys = (
            "name","type","dates","returns","latest_nav","latest_date","updated_at","day_change",
            "availability_declared","availability_status","availability_note","fund_data_source",
            "availability_declared_at","availability_generated_at","availability_expires_at",
            "availability_sequence","availability_signature_alg","availability_source",
            "availability_source_id","availability_evidence","availability_schema_version",
            "fees_verified","fees","fees_history","fees_source","fee_schedule_complete",
            "fee_field_verified","annual_cost","embedded_annual_cost","purchase_cost",
            "transaction_cost_3y","transaction_cost_5y","transaction_cost_10y",
            "total_share_class_cost_3y","total_share_class_cost_5y","total_share_class_cost_10y",
            "holding_cost_3y","holding_cost_5y","holding_cost_10y","available_from","available_to",
            "availability_history","share_class","product_features","product_features_history",
            "benchmark","index_code","fund_company","fund_manager","theme","public_purchase_status","underlying_fund_id","master_code",
            "primary_code","inception_date","termination_date","merged_into","catalog_active",
            "catalog_first_seen","catalog_last_seen","metadata_source","metadata_checked_at",
            "display_nav","display_nav_date","return_pending_adjustment","return_basis",
            "return_provider_fallbacks","return_corporate_actions","return_accumulated_confirmations",
            "ranking_candidate","training_representative","representative_history_code",
            "share_specific_history","share_history_truncated_at_inception","return_basis","return_basis_label","catalog_history",
        )
        return {key: item.get(key) for key in keys}


    @staticmethod
    def _normalized_spans(history) -> list[dict]:
        out, seen = [], set()
        if not isinstance(history, list):
            return out
        for span in history:
            if not isinstance(span, dict):
                continue
            start = str(span.get("from") or "")[:10]
            finish = str(span.get("to") or "")[:10]
            if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", start):
                continue
            key = (start, finish, bool(span.get("purchasable", True)))
            if key in seen:
                continue
            seen.add(key)
            out.append({**span, "from": start, "to": finish, "purchasable": span.get("purchasable", True) is True})
        out.sort(key=lambda x: (x["from"], x.get("to") or "9999-99-99"))
        return out

    @classmethod
    def _merge_observed_availability(cls, declared: dict, cached: dict | None) -> list[dict]:
                                                                                                    
                                                                                                
        source_history = cls._normalized_spans(declared.get("availability_history"))
        cached_history = cls._normalized_spans((cached or {}).get("availability_history"))
        history = source_history or cached_history
        if declared.get("availability_declared") is not True:
            return history
        observed = str(declared.get("availability_generated_at") or declared.get("availability_declared_at") or "")[:10]
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", observed):
            return history
        for span in history:
            finish = span.get("to") or "9999-99-99"
            if span.get("purchasable") is True and span.get("from", "") <= observed <= finish:
                return history
        history.append({"from": observed, "to": "", "purchasable": True, "evidence": "observed-signed-manifest"})
        history.sort(key=lambda x: x.get("from", ""))
        return history

    @classmethod
    def _close_observed_availability(cls, cached: dict, observed: str) -> dict:
        result = dict(cached)
        history = cls._normalized_spans(result.get("availability_history"))
        if re.fullmatch(r"\d{4}-\d{2}-\d{2}", observed):
            try:
                previous_day = (_dt.date.fromisoformat(observed) - _dt.timedelta(days=1)).isoformat()
            except ValueError:
                previous_day = observed
            for span in reversed(history):
                if span.get("purchasable") is True and not span.get("to"):
                    if span.get("from", "") <= previous_day:
                        span["to"] = previous_day
                    else:
                        history.remove(span)
                    break
        result["availability_history"] = history
        result["availability_declared"] = False
        return result

    @staticmethod
    def _unknown_market_declaration(meta: dict) -> dict:
        return {
            "availability_declared": False, "availability_status": "unknown",
            "availability_declared_at": "", "availability_generated_at": _now_iso(),
            "availability_expires_at": "", "availability_sequence": 0,
            "availability_signature_alg": "", "availability_source": "东方财富公开基金全集（非支付宝）",
            "availability_source_id": "eastmoney-public-market",
            "availability_evidence": "仅用于全市场模型训练；支付宝状态未知",
            "availability_note": "支付宝可购状态未知（仅在今天的最终候选过滤阶段处理）",
            "availability_schema_version": 0, "fund_data_source": "东方财富基金公开清单/历史净值",
            "fees_verified": False, "fees": {}, "fees_history": [],
            "available_from": "", "available_to": "", "availability_history": [],
            "share_class": "", "product_features": {}, "product_features_history": [],
            "benchmark": "", "index_code": "", "fund_company": "", "theme": "",
            **_holding_costs({}),
        }

    @staticmethod
    def _retained_training_pool(current_market: list[dict], archive: dict) -> list[dict]:
        output = {str(item.get("code") or ""): item for item in current_market}
        for code, cached in (archive or {}).items():
            if code in output or not isinstance(cached, dict):
                continue
            if cached.get("training_representative") is not True and cached.get("catalog_active") is not False:
                continue
            dates, returns = cached.get("dates") or [], cached.get("returns") or []
            if len(returns) < MIN_HISTORY_POINTS or len(dates) != len(returns):
                continue
            output[code] = {"code": code, **cached, "catalog_active": False}
        return list(output.values())


    @staticmethod
    def _classify_public_purchase_status(status_text: str, termination_date: str = "") -> str:
        text = re.sub(r"\s+", "", str(status_text or ""))
        if termination_date or any(word in text for word in ("基金清盘", "清盘", "终止运作", "基金终止")):
            return "closed"
        # Must be checked before "暂停申购" because it contains that substring.
        if any(word in text for word in ("暂停大额申购", "限制大额申购", "大额申购上限", "限购")):
            return "limited_purchasable"
        if any(word in text for word in ("暂停申购", "终止申购")):
            return "purchase_suspended"
        if any(word in text for word in ("封闭期", "暂停交易")):
            return "closed"
        if "暂停赎回" in text:
            return "redemption_suspended"
        if any(word in text for word in ("开放申购", "可申购", "开放")):
            return "public_open"
        return "unknown"

    @staticmethod
    def _public_status_note(status: str) -> str:
        return {
            "limited_purchasable": "平台公开证据：仍可小额申购但存在限购；保留候选并轻度降权（非支付宝官方确认）",
            "purchase_suspended": "平台公开证据：暂停/终止申购；从当前买入候选中排除",
            "redemption_suspended": "平台公开证据：赎回受限；不等同于暂停申购，保留候选并提示退出限制",
            "closed": "平台公开证据：封闭/终止/清盘；从当前买入候选中排除",
            "public_open": "平台可购推测：公开渠道显示开放申购（非支付宝官方确认）",
            "unknown": "支付宝状态未知；公开证据不足，不冒充支付宝确认",
        }.get(status, "支付宝状态未知；公开证据不足")

    @staticmethod
    def _apply_share_history_semantics(item: dict) -> dict:
        """Never present representative history as independent A/C/I share-class history."""
        rep_code = str(item.get("representative_history_code") or item.get("code") or "")
        code = str(item.get("code") or "")
        dates = list(item.get("dates") or [])
        returns = list(item.get("returns") or [])
        if len(dates) != len(returns):
            return item
        inherited = bool(rep_code and code and rep_code != code)
        item["share_specific_history"] = not inherited
        item["return_basis"] = "underlying_fund_history" if inherited else "share_class_history"
        item["return_basis_label"] = "底层基金历史（非该份额独立历史）" if inherited else "该份额公开历史"
        inception = str(item.get("inception_date") or "")[:10]
        if inherited and re.fullmatch(r"\d{4}-\d{2}-\d{2}", inception) and dates:
            cut = bisect.bisect_left(dates, inception)
            if cut > 0 and cut < len(dates):
                item["dates"] = dates[cut:]
                item["returns"] = returns[cut:]
                item["share_history_truncated_at_inception"] = inception
        return item


    @staticmethod
    def _append_effective_history(item: dict, key: str, values: dict, effective_date: str) -> None:
        if not isinstance(values, dict) or not values or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(effective_date)[:10]):
            return
        history_key = f"{key}_history"
        history = [row for row in (item.get(history_key) or []) if isinstance(row, dict)]
        day = str(effective_date)[:10]
        payload = {"effective_date": day, key: dict(values)}
        history = [row for row in history if str(row.get("effective_date") or row.get("date") or "")[:10] != day]
        history.append(payload); history.sort(key=lambda row: str(row.get("effective_date") or row.get("date") or "")[:10])
        item[history_key] = history[-40:]

    def _enrich_structural_metadata(self, active: list[dict], model: dict, progress=lambda *_: None) -> None:
        if not active or not hasattr(self.source, "metadata_many"):
            model["public_metadata_coverage"] = 0.0
            return
        prelim = self.ranker.score(active, model, "均衡", {}, holding_years=5)
        selected_underlyings = {
            _underlying_key(item) for item in prelim[:METADATA_ENRICH_CANDIDATES]
        }
        targets = {
            item["code"] for item in active
            if _underlying_key(item) in selected_underlyings
        }
        lookup = {item["code"]: item for item in active}
        pending = []
        for code in sorted(targets):
            item = lookup.get(code)
            if not item:
                continue
            asset_class = _asset_bucket(item.get("name", ""), item.get("type", ""))
            metadata_complete = (
                bool(item.get("fund_company"))
                and (asset_class != "指数" or bool(item.get("index_code")))
                and bool(item.get("product_features"))
                and item.get("fees_verified") is True
            )
            if metadata_complete and _age_seconds(item.get("metadata_checked_at")) < 90 * 86400:
                continue
            pending.append(item)
        if pending:
            progress(
                f"补齐最终候选区 {len(pending)} 个具体份额的公司/指数/主题/完整费率",
                89,
            )
            metadata = self.source.metadata_many(pending)
            for code, values in metadata.items():
                item = lookup.get(code)
                if not item or not isinstance(values, dict):
                    continue
                for field in (
                    "fund_company", "benchmark", "index_code", "theme", "inception_date",
                    "termination_date", "public_purchase_status", "public_purchase_status_secondary", "fund_manager", "product_features", "metadata_source", "metadata_checked_at",
                    "availability_public_signals", "availability_public_confirmations", "metadata_sources",
                ):
                    if values.get(field):
                        item[field] = values[field]
                for field in (
                    "fees", "fees_verified", "fees_source", "fee_schedule_complete",
                    "fee_field_verified", "annual_cost", "embedded_annual_cost",
                    "purchase_cost", "transaction_cost_3y", "transaction_cost_5y", "transaction_cost_10y",
                    "total_share_class_cost_3y", "total_share_class_cost_5y", "total_share_class_cost_10y",
                    "holding_cost_3y", "holding_cost_5y", "holding_cost_10y",
                ):
                    if field in values:
                        item[field] = values[field]
                effective_date = str(values.get("metadata_checked_at") or _now_iso())[:10]
                features_now = dict(item.get("product_features") or {})
                try:
                    current_day = _dt.date.fromisoformat(effective_date)
                    cutoff = (current_day - _dt.timedelta(days=TARGET_THREE_YEAR_DAYS)).isoformat()
                except ValueError:
                    cutoff = ""
                historical_feature_rows = [row for row in (item.get("product_features_history") or []) if isinstance(row, dict)]
                dated_rows = []
                for row in historical_feature_rows:
                    day = str(row.get("effective_date") or row.get("date") or "")[:10]
                    vals = row.get("product_features") if isinstance(row.get("product_features"), dict) else {}
                    if cutoff and cutoff <= day < effective_date:
                        dated_rows.append((day, vals))
                earliest_known = min((str(row.get("effective_date") or row.get("date") or "")[:10] for row in historical_feature_rows), default="")
                if cutoff and earliest_known and earliest_known <= (current_day - _dt.timedelta(days=1000)).isoformat():
                    manager_sequence = [str(vals.get("manager_name") or "").strip() for _, vals in sorted(dated_rows)]
                    manager_sequence.append(str(features_now.get("manager_name") or "").strip())
                    manager_sequence = [name for name in manager_sequence if name]
                    if len(manager_sequence) >= 2:
                        changes = sum(a != b for a,b in zip(manager_sequence, manager_sequence[1:]))
                        features_now["manager_changes_3y"] = float(changes)
                    style_sequence = [str(vals.get("style_label") or "").strip() for _, vals in sorted(dated_rows)]
                    style_sequence.append(str(features_now.get("style_label") or "").strip())
                    style_sequence = [label for label in style_sequence if label]
                    if len(style_sequence) >= 2:
                        changes = sum(a != b for a,b in zip(style_sequence, style_sequence[1:]))
                        features_now["style_drift"] = changes / max(1, len(style_sequence)-1)
                item["product_features"] = features_now
                self._append_effective_history(item, "product_features", features_now, effective_date)
                if item.get("fees_verified") is True:
                    self._append_effective_history(item, "fees", item.get("fees") or {}, effective_date)
                status_text = str(item.get("public_purchase_status") or "")
                if item.get("availability_status") not in {"confirmed_purchasable", "closed"}:
                    classified = self._classify_public_purchase_status(status_text, str(item.get("termination_date") or ""))
                    item["availability_status"] = classified
                    signals = _public_availability_signals(item)
                    item["availability_public_signals"] = sorted(signals)
                    item["availability_public_confirmations"] = len(signals)
                    item["availability_note"] = self._public_status_note(classified)
                    self._apply_share_history_semantics(item)
        considered = [lookup[code] for code in targets if code in lookup]
        for item in considered:
            status_text = str(item.get("public_purchase_status") or "")
            if item.get("availability_status") not in {"confirmed_purchasable", "closed"}:
                classified = self._classify_public_purchase_status(status_text, str(item.get("termination_date") or ""))
                item["availability_status"] = classified
                signals = _public_availability_signals(item)
                item["availability_public_signals"] = sorted(signals)
                item["availability_public_confirmations"] = len(signals)
                item["availability_note"] = self._public_status_note(classified)
                self._apply_share_history_semantics(item)
        complete = sum(
            bool(item.get("fund_company"))
            and (
                _asset_bucket(item.get("name", ""), item.get("type", "")) != "指数"
                or bool(item.get("index_code"))
            )
            for item in considered
        )
        model["public_metadata_coverage"] = complete / max(1, len(considered))
        model["metadata_enriched_candidates"] = len(considered)


    @staticmethod
    def _observe_catalog_history(cached: dict, active: bool, observed: str) -> list[dict]:
        history = [dict(row) for row in (cached.get("catalog_history") or []) if isinstance(row, dict)]
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", observed):
            return history
        if history and history[-1].get("active") is active and not history[-1].get("to"):
            history[-1]["last_observed"] = observed
            return history[-80:]
        if history and not history[-1].get("to"):
            try:
                history[-1]["to"] = (_dt.date.fromisoformat(observed) - _dt.timedelta(days=1)).isoformat()
            except ValueError:
                history[-1]["to"] = observed
        history.append({"from": observed, "to": "", "last_observed": observed, "active": bool(active)})
        return history[-80:]

    def _persist_current(self) -> None:
        archive = dict(self.store.cache.get("funds", {}))
        current_codes = {item["code"] for item in self.funds}
        observed_dates = [
            str(
                item.get("availability_generated_at")
                or item.get("availability_declared_at")
                or ""
            )[:10]
            for item in self.funds
        ]
        observed_dates = [
            value
            for value in observed_dates
            if re.fullmatch(r"\d{4}-\d{2}-\d{2}", value)
        ]
        observed = max(observed_dates, default=_china_today().isoformat())
        signed_observation = any(
            item.get("availability_declared") is True for item in self.funds
        )

        for code, cached in list(archive.items()):
            if not isinstance(cached, dict):
                continue
            cached["ranking_candidate"] = False
            cached["training_representative"] = False
            if signed_observation and code not in current_codes:
                archive[code] = self._close_observed_availability(
                    cached, observed
                )

        for item in self.market_funds or []:
            cached = (
                archive.get(item["code"])
                if isinstance(archive.get(item["code"]), dict)
                else {}
            )
            merged = dict(item)
            merged["catalog_history"] = self._observe_catalog_history(cached, item.get("catalog_active") is not False, observed)
            merged["training_representative"] = True
            merged["ranking_candidate"] = False
            if signed_observation and item["code"] not in current_codes:
                closed = self._close_observed_availability(cached, observed)
                merged["availability_history"] = (
                    closed.get("availability_history") or []
                )
                merged["availability_declared"] = False
                merged["availability_status"] = "unknown"
            else:
                merged["availability_history"] = self._merge_observed_availability(
                    merged, cached
                )
            archive[item["code"]] = self._cache_item(merged)

        for item in self.funds:
            cached = (
                archive.get(item["code"])
                if isinstance(archive.get(item["code"]), dict)
                else {}
            )
            merged = dict(item)
            merged["catalog_history"] = self._observe_catalog_history(cached, item.get("catalog_active") is not False, observed)
            merged["ranking_candidate"] = True
            merged["training_representative"] = bool(
                cached.get("training_representative")
            )
            merged["availability_history"] = self._merge_observed_availability(
                merged, cached
            )
            archive[item["code"]] = self._cache_item(merged)

        master = dict(self.store.cache.get("fund_master", {}))
        for code, item in archive.items():
            if not isinstance(item, dict):
                continue
            previous = master.get(code) if isinstance(master.get(code), dict) else {}
            master[code] = {
                "code": code,
                "name": item.get("name"),
                "type": item.get("type"),
                "underlying_fund_id": (
                    item.get("underlying_fund_id")
                    or _underlying_key({"code": code, **item})
                ),
                "inception_date": (
                    item.get("inception_date")
                    or ((item.get("dates") or [""])[0])
                ),
                "termination_date": item.get("termination_date") or "",
                "merged_into": item.get("merged_into") or "",
                "catalog_first_seen": (
                    previous.get("catalog_first_seen")
                    or item.get("catalog_first_seen")
                    or _china_today().isoformat()
                ),
                "catalog_last_seen": (
                    item.get("catalog_last_seen")
                    or previous.get("catalog_last_seen")
                    or ""
                ),
                "catalog_active": item.get("catalog_active") is True,
            }

        self.store.cache = {
            "version": CACHE_VERSION,
            "updated_at": _now_iso(),
            "funds": archive,
            "fund_master": master,
        }
        self.store.save_cache()


    @staticmethod
    def _quick_start_representatives(representatives: list[dict], limit: int = QUICK_START_REPRESENTATIVES) -> list[dict]:
        """Performance-blind deterministic stratified sample for the first visible Top10."""
        if len(representatives) <= limit:
            return list(representatives)
        buckets = {}
        for item in representatives:
            buckets.setdefault(str(item.get("asset_class") or "其他"), []).append(item)
        for rows in buckets.values():
            rows.sort(key=lambda item: hashlib.sha256(str(item.get("code") or "").encode("utf-8")).hexdigest())
        labels = sorted(buckets)
        chosen = []
        cursor = 0
        while len(chosen) < limit and labels:
            label = labels[cursor % len(labels)]
            rows = buckets[label]
            if rows:
                chosen.append(rows.pop(0))
            if not rows:
                labels.remove(label)
                cursor = 0
            else:
                cursor += 1
        return chosen

    def rebuild(self, progress=lambda *_: None, force: bool = False, quick_callback=None, quick_profile: str = "均衡", quick_holding_years: int = 5) -> None:
        progress("读取支付宝可购证据；不可得时使用公开基金候选池并明确标注未知", 1)
        availability = self._availability_snapshot(force=True)
        progress("结构筛选并先聚合 A/C/I 等具体份额，不读取近期收益", 4)

        if getattr(self, "last_availability_mode", "") == "public-fallback-alipay-unknown":
            market_rows = [
                {
                    "code": code,
                    "name": row.get("name") or code,
                    "type": row.get("type") or "其他",
                }
                for code, row in availability.items()
            ]
        else:
            market_rows = self.source.all_funds()

        market = {item["code"]: item for item in market_rows}
        for code, declared in availability.items():
            market.setdefault(
                code,
                {
                    "code": code,
                    "name": declared.get("name") or code,
                    "type": declared.get("type") or "其他",
                },
            )

        existing = (
            self.store.cache.get("funds", {})
            if isinstance(self.store.cache.get("funds", {}), dict)
            else {}
        )
        today_text = _china_today().isoformat()
        structural_fields = (
            "benchmark", "index_code", "fund_company", "fund_manager", "theme", "underlying_fund_id",
            "master_code", "primary_code", "inception_date", "termination_date",
            "merged_into", "metadata_source", "metadata_checked_at", "product_features",
            "product_features_history", "fees_history",
        )
        all_candidates = []

        for code, meta in market.items():
            declared = availability.get(code)
            cached = existing.get(code) if isinstance(existing.get(code), dict) else {}
            name = (
                (declared or {}).get("name")
                or meta.get("name")
                or cached.get("name")
                or code
            )
            fund_type = (
                (declared or {}).get("type")
                or meta.get("type")
                or cached.get("type")
                or "其他"
            )
            if not _candidate_allowed(name, fund_type):
                continue
            cached_termination = str(cached.get("termination_date") or "")[:10]
            if re.fullmatch(r"\d{4}-\d{2}-\d{2}", cached_termination) and cached_termination <= today_text:
                continue
            cached_inception = str(cached.get("inception_date") or "")[:10]
            if re.fullmatch(r"\d{4}-\d{2}-\d{2}", cached_inception):
                try:
                    if (_china_today() - _dt.date.fromisoformat(cached_inception)).days < 1040:
                        continue
                except ValueError:
                    pass
            base = {
                **meta,
                **self._unknown_market_declaration(meta),
                "code": code,
                "name": name,
                "type": fund_type,
            }
            for field in structural_fields:
                if cached.get(field):
                    base[field] = cached[field]
            if declared:
                base.update(self._availability_fields(declared))
                base["name"], base["type"] = name, fund_type
                base["availability_history"] = self._merge_observed_availability(
                    declared, cached
                )
            else:
                base["availability_history"] = self._normalized_spans(
                    cached.get("availability_history")
                )
            base["catalog_active"] = True
            base["catalog_first_seen"] = cached.get("catalog_first_seen") or today_text
            base["catalog_last_seen"] = today_text
            base["asset_class"] = _asset_bucket(name, fund_type)
            base["wrapper"] = _wrapper_type(fund_type)
            all_candidates.append(base)

        if len(all_candidates) < 25:
            raise DataError(
                f"公开全市场中符合结构条件的具体份额仅 {len(all_candidates)} 个，样本不足"
            )

        groups = {}
        for item in all_candidates:
            group_key = (
                _base_name(item.get("name", "")).casefold(),
                item["asset_class"],
                item["wrapper"],
            )
            groups.setdefault(group_key, []).append(item)

        representatives = []
        shares_by_group = {}
        group_key_by_rep = {}
        for group_key, shares in groups.items():
            def rep_preference(item):
                cached = (
                    existing.get(item["code"])
                    if isinstance(existing.get(item["code"]), dict)
                    else {}
                )
                usable_cache = (
                    len(cached.get("returns") or []) >= MIN_HISTORY_POINTS
                    and len(cached.get("returns") or []) == len(cached.get("dates") or [])
                )
                return (
                    0 if usable_cache else 1,
                    -_share_preference(item.get("name", "")),
                    item["code"],
                )

            representative = min(shares, key=rep_preference)
            representatives.append(representative)
            shares_by_group[group_key] = shares
            group_key_by_rep[representative["code"]] = group_key

        representatives.sort(key=lambda item: item["code"])
        progress(
            f"结构阶段 {len(all_candidates)} 个具体份额已聚合为 "
            f"{len(representatives)} 个底层代表；开始历史增量",
            8,
        )

        completed, total, results, historical_results, failures = 0, len(representatives), [], [], []

        def checkpoint_history():
            if not historical_results:
                return
            cache_funds = dict(self.store.cache.get("funds", {}))
            for row in historical_results:
                merged = dict(cache_funds.get(row["code"]) or {})
                merged.update(row); merged["training_representative"] = True
                cache_funds[row["code"]] = self._cache_item(merged)
            self.store.cache["funds"] = cache_funds
            self.store.cache["version"] = CACHE_VERSION
            self.store.cache["updated_at"] = _now_iso()
            self.store.save_cache()

        def load_one(candidate):
            cached = existing.get(candidate["code"])
            cached_usable = (
                isinstance(cached, dict)
                and len(cached.get("returns") or []) >= MIN_HISTORY_POINTS
                and len(cached.get("returns") or []) == len(cached.get("dates") or [])
            )
            if cached_usable:
                history = (
                    self.source.update_history(candidate["code"], cached)
                    if hasattr(self.source, "update_history")
                    else {
                        "dates": cached["dates"],
                        "returns": cached["returns"],
                        "latest_nav": cached.get("latest_nav"),
                        "latest_date": cached.get("latest_date", ""),
                    }
                )
            else:
                history = self.source.history(candidate["code"])
            item = {**candidate, **history, "updated_at": _now_iso()}
            item["inception_date"] = item.get("inception_date") or ((item.get("dates") or [""])[0])
            item["underlying_fund_id"] = item.get("underlying_fund_id") or _underlying_key(item)
            return item

        initial_workers = min(6, max(2, os.cpu_count() or 4))

        def download_batch(batch: list[dict], phase_start: float, phase_span: float, label: str) -> None:
            nonlocal completed
            if not batch:
                return
            workers = initial_workers
            batch_done = 0
            cursor = 0
            while cursor < len(batch):
                wave_size = min(len(batch) - cursor, max(24, workers * 8))
                wave = batch[cursor:cursor + wave_size]
                cursor += wave_size
                wave_success = wave_fail = 0
                with concurrent.futures.ThreadPoolExecutor(max_workers=workers, thread_name_prefix="fund-data") as executor:
                    future_map = {executor.submit(load_one, candidate): candidate for candidate in wave}
                    for future in concurrent.futures.as_completed(future_map):
                        candidate = future_map[future]
                        completed += 1; batch_done += 1
                        try:
                            item = future.result()
                            if len(item.get("returns") or []) >= MIN_HISTORY_POINTS:
                                if self._history_recent_enough(item, max_days=5):
                                    historical_results.append(item); results.append(item); wave_success += 1
                                else:
                                    inactive = dict(item)
                                    inactive["catalog_active"] = False
                                    inactive["termination_date"] = inactive.get("termination_date") or str(inactive.get("latest_date") or "")[:10]
                                    inactive["ranking_candidate"] = False
                                    historical_results.append(inactive); wave_success += 1
                            else:
                                wave_fail += 1
                        except Exception as exc:
                            wave_fail += 1
                            failures.append((candidate["code"], str(exc)))
                        if completed % HISTORY_CHECKPOINT_BATCH == 0:
                            checkpoint_history()
                        progress(f"{label} {batch_done}/{len(batch)} · 全部 {completed}/{total} · 有效 {len(results)} · 并发{workers}", phase_start + phase_span * batch_done / max(1, len(batch)))
                ratio = wave_success / max(1, wave_success + wave_fail)
                if ratio >= 0.94 and workers < 12:
                    workers = min(12, workers + 2)
                elif ratio < 0.78 and workers > 2:
                    workers = max(2, workers // 2)
                checkpoint_history()

        quick_representatives = self._quick_start_representatives(representatives)
        quick_codes = {item["code"] for item in quick_representatives}
        remaining_representatives = [item for item in representatives if item["code"] not in quick_codes]
        download_batch(quick_representatives, 8, 25, "阶段1结构盲选历史")

        if callable(quick_callback) and len(results) >= 10:
            try:
                quick_model = self.store.model if self.store.model.get("version") == MODEL_VERSION else LocalStore.default_model()
                quick_scored = self.ranker.score(results, quick_model, quick_profile, {}, holding_years=quick_holding_years)
                quick_top = self.ranker.select_portfolio(quick_scored, quick_profile)
                if len(quick_top) >= 10:
                    for item in quick_top:
                        item["preliminary_phase1"] = True
                        item["absolute_buy_rating"] = "分析中/预览候选"
                        item["formal_result"] = False
                    quick_callback(quick_top[:10])
                    progress("首版 Top10 已显示；继续补齐全量历史、元数据与 OOS 排名训练", 34)
            except Exception:
                pass

        download_batch(remaining_representatives, 35, 31, "阶段2全量代表历史")

        if len(results) < 25:
            if self.load_cached():
                raise DataError("本次底层代表历史更新失败，已保留上次可用结果")
            raise DataError(
                f"有效历史数据仅 {len(results)} 个底层代表，无法可靠训练"
            )

        training_pool = self._retained_training_pool(historical_results or results, existing)
        retained_inactive = sum(
            item.get("catalog_active") is False for item in training_pool
        )
        current_model = self.store.model
        trained_at = _parse_iso(current_model.get("trained_at"))
        if trained_at is not None and trained_at.tzinfo is None:
            trained_at = trained_at.replace(
                tzinfo=_dt.datetime.now().astimezone().tzinfo
            )
        model_age_days = (
            float("inf")
            if trained_at is None
            else max(
                0.0,
                (
                    _dt.datetime.now().astimezone() - trained_at
                ).total_seconds() / 86400.0,
            )
        )
        old_codes = set(current_model.get("universe_codes") or [])
        new_codes = {item["code"] for item in training_pool}
        change_ratio = (
            len(old_codes ^ new_codes) / max(1, len(old_codes | new_codes))
            if old_codes
            else 1.0
        )
        auto_update_model = _model_auto_update_enabled()
        should_retrain = (
            force
            or trained_at is None
            or current_model.get("version") != MODEL_VERSION
            or (auto_update_model and (model_age_days >= MODEL_RETRAIN_DAYS or change_ratio >= 0.05))
        )
        if should_retrain:
            progress(
                "anchored walk-forward 选择长期目标/模型；随后用全部已成熟长期标签重训 production_model",
                69,
            )
            model = self.ranker.train(training_pool)
        else:
            progress(
                f"历史已增量刷新；AI 年龄 {model_age_days:.1f} 天，"
                f"底层池变化 {change_ratio:.1%}，本轮不重训",
                80,
            )
            model = current_model

        model["full_market_scanned_shares"] = len(all_candidates)
        model["representative_history_downloads"] = len(representatives)
        model["quick_start_representatives"] = len(quick_representatives)
        model["auto_update_model"] = auto_update_model
        model["retained_inactive_funds"] = retained_inactive
        model["survivorship_bias"] = True
        model["survivorship_mitigation"] = "point-in-time inception/termination + stale histories + persistent inactive archive"
        model["survivorship_note"] = (
            f"已纳入 {retained_inactive} 个历史退出/非活动底层样本并按历史日期做 universe 过滤；"
            "若公开基金目录未覆盖首次运行前已经彻底消失的基金，仍保留剩余存续偏差告警。"
        )

        prelim = self.ranker.score(
            results, model, "均衡", {}, holding_years=5
        )
        finalist_rep_codes = {
            item["code"] for item in prelim[:METADATA_ENRICH_CANDIDATES]
        }

        expanded = []
        for representative in results:
            if representative["code"] not in finalist_rep_codes:
                continue
            group_key = group_key_by_rep.get(representative["code"])
            shares = shares_by_group.get(group_key, [representative])
            underlying_id = _underlying_key(representative)
            for share in shares:
                cached = (
                    existing.get(share["code"])
                    if isinstance(existing.get(share["code"]), dict)
                    else {}
                )
                item = {
                    **share,
                    "dates": list(representative.get("dates") or []),
                    "returns": list(representative.get("returns") or []),
                    "latest_nav": representative.get("latest_nav"),
                    "latest_date": representative.get("latest_date"),
                    "updated_at": representative.get("updated_at"),
                    "underlying_fund_id": underlying_id,
                    "representative_history_code": representative["code"],
                }
                for field in (
                    "fees", "fees_verified", "fees_source", "fee_schedule_complete",
                    "fee_field_verified", "annual_cost", "embedded_annual_cost",
                    "purchase_cost", "transaction_cost_3y", "transaction_cost_5y", "transaction_cost_10y",
                    "total_share_class_cost_3y", "total_share_class_cost_5y", "total_share_class_cost_10y",
                    "holding_cost_3y", "holding_cost_5y", "holding_cost_10y", "fund_company", "benchmark", "index_code",
                    "theme", "product_features", "product_features_history", "fees_history", "fund_manager", "public_purchase_status", "metadata_checked_at",
                ):
                    if field in cached:
                        item[field] = cached[field]
                self._apply_share_history_semantics(item)
                expanded.append(item)

        current_filter_codes = set(availability)
        active_results = [
            item for item in expanded if item["code"] in current_filter_codes
        ]
        if len({_underlying_key(item) for item in active_results}) < 10:
            active_results = [
                item for item in expanded
                if str(item.get("availability_status") or "") not in PURCHASE_UNAVAILABLE_STATUSES
            ]
        if len({_underlying_key(item) for item in active_results}) < 10:
            raise DataError(
                "最终候选区历史充分的底层基金不足 10 个，无法输出 Top 10"
            )

        self._enrich_structural_metadata(active_results, model, progress)
        active_results = [item for item in active_results if str(item.get("availability_status") or "") not in PURCHASE_UNAVAILABLE_STATUSES]
        if len({_underlying_key(item) for item in active_results}) < 10:
            raise DataError("公开申购状态过滤后可用于 Top10 的不同底层基金不足 10 个")
        progress(
            "按完整费率选择 A/C/I 具体份额，并生成相关性/主题约束后的推荐 Top 10",
            93,
        )
        with self.lock:
            self.market_funds = training_pool
            self.funds = active_results
            self.feature_cache.clear()
            self.store.save_model(model)
            self._persist_current()

        self._last_full_nav_refresh_at = 0.0
        gate = self._final_freshness_gate(quick_profile, quick_holding_years, progress)
        if gate.get("ok"):
            progress("正式 Top10 已通过新鲜度/申购状态强制门控；AI 与 SQLite 已保存", 100)
        else:
            progress("新鲜度门控未通过；仅保留‘上次有效 Top10’语义，不冒充当前结果", 100)


    @staticmethod
    def _return_correlation(left: dict, right: dict, lookback: int = 504) -> float:
        ld, lr = left.get("dates") or [], left.get("returns") or []
        rd, rr = right.get("dates") or [], right.get("returns") or []
        if len(ld) != len(lr) or len(rd) != len(rr):
            return 0.0
        lmap = dict(zip(ld[-lookback:], lr[-lookback:]))
        rmap = dict(zip(rd[-lookback:], rr[-lookback:]))
        common = sorted(set(lmap) & set(rmap))
        if len(common) < 126:
            return 0.0
        return _clamp(_pearson([lmap[d] for d in common], [rmap[d] for d in common]), -1.0, 1.0)

    def rankings(
        self,
        profile: str,
        *,
        cross_verify: bool = True,
        holding_years: int | None = None,
    ) -> list[dict]:
        with self.lock:
            scored = self.ranker.score(
                self.funds,
                self.store.model,
                profile,
                self.feature_cache,
                holding_years=_expected_holding_years(holding_years),
            )
            chosen = self.ranker.select_portfolio(scored, profile)
            raw_rank = {item["code"]: index+1 for index,item in enumerate(scored)}
            warnings = []
            if chosen and all(item.get("long_term_quality") in {"一般", "偏弱"} for item in chosen):
                warnings.append("这是相对前10，不代表当前适合立即买入")
            if not (self.last_freshness_gate or {}).get("ok"):
                warnings.append("上次有效 Top10：本次强制新鲜度门控尚未通过")
            if chosen and any(item.get("pit_rating_capped") for item in chosen):
                warnings.append("PIT宇宙/OOS证据不足，绝对买入评级已硬降级")
            self.last_ranking_warning = "；".join(warnings)
            for rank, item in enumerate(chosen, 1):
                item["ai_raw_rank"] = raw_rank.get(item["code"], rank)
                item["ranking_rank"] = rank

        if (
            cross_verify
            and len(chosen) == 10
            and hasattr(getattr(self, "source", None), "cross_verify_top10")
        ):
            try:
                keys = [
                    (
                        item["code"],
                        str(
                            item.get("display_nav_date")
                            or item.get("latest_date")
                            or ""
                        ),
                    )
                    for item in chosen
                ]
                if all(key in self._cross_check_cache for key in keys):
                    for item, key in zip(chosen, keys):
                        item.update(self._cross_check_cache[key])
                    self.last_cross_check = {
                        "verified": sum(
                            bool(item.get("independent_source_verified"))
                            for item in chosen
                        ),
                        "requested": 10,
                        "source": "新浪财经基金中心",
                        "cached": True,
                    }
                else:
                    self.last_cross_check = self.source.cross_verify_top10(chosen)
                    for item, key in zip(chosen, keys):
                        self._cross_check_cache[key] = {
                            field: item.get(field)
                            for field in (
                                "independent_source_verified",
                                "metadata_cross_verified",
                                "independent_source",
                                "independent_source_nav",
                                "independent_source_note",
                            )
                        }
                for item in chosen:
                    item["AlipayAvailabilityConfidence"] = _alipay_availability_confidence(item)
            except Exception as exc:
                self.last_cross_check = {
                    "verified": 0,
                    "requested": 10,
                    "source": "新浪财经基金中心",
                    "error": str(exc)[:160],
                }
        return chosen


    @staticmethod
    def _apply_latest_rows(funds: list[dict], latest: dict[str, dict]) -> int:
        updated_series=0; lookup={item["code"]:item for item in funds}
        for code,row in latest.items():
            item=lookup.get(code)
            if not item: continue
            old_date=str(item.get("latest_date") or ((item.get("dates") or [""])[-1])); old_nav=_finite(item.get("latest_nav"),float("nan"))
            new_date=str(row.get("nav_date") or "")[:10]; new_nav=_finite(row.get("nav"),float("nan")); source_day=_finite(row.get("day_change"),float("nan"))
            if row.get("name"): item["name"]=row["name"]
            if row.get("latest_sources"):
                item["latest_sources"] = list(row.get("latest_sources") or [])
                item["latest_public_confirmations"] = int(_finite(row.get("latest_public_confirmations"), len(item["latest_sources"])))
                signals = _public_availability_signals(item)
                item["availability_public_signals"] = sorted(signals)
                item["availability_public_confirmations"] = len(signals)
            if math.isfinite(new_nav) and new_nav>0: item["display_nav"]=new_nav
            if new_date: item["display_nav_date"]=new_date
            if math.isfinite(source_day): item["day_change"]=source_day
            if new_date and new_date>old_date and math.isfinite(new_nav) and new_nav>0 and math.isfinite(old_nav) and old_nav>0:
                nav_return=new_nav/old_nav-1.0; source_return=source_day/100.0 if math.isfinite(source_day) else float("nan")
                                                                                                     
                                                                                                                             
                agreed=math.isfinite(source_return) and abs(source_return-nav_return)<=max(0.0035,0.15*abs(source_return))
                if agreed:
                    item.setdefault("dates",[]).append(new_date); item.setdefault("returns",[]).append(_clamp(nav_return,-0.8,2.0))
                    item["latest_nav"]=new_nav; item["latest_date"]=new_date; item["return_pending_adjustment"]=False; item["updated_at"]=_now_iso(); updated_series+=1
                else:
                    item["return_pending_adjustment"]=True
            elif new_date==old_date and math.isfinite(new_nav) and new_nav>0:
                item["latest_nav"]=new_nav
        return updated_series

    def _resolve_pending_adjustments(self, funds: list[dict], max_workers: int = 4) -> int:
        pending = [item for item in funds if item.get("return_pending_adjustment") is True]
        if not pending:
            return 0
        resolved = 0
        def resolve(item):
            cached = {"dates": list(item.get("dates") or []), "returns": list(item.get("returns") or []),
                      "latest_nav": item.get("latest_nav"), "latest_date": item.get("latest_date", "")}
            return self.source.update_history(item["code"], cached) if hasattr(self.source, "update_history") else self.source.history(item["code"])
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(max_workers, len(pending)), thread_name_prefix="corp-action") as pool:
            futures = {pool.submit(resolve, item): item for item in pending}
            for future in concurrent.futures.as_completed(futures):
                item = futures[future]
                try:
                    history = future.result()
                except Exception:
                    continue
                dates, returns = history.get("dates") or [], history.get("returns") or []
                if len(dates) == len(returns) and len(returns) >= MIN_HISTORY_POINTS and str(history.get("latest_date") or "") >= str(item.get("display_nav_date") or ""):
                    for key in ("dates","returns","latest_nav","latest_date","return_basis","return_provider_fallbacks","return_corporate_actions","return_accumulated_confirmations"):
                        if key in history:
                            item[key] = history[key]
                    item["return_pending_adjustment"] = False; item["updated_at"] = _now_iso(); resolved += 1
        return resolved

    @staticmethod
    def _availability_fields(declared: dict) -> dict:
        keys = (
            "availability_declared","availability_status","availability_note","fund_data_source","availability_declared_at","availability_generated_at","availability_expires_at","availability_sequence","availability_signature_alg",
            "availability_source","availability_source_id","availability_evidence","availability_schema_version",
            "fees_verified","fees","fees_history","fees_source","fee_schedule_complete","fee_field_verified","annual_cost","embedded_annual_cost","purchase_cost",
            "transaction_cost_3y","transaction_cost_5y","transaction_cost_10y",
            "total_share_class_cost_3y","total_share_class_cost_5y","total_share_class_cost_10y",
            "holding_cost_3y","holding_cost_5y","holding_cost_10y",
            "available_from","available_to","availability_history","share_class","product_features","product_features_history",
            "benchmark","index_code","fund_company","fund_manager","theme","public_purchase_status",
            "underlying_fund_id","master_code","primary_code","inception_date","termination_date","merged_into",
            "metadata_source","metadata_checked_at",
            "display_nav","display_nav_date","return_pending_adjustment","return_basis","return_provider_fallbacks","return_corporate_actions","return_accumulated_confirmations",
        )
        optional_structural = {
            "benchmark","index_code","fund_company","fund_manager","theme","public_purchase_status","underlying_fund_id","master_code","primary_code",
            "inception_date","termination_date","merged_into","metadata_source","metadata_checked_at","product_features","product_features_history","fees_history",
        }
        return {
            key: declared[key] for key in keys if key in declared
            and (key not in optional_structural or declared.get(key) not in (None, "", {}, []))
        }

    def _sync_candidate_pool(
        self,
        availability: dict[str, dict],
    ) -> tuple[list[str], list[str], list[str]]:
        with self.lock:
            current = {item["code"]: item for item in self.funds}

        availability_codes = set(availability)
        current_codes = set(current)
        removed_codes = sorted(current_codes - availability_codes)
        kept = []

        for code, item in current.items():
            if code not in availability_codes:
                continue
            declared = availability[code]
            updated = dict(item)
            updated.update(self._availability_fields(declared))
            updated["availability_history"] = self._merge_observed_availability(
                declared, item
            )
            updated["name"] = (
                declared.get("name") or updated.get("name") or code
            )
            updated["type"] = (
                declared.get("type") or updated.get("type") or "其他"
            )
            if _candidate_allowed(updated["name"], updated["type"]):
                kept.append(updated)

        archive = (
            self.store.cache.get("funds", {})
            if isinstance(self.store.cache.get("funds", {}), dict)
            else {}
        )
        current_group_lookup = {}
        for item in kept:
            group_key = (
                _base_name(item.get("name", "")).casefold(),
                _asset_bucket(item.get("name", ""), item.get("type", "")),
                _wrapper_type(item.get("type", "")),
            )
            current_group_lookup.setdefault(group_key, item)

        added_items = []
        failed_new = []
        deferred = 0
        for code in sorted(availability_codes - current_codes):
            declared = availability[code]
            cached = (
                archive.get(code)
                if isinstance(archive.get(code), dict)
                else None
            )
            name = (
                declared.get("name")
                or (cached or {}).get("name")
                or code
            )
            fund_type = (
                declared.get("type")
                or (cached or {}).get("type")
                or "其他"
            )
            if not _candidate_allowed(name, fund_type):
                continue

            candidate = None
            if cached:
                dates, returns = (
                    cached.get("dates") or [],
                    cached.get("returns") or [],
                )
                if (
                    len(returns) >= MIN_HISTORY_POINTS
                    and len(dates) == len(returns)
                    and self._history_recent_enough(cached, max_days=5)
                ):
                    candidate = {
                        "code": code,
                        **cached,
                        **self._availability_fields(declared),
                    }

            if candidate is None:
                group_key = (
                    _base_name(name).casefold(),
                    _asset_bucket(name, fund_type),
                    _wrapper_type(fund_type),
                )
                representative = current_group_lookup.get(group_key)
                if representative is not None:
                    candidate = {
                        **declared,
                        "code": code,
                        "name": name,
                        "type": fund_type,
                        "dates": list(representative.get("dates") or []),
                        "returns": list(representative.get("returns") or []),
                        "latest_nav": representative.get("latest_nav"),
                        "latest_date": representative.get("latest_date"),
                        "updated_at": representative.get("updated_at"),
                        "underlying_fund_id": _underlying_key(representative),
                        "representative_history_code": representative.get(
                            "representative_history_code",
                            representative.get("code"),
                        ),
                    }

            if candidate is None:
                deferred += 1
                continue

            candidate.update(self._availability_fields(declared))
            self._apply_share_history_semantics(candidate)
            candidate["availability_history"] = self._merge_observed_availability(
                declared, cached if isinstance(cached, dict) else None
            )
            candidate["name"] = name
            candidate["type"] = fund_type
            added_items.append(candidate)

        with self.lock:
            self.funds = kept + added_items
            for code in removed_codes:
                self.feature_cache.pop(code, None)
            for item in added_items:
                self.feature_cache.pop(item["code"], None)

        self.last_sync_deferred_count = deferred
        return (
            [item["code"] for item in added_items],
            removed_codes,
            failed_new,
        )


    def _final_freshness_gate(self, profile: str, holding_years: int | None = None, progress=lambda *_: None) -> dict:
        """Formal Top10 is current only after a fresh Top30 NAV + purchase-status recheck."""
        years = _expected_holding_years(holding_years)
        with self.lock:
            preliminary = self.ranker.score(self.funds, self.store.model, profile, self.feature_cache, holding_years=years)
            gate_candidates = preliminary[:FINAL_FRESHNESS_CANDIDATES]
            codes = [item["code"] for item in gate_candidates]
            provisional_top10 = [item["code"] for item in preliminary[:10]]
        if len(provisional_top10) < 10:
            self.last_freshness_gate = {"ok": False, "reason": "正式门控前候选不足10只"}
            return self.last_freshness_gate
        progress(f"正式展示前强制复核 Top{len(codes)} 最新净值与申购状态", 96)
        report = self.source.latest_many(codes)
        rows = report.get("rows") or {}
        today = _china_today(); fresh_rows = {}
        for code, row in rows.items():
            try:
                day = _dt.date.fromisoformat(str(row.get("nav_date") or "")[:10])
            except ValueError:
                continue
            nav = _finite(row.get("nav"), float("nan"))
            if math.isfinite(nav) and nav > 0 and _expected_market_sessions(day, today) <= FRESH_NAV_MAX_MARKET_SESSIONS:
                fresh_rows[code] = row
        fresh_coverage = len(fresh_rows) / max(1, len(codes))
        top10_fresh = all(code in fresh_rows for code in provisional_top10)
        # Purchase-status recheck is mandatory for the formal shortlist; failures leave the result in last-valid mode.
        metadata = self.source.metadata_many(gate_candidates) if hasattr(self.source, "metadata_many") else {}
        meta_coverage = len(metadata) / max(1, len(codes))
        with self.lock:
            lookup = {item["code"]: item for item in self.funds}
            for code, values in metadata.items():
                item = lookup.get(code)
                if not item or not isinstance(values, dict):
                    continue
                for field in ("public_purchase_status", "public_purchase_status_secondary", "termination_date", "metadata_checked_at", "availability_public_signals", "availability_public_confirmations"):
                    if field in values and values.get(field) not in (None, ""):
                        item[field] = values[field]
                if item.get("availability_status") != "confirmed_purchasable":
                    classified = self._classify_public_purchase_status(str(item.get("public_purchase_status") or ""), str(item.get("termination_date") or ""))
                    item["availability_status"] = classified
                    item["availability_note"] = self._public_status_note(classified)
                self._apply_share_history_semantics(item)
            # Remove newly proven purchase-suspended/closed rows before deciding whether the formal gate passes.
            self.funds = [item for item in self.funds if str(item.get("availability_status") or "") not in PURCHASE_UNAVAILABLE_STATUSES]
            if fresh_coverage >= FINAL_FRESHNESS_COVERAGE and top10_fresh and meta_coverage >= FINAL_FRESHNESS_COVERAGE:
                self._apply_latest_rows(self.funds, fresh_rows)
                self._resolve_pending_adjustments(self.funds)
                self._persist_current()
                ok = len(self.ranker.select_portfolio(self.ranker.score(self.funds, self.store.model, profile, self.feature_cache, holding_years=years), profile)) >= 10
            else:
                ok = False
        reason = (
            f"Top{len(codes)}新鲜净值{fresh_coverage:.1%}、申购状态复核{meta_coverage:.1%}、原Top10新鲜={'是' if top10_fresh else '否'}"
        )
        self.last_freshness_gate = {"ok": bool(ok), "fresh_coverage": fresh_coverage, "metadata_coverage": meta_coverage, "top10_fresh": top10_fresh, "reason": reason, "checked_at": _now_iso()}
        return dict(self.last_freshness_gate)

    def refresh_latest(
        self,
        profile: str,
        holding_years: int | None = None,
    ) -> dict:
        started = time.monotonic()
        self.ensure_source_contract()
        years = _expected_holding_years(holding_years)
        availability = self._availability_snapshot()
        added, removed, failed_new = self._sync_candidate_pool(availability)

        with self.lock:
            all_codes = [item["code"] for item in self.funds]
            priority_scored = self.ranker.score(
                self.funds,
                self.store.model,
                profile,
                self.feature_cache,
                holding_years=years,
            )
            priority_codes = [
                item["code"] for item in priority_scored[:LATEST_PRIORITY_COUNT]
            ]

        if len(all_codes) < 10:
            self._persist_current()
            raise DataError("当前候选且历史数据充足的份额不足 10 个")

        full_due = (
            self._last_full_nav_refresh_at <= 0
            or time.monotonic() - self._last_full_nav_refresh_at
            >= FULL_NAV_REFRESH_SECONDS
            or bool(added or removed)
        )
        request_codes = all_codes if full_due else priority_codes
        report = self.source.latest_many(request_codes)
        rows = report.get("rows") or {}
        requested = int(report.get("requested", len(request_codes)))
        received = int(report.get("received", len(rows)))
        returned_coverage = received / max(1, requested)

        today = _china_today()
        fresh_rows = {}
        stale_codes = []
        for code, row in rows.items():
            date_text = str(row.get("nav_date") or "")[:10]
            try:
                nav_date = _dt.date.fromisoformat(date_text)
            except ValueError:
                stale_codes.append(code)
                continue
            nav = _finite(row.get("nav"), float("nan"))
            sessions = _expected_market_sessions(nav_date, today)
            if (
                math.isfinite(nav)
                and nav > 0
                and sessions <= FRESH_NAV_MAX_MARKET_SESSIONS
            ):
                fresh_rows[code] = row
            else:
                stale_codes.append(code)

        fresh_coverage = len(fresh_rows) / max(1, requested)
        priority_missing = sorted(set(priority_codes) - set(fresh_rows))
        priority_complete = not priority_missing
        ranking_updated = bool(
            full_due
            and fresh_coverage >= REFRESH_MIN_COVERAGE
            and priority_complete
        )

        updated_series = 0
        resolved_adjustments = 0

        if ranking_updated:
            with self.lock:
                updated_series = self._apply_latest_rows(
                    self.funds, fresh_rows
                )
                resolved_adjustments = self._resolve_pending_adjustments(
                    self.funds
                )
                updated_series += resolved_adjustments
                self._persist_current()
                results = self.rankings(
                    profile, holding_years=years
                )
            self._last_full_nav_refresh_at = time.monotonic()
            status = (
                f"全候选净值：返回 {returned_coverage:.1%} / "
                f"新鲜 {fresh_coverage:.1%} / 陈旧 {len(stale_codes)}；"
                f"Top {len(priority_codes)} 全部新鲜，已重排"
            )
        elif not full_due:
            with self.lock:
                lookup = {item["code"]: item for item in self.funds}
                for code, row in fresh_rows.items():
                    item = lookup.get(code)
                    if not item:
                        continue
                    nav = _finite(row.get("nav"), float("nan"))
                    if math.isfinite(nav) and nav > 0:
                        item["display_nav"] = nav
                    item["display_nav_date"] = str(
                        row.get("nav_date") or ""
                    )[:10]
                    day_change = _finite(
                        row.get("day_change"), float("nan")
                    )
                    if math.isfinite(day_change):
                        item["day_change"] = day_change
                self._persist_current()
                results = self.rankings(
                    profile, holding_years=years
                )
            status = (
                f"Top {len(priority_codes)} 高频复核：返回 "
                f"{returned_coverage:.1%} / 新鲜 {fresh_coverage:.1%} / "
                f"陈旧 {len(stale_codes)}；完整全池重排每约20分钟执行"
            )
        else:
            with self.lock:
                self._persist_current()
                results = self.rankings(
                    profile, holding_years=years
                )
            status = (
                f"全候选净值：返回 {returned_coverage:.1%} / "
                f"新鲜 {fresh_coverage:.1%} / 陈旧 {len(stale_codes)}；"
            )
            if fresh_coverage < REFRESH_MIN_COVERAGE:
                status += (
                    f"低于新鲜覆盖门槛 {REFRESH_MIN_COVERAGE:.1%}，"
                    "排名未更新"
                )
            else:
                status += (
                    f"Top候选仍有 {len(priority_missing)} 个不新鲜，"
                    "排名未更新"
                )

        if len(results) != 10:
            raise DataError(
                "当前候选且历史数据充足的底层基金不足 10 个，无法输出 Top 10"
            )

        return {
            "results": results,
            "status": status,
            "coverage": fresh_coverage,
            "returned_coverage": returned_coverage,
            "fresh_coverage": fresh_coverage,
            "stale_count": len(stale_codes),
            "stale_codes": sorted(stale_codes),
            "requested": requested,
            "received": received,
            "fresh_received": len(fresh_rows),
            "failed_codes": report.get("failed_codes") or [],
            "priority_codes": sorted(priority_codes),
            "priority_missing_codes": priority_missing,
            "priority_complete": priority_complete,
            "ranking_updated": ranking_updated,
            "full_refresh": full_due,
            "new_codes": added,
            "removed_codes": removed,
            "failed_new_codes": failed_new,
            "updated_series": updated_series,
            "resolved_adjustments": resolved_adjustments,
            "elapsed_seconds": time.monotonic() - started,
        }



# ===== UI / 控制台 =====

METHOD_TEXT = """这是什么

这是一个本地运行的“长期持有组合 Top10 + AI 原始排名”。目标不是预测一个绝对收益数字，而是在同一时间截面的候选基金中做长期横截面排序，再叠加可购证据置信度、产品资料完整性和组合去同质化约束，给出更值得在支付宝搜索并考虑长期持有的 10 只基金。

首次安装

第一次正常启动会让用户选择一次“极简安装 / 完整安装 / 自定义安装”。极简安装只用 Python 标准库，不下载第三方 AI 包；完整安装在后台把固定版本的 NumPy、SciPy、LightGBM，以及兼容 Python 版本时的第二树模型先装入 BestAlipayFunds_deps.tmp，隔离验证导入后再原子切换到 BestAlipayFunds_deps；自定义安装可单独选择 LightGBM、第二树模型和是否自动更新模型。选择保存到 BestAlipayFunds_Settings.json，后续自动读取。程序只从 BestAlipayFunds_deps 加载这些可选 AI 包，不修改用户的全局 Python；旧目录会在切换失败时回滚，安装失败则自动退回原有依赖或纯 Python 模型。

两阶段首启

首次重建先做完全不读取近期收益的结构筛选，并按基金基础名称 + 资产类别 + wrapper 聚合 A/C/I 等具体份额。阶段 1 按资产类别和基金代码做确定性的 performance-blind 分层抽样，只显示“分析中/预览候选”且禁用复制代码；阶段 2 自动继续补齐全量代表历史、元数据和费率，执行完整 walk-forward / AI 重训后替换为最终 Top10。每完成约 75 个代表份额会 checkpoint 到脚本同级 BestAlipayFunds_cache.sqlite3。

购买证据分层

只有签名支付宝证据才显示“支付宝已确认 100/100”。第三方公开状态无论是 60/80 分都统一显示为“平台可购推测”，不再让分数看起来像支付宝本身确认。“暂停大额申购/限购”保留候选并轻度降权；“暂停赎回”仅提示退出限制；“暂停/终止申购、封闭、清盘”才从当前买入候选排除。今天的最终排序使用长期质量排序 × 可购置信度调整 × 产品资料完整性调整；历史 OOS 回测不会把今天的可购状态倒灌到过去。

AI 排名模型

模型选择严格执行 development folds → 候选模型 OOS 比较 → 冻结模型家族 → untouched-test → production refit。树模型学习目标是横截面 ranking：LightGBM 使用 LambdaRank/NDCG；兼容时可加入 XGBoost rank:ndcg。它们与 Expert、分层 Ridge、随机非线性模型一起参加 development OOS 比赛，只有真正胜过简单基线并通过稳定性 gate 的家族才能进入 production。untouched OOS 只用于审计，不参与重新选模型。

模型证据折扣

程序仍明确承认首次运行无法完整恢复历史上已经消失的全部基金，因此 survivorship_bias 仍为真，但不再只显示一句警告。模型证据会根据 historical_universe_known_coverage、historical_availability_coverage、OOS 窗口数、RankIC 离散度和净值新鲜度共同缩水；历史 universe 覆盖低于 25% 时证据因子硬封顶 50/100、低于 60% 时封顶 60/100；费率未验证还会继续降低证据。也就是说，历史宇宙覆盖差、OOS 太少或数据过旧时，即使原始模型一致性很高，界面中的“模型证据”也会被实际压低。

份额历史口径

A/C/I 等具体份额若借用同底层代表份额历史，界面明确标记为“底层”历史，并在取得该份额成立日后截断成立日前数据；因此不会再把成立仅两年的 C 类显示成其自身已有五年历史。该底层历史用于长期底层质量，具体份额成本仍按该份额公开费率计算。

费率与产品完整性

管理费、托管费、销售服务费、申购费、3/5/10 年赎回费必须有公开证据后，fee_schedule_complete 才为真。解析不到的字段保持 None；只有页面明确写 0% / 不收取 / 免收时才记为 0。最终候选区才补齐同底层 A/C/I 具体费率，并按预计持有 3/5/10 年选择成本更合适的份额。产品完整性只做温和调整，不能凭“元数据填得多”压过长期质量。

排名与显示

界面显示 AI 原始名次与去同质化后的推荐 Top10，并显示“可购证据、同类百分位、长期质量、当前择时、绝对买入评级、模型证据/稳定率”。组合层限制重复底层、过度集中主题/公司/资产类别，并对高相关基金施加惩罚。绝对评级用于避免把相对第 1 名误读成现在一定应买。

当前买入时点

近期收益/趋势不再独占择时信号。若指数/QDII公开页面能取得 PE/PB/股息率/风险溢价历史百分位，程序把它压缩为最多约5%的小权重估值信号；拿不到可靠估值时该项严格为0，不猜测、不回填，也不改变长期质量主排序。

正式结果新鲜度

最终 Top10 正式展示前会强制复核 Top30：至少95%最新净值不超过1个市场日、原Top10全部新鲜，同时申购状态复核覆盖至少95%。不满足时界面只能称“上次有效 Top10”，不会冒充当前最值得买入。

数据与风险

基金目录、历史净值、最新净值和元数据均通过 PrimarySource（东方财富）/ SecondarySource（新浪财经）适配器自动降级；无法取得支付宝签名确认时会明确降级为“平台可购推测”或“未知”，绝不把第三方公开申购状态冒充支付宝官方证明。历史表现不预示未来，基金可能亏损；实际买入前仍需在支付宝确认可购、限购、实时费率、官方风险等级与适当性。
"""


class FundsApp:
    def __init__(self, root, tk, ttk, messagebox):
        self.root, self.tk, self.ttk, self.messagebox = root, tk, ttk, messagebox
        self.engine = AnalysisEngine()
        self.events = queue.Queue()
        self.stop_event = threading.Event()
        self.busy = False
        self.refreshing = False
        self.refresh_policy = SmartRefreshPolicy()
        self.next_refresh = float("inf")
        self.current = []
        self.profile = tk.StringVar(value="均衡")
        self.holding_years = tk.IntVar(value=_expected_holding_years())
        self.status = tk.StringVar(value="正在启动本地 AI…")
        self.clock = tk.StringVar(value="智能刷新：等待首次分析")
        self.model_info = tk.StringVar(value="模型：等待训练")
        self.data_info = tk.StringVar(value="数据日期：—")
        self.result_title = tk.StringVar(value="上次有效 Top10 · 正在复核新鲜度")
        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.after(120, self._poll_events)
        self.root.after(1000, self._tick)
        self._start_initial()

    def _build_ui(self):
        self.root.title(f"{APP_NAME} {VERSION}")
        self.root.geometry("1540x780")
        self.root.minsize(1120, 640)
        self.root.configure(bg="#0b1220")
        try:
            self.root.iconname(APP_NAME)
        except Exception:
            pass
        style = self.ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except self.tk.TclError:
            pass
        font = ("Microsoft YaHei UI", 10)
        style.configure(".", font=font)
        style.configure("Root.TFrame", background="#0b1220")
        style.configure("Card.TFrame", background="#111c31")
        style.configure("Title.TLabel", background="#0b1220", foreground="#f8fafc", font=("Microsoft YaHei UI", 22, "bold"))
        style.configure("Sub.TLabel", background="#0b1220", foreground="#94a3b8", font=("Microsoft YaHei UI", 10))
        style.configure("Badge.TLabel", background="#18263f", foreground="#cbd5e1", padding=(10, 5))
        style.configure("Status.TLabel", background="#0b1220", foreground="#94a3b8")
        style.configure("Warn.TLabel", background="#0b1220", foreground="#fbbf24", font=("Microsoft YaHei UI", 9))
        style.configure("TButton", padding=(11, 7), background="#1d4ed8", foreground="#ffffff")
        style.map("TButton", background=[("active", "#2563eb"), ("disabled", "#334155")])
        style.configure("TCombobox", padding=5)
        style.configure("Treeview", background="#111c31", fieldbackground="#111c31", foreground="#e2e8f0", rowheight=36, borderwidth=0)
        style.configure("Treeview.Heading", background="#18263f", foreground="#cbd5e1", relief="flat", padding=(6, 8), font=("Microsoft YaHei UI", 9, "bold"))
        style.map("Treeview", background=[("selected", "#1d4ed8")], foreground=[("selected", "#ffffff")])
        style.configure("Horizontal.TProgressbar", background="#22c55e", troughcolor="#18263f")

        outer = self.ttk.Frame(self.root, style="Root.TFrame", padding=(24, 20, 24, 16))
        outer.pack(fill="both", expand=True)
        header = self.ttk.Frame(outer, style="Root.TFrame")
        header.pack(fill="x")
        titles = self.ttk.Frame(header, style="Root.TFrame")
        titles.pack(side="left", fill="x", expand=True)
        self.ttk.Label(titles, textvariable=self.result_title, style="Title.TLabel").pack(anchor="w")
        self.ttk.Label(
            titles,
            text="同时显示原始 AI 名次与组合入选顺序 · 支付宝多信号分层 · purged walk-forward",
            style="Sub.TLabel",
        ).pack(anchor="w", pady=(5, 0))

        controls = self.ttk.Frame(header, style="Root.TFrame")
        controls.pack(side="right", anchor="e")
        self.ttk.Label(controls, text="风险偏好", style="Sub.TLabel").grid(row=0, column=0, padx=(0, 7))
        profile_box = self.ttk.Combobox(controls, textvariable=self.profile, values=("稳健", "均衡", "进取"), state="readonly", width=7)
        profile_box.grid(row=0, column=1, padx=(0, 8))
        profile_box.bind("<<ComboboxSelected>>", lambda _event: self._rerank())
        self.ttk.Label(controls, text="预计持有", style="Sub.TLabel").grid(row=0, column=2, padx=(5, 7))
        holding_box = self.ttk.Combobox(controls, textvariable=self.holding_years, values=(3, 5, 10), state="readonly", width=4)
        holding_box.grid(row=0, column=3, padx=(0, 8))
        holding_box.bind("<<ComboboxSelected>>", lambda _event: self._rerank())
        self.ttk.Label(controls, text="年", style="Sub.TLabel").grid(row=0, column=4, padx=(0, 5))
        self.ttk.Button(controls, text="立即刷新", command=self._start_refresh).grid(row=0, column=5, padx=4)
        self.ttk.Button(controls, text="重建 AI", command=self._confirm_rebuild).grid(row=0, column=6, padx=4)
        self.ttk.Button(controls, text="复制代码", command=self._copy_selected).grid(row=0, column=7, padx=4)
        self.ttk.Button(controls, text="方法与风险", command=self._show_method).grid(row=0, column=8, padx=(4, 0))

        badges = self.ttk.Frame(outer, style="Root.TFrame")
        badges.pack(fill="x", pady=(18, 12))
        self.ttk.Label(badges, textvariable=self.data_info, style="Badge.TLabel").pack(side="left", padx=(0, 8))
        self.ttk.Label(badges, textvariable=self.model_info, style="Badge.TLabel").pack(side="left", padx=8)
        self.ttk.Label(badges, textvariable=self.clock, style="Badge.TLabel").pack(side="right")

        table_card = self.ttk.Frame(outer, style="Card.TFrame", padding=1)
        table_card.pack(fill="both", expand=True)
        columns = ("portfolio_rank", "ai_raw", "code", "name", "type", "wrapper", "alipay", "percentile", "quality", "timing", "buy_rating", "consistency", "risk", "nav", "day", "ann", "ann5", "cost5y", "dd", "sharpe", "reason", "date")
        self.tree = self.ttk.Treeview(table_card, columns=columns, show="headings", selectmode="browse")
        headings = {
            "portfolio_rank": "组合#", "ai_raw": "原始AI#", "code": "基金代码", "name": "基金名称", "type": "资产类型", "wrapper": "载体", "alipay": "可购证据",
            "percentile": "同类百分位", "quality": "长期质量", "timing": "当前择时", "buy_rating": "绝对买入评级", "consistency": "模型证据/稳定率", "risk": "模型波动风险", "nav": "最新净值", "day": "披露日涨跌", "ann": "历史近3年年化", "ann5": "历史近5年年化",
            "cost5y": "预计持有总成本", "dd": "近5年最大回撤", "sharpe": "夏普", "reason": "入选理由", "date": "净值日期",
        }
        widths = {"portfolio_rank": 54, "ai_raw": 64, "code": 76, "name": 178, "type": 82, "wrapper": 58, "alipay": 126, "percentile": 82, "quality": 70, "timing": 70, "buy_rating": 126, "consistency": 76, "risk": 86, "nav": 76, "day": 82, "ann": 82, "ann5": 82, "cost5y": 112, "dd": 96, "sharpe": 60, "reason": 190, "date": 88}
        for column in columns:
            self.tree.heading(column, text=headings[column])
            self.tree.column(column, width=widths[column], minwidth=widths[column], anchor="center" if column not in ("name", "reason") else "w", stretch=column in ("name", "reason"))
        scrollbar = self.ttk.Scrollbar(table_card, orient="vertical", command=self.tree.yview)
        hscrollbar = self.ttk.Scrollbar(table_card, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=scrollbar.set, xscrollcommand=hscrollbar.set)
        table_card.rowconfigure(0, weight=1); table_card.columnconfigure(0, weight=1)
        self.tree.grid(row=0, column=0, sticky="nsew")
        scrollbar.grid(row=0, column=1, sticky="ns")
        hscrollbar.grid(row=1, column=0, sticky="ew")
        self.tree.tag_configure("positive", foreground="#fb7185")
        self.tree.tag_configure("negative", foreground="#4ade80")
        self.tree.tag_configure("neutral", foreground="#e2e8f0")
        self.tree.bind("<Double-1>", lambda _event: self._copy_selected())

        footer = self.ttk.Frame(outer, style="Root.TFrame")
        footer.pack(fill="x", pady=(12, 0))
        self.progress = self.ttk.Progressbar(footer, mode="determinate", maximum=100, value=0, length=230)
        self.progress.pack(side="left", padx=(0, 10))
        self.ttk.Label(footer, textvariable=self.status, style="Status.TLabel").pack(side="left", fill="x", expand=True)
        self.ttk.Label(
            outer,
            text="支付宝可购状态无法确认时仍会给出公开基金数据的长期候选，但会明确标为“未知（未排除）”；下单前请在支付宝确认可购、费率、限购与适当性。",
            style="Warn.TLabel",
        ).pack(fill="x", pady=(9, 0))

    def _start_initial(self):
        self.busy = True

        def worker():
            try:
                cached = self.engine.load_cached()
                try:
                    self.engine.ensure_source_contract()
                except DataError as exc:
                    self.events.put(("progress", f"数据源契约检查：{exc}", 2))
                if cached:
                    self.events.put(("results", self.engine.rankings(self.profile.get(), holding_years=self.holding_years.get()), "已载入本地缓存"))
                if not cached or self.engine.cache_age_hours() >= 14:
                    self.engine.rebuild(
                        lambda text, pct: self.events.put(("progress", text, pct)),
                        force=False,
                        quick_callback=lambda rows: self.events.put(("stage1_results", rows)),
                        quick_profile=self.profile.get(),
                        quick_holding_years=self.holding_years.get(),
                    )
                    gate = self.engine.last_freshness_gate or {}
                    label = "当前 Top10（已通过强制新鲜度门控）" if gate.get("ok") else "上次有效 Top10（本次新鲜度门控未通过）"
                    self.events.put(("results", self.engine.rankings(self.profile.get(), holding_years=self.holding_years.get()), label))
                self.events.put(("done",))
            except Exception as exc:
                self.events.put(("error", str(exc)))
                self.events.put(("done",))

        threading.Thread(target=worker, name="initial-analysis", daemon=True).start()

    def _confirm_rebuild(self):
        if self.busy:
            self.status.set("当前任务尚未完成")
            return
        if not self.messagebox.askyesno("重建本地 AI", "将增量更新代表份额历史并重新训练 AI；已有历史不会整段重下。继续吗？"):
            return
        self.busy = True
        self.progress["value"] = 0

        def worker():
            try:
                self.engine.rebuild(
                    lambda text, pct: self.events.put(("progress", text, pct)),
                    force=True,
                    quick_callback=lambda rows: self.events.put(("stage1_results", rows)),
                    quick_profile=self.profile.get(),
                    quick_holding_years=self.holding_years.get(),
                )
                gate = self.engine.last_freshness_gate or {}
                label = "AI 重建完成 · 当前 Top10已通过新鲜度门控" if gate.get("ok") else "AI 重建完成 · 仅显示上次有效 Top10"
                self.events.put(("results", self.engine.rankings(self.profile.get(), holding_years=self.holding_years.get()), label))
            except Exception as exc:
                self.events.put(("error", str(exc)))
            finally:
                self.events.put(("done",))

        threading.Thread(target=worker, name="rebuild-analysis", daemon=True).start()

    def _start_refresh(self):
        if self.refreshing or self.busy or not self.current:
            return
        self.refreshing = True
        self.status.set("按分层时钟复核支付宝目录与净值新鲜度…")

        def worker():
            started = time.monotonic()
            try:
                outcome = self.engine.refresh_latest(self.profile.get(), self.holding_years.get())
                self.events.put(("refresh_results", outcome))
            except Exception as exc:
                self.events.put(("refresh_error", str(exc), time.monotonic() - started))
            finally:
                self.events.put(("refresh_done",))

        threading.Thread(target=worker, name="latest-refresh", daemon=True).start()

    def _rerank(self):
        results = self.engine.rankings(self.profile.get(), holding_years=self.holding_years.get())
        if results:
            self._render(results)
            self.status.set(f"已切换为“{self.profile.get()}”权重 / 预计持有 {self.holding_years.get()} 年")

    def _render(self, results):
        self.current = results
        if results and any(item.get("preliminary_phase1") is True for item in results):
            self.result_title.set("预览候选 · 结构盲选分析中")
        else:
            gate = getattr(self.engine, "last_freshness_gate", {}) or {}
            if gate.get("ok"):
                self.result_title.set("当前长期持有组合 Top10 · 已通过新鲜度门控")
            else:
                self.result_title.set("上次有效 Top10 · 本次新鲜度待复核")
        selected_code = None
        selected = self.tree.selection()
        if selected:
            values = self.tree.item(selected[0], "values")
            selected_code = values[2] if values else None
        for child in self.tree.get_children():
            self.tree.delete(child)
        latest_dates = []
        selected_id = None
        for rank, item in enumerate(results, 1):
            stats = item["stats"]
            day = item.get("day_change")
            day_text = "—" if day is None or not math.isfinite(_finite(day, float("nan"))) else f"{day:+.2f}%"
            tag = "positive" if _finite(day) > 0 else "negative" if _finite(day) < 0 else "neutral"
            nav = item.get("display_nav", item.get("latest_nav"))
            nav_text = "—" if nav is None or not math.isfinite(_finite(nav, float("nan"))) else f"{nav:.4f}"
            date = item.get("display_nav_date") or item.get("latest_date") or (item.get("dates") or [""])[-1]
            if date:
                latest_dates.append(date)
            status_key = str(item.get("availability_status") or "unknown")
            confidence = int(_finite(item.get("AlipayAvailabilityConfidence"), _alipay_availability_confidence(item)))
            source_text = _purchase_evidence_label(item)
            row_id = self.tree.insert("", "end", values=(
                rank, int(_finite(item.get("ai_raw_rank"), rank)), item["code"], item["name"], item.get("asset_class", item["type"]), item.get("wrapper", "普通"), source_text,
                f"{_finite(item.get('category_percentile')):.0f}%", f"{item.get('long_term_quality','—')} {_finite(item.get('LongTermQualityScore')):.0f}", f"{item.get('timing_view','—')} {_finite(item.get('EntryTimingScore')):.0f}", item.get("absolute_buy_rating", "可观察"),
                f"{_finite(item.get('model_consistency')):.0f}/100 · 稳{_finite(item.get('Top10SelectionStability')):.0f}%", item["risk"], nav_text, day_text, ("底层 " if item.get("return_basis") == "underlying_fund_history" else "") + f"{stats['return_3y_ann']:+.1%}",
                (("底层 " if item.get("return_basis") == "underlying_fund_history" else "") + f"{stats['return_5y_ann']:+.1%}" if stats.get("long_evidence_strength",0) >= 0.28 else "证据不足"),
                f"{_share_class_cost(item, item.get('selected_holding_years', 5)):.1%}" if item.get("fees_verified") else "交易费率未知",
                f"{stats['max_drawdown_5y']:.1%}", f"{stats['sharpe']:.2f}", item["reason"], date or "—",
            ), tags=(tag,))
            if item["code"] == selected_code:
                selected_id = row_id
        if selected_id:
            self.tree.selection_set(selected_id)
        source_ids = sorted({str(item.get("availability_source_id") or "unknown") for item in results})
        declared = [str(item.get("availability_declared_at") or "") for item in results if item.get("availability_declared_at")]
        declared_text = min(declared)[:19].replace("T"," ") if declared else "—"
        confirmed = sum(str(item.get("availability_status") or "") == "confirmed_purchasable" for item in results)
        limited = sum(str(item.get("availability_status") or "") == "limited_purchasable" for item in results)
        avg_confidence = sum(_finite(item.get("AlipayAvailabilityConfidence"), _alipay_availability_confidence(item)) for item in results) / max(1, len(results))
        source_badge = f"支付宝已确认 {confirmed}/10 · 平台可购推测均值 {avg_confidence:.0f}/100 · 限购 {limited}/10 · 其余均非支付宝官方确认 · 来源：" + ",".join(source_ids[:2])
        cross = getattr(self.engine, "last_cross_check", {}) or {}
        cross_text = f"新浪复核 {int(cross.get('verified',0))}/{int(cross.get('requested',0))}" if cross.get("requested") else "新浪复核 —"
        warning = getattr(self.engine, "last_ranking_warning", "")
        warning_text = f" · {warning}" if warning else ""
        self.data_info.set(f"基金/净值：东方财富主源 + 新浪降级/交叉源 · {max(latest_dates) if latest_dates else '—'} · 支付宝声明：{declared_text} · {source_badge} · {cross_text}{warning_text}")
        model = self.engine.store.model; full = model.get("full_pipeline_oos") or {}; trained = (model.get("trained_at") or "—")[:10]
        coverage = _clamp(_finite(model.get("historical_availability_coverage")), 0.0, 1.0); mode = "AI启用" if model.get("ai_enabled") else f"基线:{model.get('baseline_mode','expert')}"
        bias = " · 存在存续偏差（已保留本机观察到的退出基金）" if model.get("survivorship_bias", True) else ""
        cutoff = ((model.get("split_boundaries") or {}).get("test_feature_start") or "—")[:10]
        target_name = str((model.get("target_spec") or {}).get("name") or "长期目标")
        blend = _finite(model.get("long_term_blend"), 0.80)
        self.model_info.set(f"{mode}：{model.get('universe_size',0)}底层基金 · {target_name} · 长期/择时 {blend:.0%}/{1-blend:.0%} · untouched OOS RankIC中位数 {_finite(full.get('rank_ic_median')):+.2f} · 胜基准 {_finite(full.get('top10_benchmark_win_rate')):.0%} · 测试起点 {cutoff} · 支付宝历史覆盖{coverage:.0%}(诊断) · 训练 {trained}{bias}")

    def _copy_selected(self):
        selected = self.tree.selection()
        if not selected:
            self.status.set("请先选择一只基金")
            return
        values = self.tree.item(selected[0], "values")
        if not values:
            return
        code = str(values[2])
        current_item = next((item for item in self.current if str(item.get("code")) == code), None)
        if current_item and current_item.get("preliminary_phase1") is True:
            self.status.set("阶段1仅为结构盲选预览；全池分析完成前禁用复制代码")
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(code)
        self.root.update_idletasks()
        self.status.set(f"已复制 {code}；请在实际交易平台确认该份额当前可购与最新交易条件")

    def _show_method(self):
        window = self.tk.Toplevel(self.root)
        window.title("方法、数据与风险说明")
        window.geometry("780x620")
        window.configure(bg="#0b1220")
        text = self.tk.Text(
            window, wrap="word", bg="#111c31", fg="#e2e8f0", insertbackground="#ffffff",
            relief="flat", padx=22, pady=18, font=("Microsoft YaHei UI", 10), spacing2=4, spacing3=8,
        )
        text.insert("1.0", METHOD_TEXT)
        text.configure(state="disabled")
        text.pack(fill="both", expand=True, padx=16, pady=16)

    def _poll_events(self):
        try:
            while True:
                event = self.events.get_nowait()
                kind = event[0]
                if kind == "progress":
                    self.status.set(event[1])
                    self.progress["value"] = event[2]
                elif kind == "stage1_results":
                    self._render(event[1])
                    self.status.set("预览候选（80只结构盲选样本）已显示；无正式买入评级、复制已禁用；继续全池分析…")
                    self.progress["value"] = max(_finite(self.progress["value"]), 34)
                elif kind == "results":
                    self._render(event[1])
                    self.status.set(event[2])
                    self.progress["value"] = 100
                    if not getattr(self, "schedule_started", False):
                        delay = self.refresh_policy.initial_delay(event[1])
                        self.next_refresh = time.monotonic() + delay
                        self.schedule_started = True
                elif kind == "refresh_results":
                    outcome = event[1]
                    self._render(outcome["results"])
                    delay = self.refresh_policy.on_success(outcome)
                    self.next_refresh = time.monotonic() + delay
                    self.status.set(outcome["status"] + f"；{self.refresh_policy.last_reason}")
                    self.progress["value"] = 100
                elif kind == "error":
                    self.status.set(f"更新失败：{event[1]}")
                    if not self.current:
                        self.messagebox.showerror("无法完成基金分析", event[1] + "\n\n请保持网络连接后重试；程序会自动在签名支付宝证据与公开多信号候选模式之间降级。")
                elif kind == "refresh_error":
                    delay = self.refresh_policy.on_error(event[2] if len(event) > 2 else 0.0)
                    self.next_refresh = time.monotonic() + delay
                    self.status.set(f"本轮刷新失败，保留上次数据：{event[1]}；{self.refresh_policy.last_reason}")
                elif kind == "done":
                    self.busy = False
                elif kind == "refresh_done":
                    self.refreshing = False
        except queue.Empty:
            pass
        if not self.stop_event.is_set():
            self.root.after(150, self._poll_events)

    def _tick(self):
        now = time.monotonic()
        if math.isfinite(self.next_refresh):
            remaining = max(0.0, self.next_refresh - now)
            self.clock.set(f"智能刷新：{self.refresh_policy.last_reason} · {_human_seconds(remaining)}后")
            if remaining <= 0 and not self.refreshing and not self.busy:
                self.next_refresh = float("inf")
                self._start_refresh()
        else:
            self.clock.set("智能刷新：正在刷新…" if self.refreshing else "智能刷新：等待分析完成")
        if not self.stop_event.is_set():
            self.root.after(1000, self._tick)

    def close(self):
        self.stop_event.set()
        self.root.destroy()


def _run_console():
    engine = AnalysisEngine()
    if not engine.load_cached() or engine.cache_age_hours() >= 14:
        engine.rebuild(lambda text, pct: print(f"[{pct:5.1f}%] {text}"), force=False)
    profile = "均衡"
    holding_years = _expected_holding_years()
    policy = SmartRefreshPolicy()
    results = engine.rankings(profile, holding_years=holding_years)
    delay = policy.initial_delay(results)
    refresh_note = "已载入结果"
    while True:
        os.system("cls" if os.name == "nt" else "clear")
        print(f"{APP_NAME} {VERSION} · 均衡 · 预计持有{holding_years}年 · {time.strftime('%Y-%m-%d %H:%M:%S')}")
        source_ids = sorted({str(item.get("availability_source_id") or "unknown") for item in results})
        declared = min((str(item.get("availability_declared_at") or "") for item in results if item.get("availability_declared_at")), default="—")
        confirmed = sum(str(item.get("availability_status") or "") == "confirmed_purchasable" for item in results)
        alipay_text = f"支付宝已确认 {confirmed}/10；其余为平台推测/未知" if confirmed else "支付宝已确认 0/10；全部仅为平台推测/未知"
        cross = getattr(engine, "last_cross_check", {}) or {}
        print(f"数据来源：基金/净值=东方财富主源+新浪降级/交叉源 · 支付宝={alipay_text}（{','.join(source_ids[:2])}） · Top10复核=新浪 {int(cross.get('verified',0))}/{int(cross.get('requested',0))} · 声明时间 {declared[:19].replace('T',' ')}。")
        print(f"刷新状态：{refresh_note}")
        warning = getattr(engine, "last_ranking_warning", "")
        if warning:
            print(f"排名提示：{warning}")
        print(f"调度策略：{policy.last_reason} · {_human_seconds(delay)}后刷新\n")
        for rank, item in enumerate(results, 1):
            stats = item["stats"]
            ann5_text = f"{stats['return_5y_ann']:+6.1%}" if stats.get("long_evidence_strength", 0) >= 0.28 else "证据不足"
            print(
                f"组合#{rank:2d}/原始AI#{int(_finite(item.get('ai_raw_rank'),rank)):2d}  {item['code']}  {item['name'][:22]:22s}  "
                f"{item.get('asset_class', item.get('type',''))}/{item.get('wrapper','普通')}  "
                f"{_purchase_evidence_label(item):28s}  "
                f"同类百分位 {_finite(item.get('category_percentile')):3.0f}%  "
                f"长期质量 {item.get('long_term_quality','—')}({ _finite(item.get('LongTermQualityScore')):.0f})  当前择时 {item.get('timing_view','—')}({ _finite(item.get('EntryTimingScore')):.0f})  评级 {item.get('absolute_buy_rating','可观察')}  "
                f"模型证据 {_finite(item.get('model_consistency')):3.0f}/100 · Top10稳定率{_finite(item.get('Top10SelectionStability')):3.0f}% (证据因子{_finite(item.get('model_evidence_factor')):3.0f})  "
                f"3年 {stats['return_3y_ann']:+6.1%} / 5年 {ann5_text}  "
                f"预计持有总成本 {(_share_class_cost(item,holding_years) if item.get('fees_verified') else float('nan')):5.1%}  "
                f"5年最大回撤 {stats['max_drawdown_5y']:6.1%}  {item['reason']}"
            )
        print("\n按 Ctrl+C 退出。")
        deadline = time.monotonic() + delay
        while time.monotonic() < deadline:
            time.sleep(min(0.5, deadline - time.monotonic()))
        started = time.monotonic()
        try:
            outcome = engine.refresh_latest(profile, holding_years)
            results = outcome["results"]
            refresh_note = outcome["status"]
            delay = policy.on_success(outcome)
        except DataError as exc:
            results = engine.rankings(profile, holding_years=holding_years)
            if len(results) != 10:
                raise
            refresh_note = f"本轮刷新失败，保留上次结果：{exc}"
            delay = policy.on_error(time.monotonic() - started)


def _synthetic_funds(count=40, points=2400):
    rng = random.Random(20260815)
    funds = []
    types = ("混合型-偏股", "股票型", "债券型", "指数型")
    declared_at = _now_iso()
    for index in range(count):
        quality = (index - count/2) / 80000.0
        returns = [0.0]
        nav = 1.0
        dates = []
        day = _dt.date(2012, 1, 2)
        for day_index in range(points):
            while day.weekday() >= 5:
                day += _dt.timedelta(days=1)
            dates.append(day.isoformat())
            day += _dt.timedelta(days=1)
            if day_index:
                daily = 0.00020 + quality + rng.gauss(0, 0.007 + (index % 4) * 0.0015)
                daily = _clamp(daily, -0.15, 0.15)
                returns.append(daily)
                nav *= 1 + daily
        fees = {
            "purchase_fee": 0.0005 + (index % 3) * 0.0002,
            "management_fee_annual": 0.006 + (index % 5) * 0.001,
            "custody_fee_annual": 0.001,
            "sales_service_fee_annual": 0.0 if index % 2 == 0 else 0.003,
            "redemption_fee_3y": 0.0, "redemption_fee_5y": 0.0, "redemption_fee_10y": 0.0,
        }
        costs = _holding_costs(fees)
        funds.append({
            "code": f"{index:06d}", "name": f"测试基金{index}A", "type": types[index % 4],
            "dates": dates, "returns": returns, "latest_nav": nav, "latest_date": dates[-1],
            "availability_declared": True, "availability_status": "confirmed_purchasable", "availability_declared_at": declared_at, "availability_evidence": "self-test",
            "fees_verified": True, "fees": fees, **costs,
            "available_from": "2020-01-01", "available_to": "",
            "availability_history": [{"from":"2020-01-01","to":"2099-12-31","purchasable":True}],
        })
    return funds



def _validate_runtime(*, formal=False) -> list[tuple[str,str]]:
    checks = []
    if sys.version_info < MIN_PYTHON:
        raise DataError(f"需要 Python {MIN_PYTHON[0]}.{MIN_PYTHON[1]} 或更高版本")
    checks.append(("OK", f"Python >= {MIN_PYTHON[0]}.{MIN_PYTHON[1]}"))
    if struct.calcsize("P") * 8 != 64:
        raise DataError("需要 64 位 Python")
    checks.append(("OK", "64-bit Python"))
    if os.name == "nt":
        version = sys.getwindowsversion()
        if version.major < 10 or version.build < 22000:
            raise DataError("正式环境要求 Windows 11 x64")
        checks.append(("OK", "Windows 11 x64（正式环境）"))
    else:
        if formal:
            raise DataError("正式环境要求 Windows 11 x64")
        checks.append(("SKIP", f"Windows 11 x64（当前测试环境为 {platform.system()}）"))
    if any(path.parent != BASE_DIR for path in (MODEL_PATH, CACHE_PATH, ALIPAY_FILE_PATH, SETTINGS_PATH, DEPS_DIR)):
        raise DataError("AI/缓存/可购状态快照/设置/本地依赖路径必须与脚本同目录")
    checks.append(("OK", "AI/缓存/可购快照/设置/本地依赖路径 == 脚本目录"))
    probe = BASE_DIR / ".BestAlipayFunds_write_test.tmp"
    try:
        _atomic_bytes(probe, b"ok")
        if probe.read_bytes() != b"ok":
            raise OSError("write verification failed")
    except OSError as exc:
        raise DataError(f"脚本目录不可写：{BASE_DIR}\n{exc}") from exc
    finally:
        try:
            probe.unlink(missing_ok=True)
        except OSError:
            pass
    checks.append(("OK", "脚本目录可写 + 原子写入"))
    return checks


# ===== 自测 =====

def _self_test_impl(full=False):
    checks = _validate_runtime(formal=False)

    missing_fee_text = "申购费率 0.1% 销售服务费率 0% 赎回费率 3年以上 0%"
    missing = FundDataSource._parse_fee_schedule(missing_fee_text)
    assert missing["fees_verified"] is False
    assert missing["fees"]["management_fee_annual"] is None
    assert missing["fees"]["custody_fee_annual"] is None
    assert _holding_costs(missing["fees"])["annual_cost"] is None
    assert _holding_costs(missing["fees"])["transaction_cost_5y"] is None

    complete_fee_text = """
    <h3>申购费率</h3><table><tr><td>申购</td><td>小于100万元</td><td>0.10%</td></tr></table>
    管理费率 1.00% 托管费率 0.20% 销售服务费率 0%
    <h3>赎回费率</h3><table><tr><td>大于等于0年</td><td>0%</td></tr></table>
    """
    complete = FundDataSource._parse_fee_schedule(complete_fee_text)
    assert complete["fees_verified"] is True
    assert complete["fees"]["management_fee_annual"] == 0.01
    assert complete["fees"]["custody_fee_annual"] == 0.002
    checks.append(("OK", "费率缺失保持 None；完整成本字段才允许 fees_verified"))

    payload = {"Data":{"LSJZList":[{"FSRQ":"2026-08-14","DWJZ":"1.0"}],"TotalCount":1}}
    rows, total = FundDataSource._history_rows(payload)
    assert total == 1 and rows[0]["DWJZ"] == "1.0"
    adjusted = FundDataSource._normalize_history([
        {"FSRQ":"2026-08-13","DWJZ":"1.0000","LJJZ":"1.0000","JZZZL":"0","FHFCZ":""},
        {"FSRQ":"2026-08-14","DWJZ":"0.9000","LJJZ":"1.0000","JZZZL":"0","FHFCZ":"每份派现金0.1元"},
    ])
    assert len(adjusted["returns"]) == 2
    assert abs(adjusted["returns"][1]) < 1e-12
    assert adjusted["return_corporate_actions"] == 1
    checks.append(("OK", "净值解析与现金分红 total-return 公司行动校正"))

    smoke_funds = _synthetic_funds(14, 900)
    ranker = AdaptiveRanker()
    model = LocalStore.default_model()
    scored = ranker.score(smoke_funds, model, "均衡", {})
    selected = ranker.select_portfolio(scored, "均衡")
    assert len(scored) == 14 and len(selected) == 10
    assert len({item["code"] for item in selected}) == 10
    assert all("ai_raw_rank" in item and "portfolio_max_correlation" in item for item in selected)
    assert all("LongTermQualityScore" in item and "EntryTimingScore" in item and "absolute_buy_rating" in item for item in scored)
    assert all("category_percentile" in item for item in selected)
    assert all(item.get("AlipayAvailabilityConfidence") == 100 for item in scored)
    assert all(50 <= _finite(item.get("model_evidence_factor")) <= 100 for item in scored)
    assert _alipay_availability_confidence({"availability_status":"public_open"}) == 60
    assert _alipay_availability_confidence({"availability_status":"public_open", "availability_public_signals":["public-purchase-open","multi-public-catalog","recent-nav-active"]}) == 80
    assert _alipay_availability_confidence({"availability_status":"unknown"}) == 30
    assert _alipay_availability_confidence({"availability_status":"confirmed_unavailable"}) == 0
    sample_reps = [{"code":f"{i:06d}", "asset_class":("指数" if i%2 else "债券")} for i in range(200)]
    quick_a = AnalysisEngine._quick_start_representatives(sample_reps, 40)
    quick_b = AnalysisEngine._quick_start_representatives(list(reversed(sample_reps)), 40)
    assert [x["code"] for x in quick_a] == [x["code"] for x in quick_b] and len(quick_a) == 40
    assert _asset_bucket("纳斯达克100QDII指数A", "QDII指数型") == "QDII/海外"
    assert _wrapper_type("QDII指数型") == "QDII"
    checks.append(("OK", "14只 synthetic 小样本：纯AI原始名次 + 去同质化推荐Top10 + 长期/择时双分数"))
    time_probe = dict(smoke_funds[0])
    time_probe["inception_date"] = "2010-01-01"
    time_probe["product_features"] = {"fund_size_billion": 10.0}
    q_2018 = ranker._product_quality(time_probe, "均衡", "2018-06-30")
    q_2026 = ranker._product_quality(time_probe, "均衡", "2026-06-30")
    assert q_2026 > q_2018
    checks.append(("OK", "PIT基金年龄回归：历史 as_of_date 不再读取今天日期"))

    pit_probe = dict(time_probe)
    pit_probe["product_features_history"] = [
        {"effective_date":"2018-01-01", "product_features":{"fund_size_billion":1.0, "manager_tenure_years":1.0}},
        {"effective_date":"2025-01-01", "product_features":{"fund_size_billion":20.0, "manager_tenure_years":8.0}},
    ]
    pit_features, _, _ = ranker._pit_fields(pit_probe, "2020-06-30")
    assert pit_features.get("fund_size_billion") == 1.0 and pit_features.get("manager_tenure_years") == 1.0
    checks.append(("OK", "product_features_history 回归：历史回测只读取 feature_date 当时已经生效的产品特征"))

    assert AnalysisEngine._classify_public_purchase_status("暂停申购") == "purchase_suspended"
    assert AnalysisEngine._classify_public_purchase_status("开放申购") == "public_open"
    assert AnalysisEngine._classify_public_purchase_status("", "2026-01-01") == "closed"
    assert AnalysisEngine._classify_public_purchase_status("暂停大额申购") == "limited_purchasable"
    assert AnalysisEngine._classify_public_purchase_status("暂停赎回") == "redemption_suspended"
    assert "limited_purchasable" not in PURCHASE_UNAVAILABLE_STATUSES
    assert "redemption_suspended" not in PURCHASE_UNAVAILABLE_STATUSES
    assert 0 < _alipay_availability_confidence({"availability_status":"limited_purchasable"}) < 100
    checks.append(("OK", "公开申购状态拆分：限购/暂停申购/暂停赎回/封闭/开放/未知可区分"))

    share_probe = {
        "code":"000002", "representative_history_code":"000001", "inception_date":"2025-01-02",
        "dates":["2024-12-30","2025-01-02","2025-01-03"], "returns":[0.0,0.01,-0.005],
    }
    AnalysisEngine._apply_share_history_semantics(share_probe)
    assert share_probe["return_basis"] == "underlying_fund_history"
    assert share_probe["dates"] == ["2025-01-02","2025-01-03"]
    assert share_probe["share_history_truncated_at_inception"] == "2025-01-02"
    checks.append(("OK", "具体份额不再冒充拥有代表份额完整历史；继承口径明确标注并按成立日截断"))

    eligibility_probe = dict(smoke_funds[0])
    eligibility_probe["availability_history"] = [{"from":"2000-01-01","to":"2000-12-31","purchasable":True}]
    end_probe = len(eligibility_probe["dates"])
    assert ranker._eligibility_at(eligibility_probe, end_probe, eligibility_probe["dates"][-1]) == (True, False)
    checks.append(("OK", "历史可购区间未覆盖指定日期时返回未知，而非误报已知可购"))

    future_probe = dict(smoke_funds[0])
    assert ranker._eligibility_at(future_probe, len(future_probe["dates"]), future_probe["dates"][-2]) == (False, False)
    liquidated_probe = dict(smoke_funds[0])
    liquidated_probe["termination_date"] = liquidated_probe["dates"][-10]
    assert ranker._eligibility_at(liquidated_probe, len(liquidated_probe["dates"]), liquidated_probe["dates"][-1]) == (False, False)
    checks.append(("OK", "未来观测泄漏与已清盘基金回归：PIT eligibility 会拒绝未来数据/终止后样本"))

    sample = smoke_funds[0]
    code = sample["code"]
    store = LocalStore()
    store.cache = {
        "version": CACHE_VERSION,
        "updated_at": _now_iso(),
        "fund_master": {code:{"code":code,"name":sample["name"],"type":sample["type"]}},
        "funds": {code:{
            "code":code,"name":sample["name"],"type":sample["type"],
            "dates":sample["dates"][:5],"returns":sample["returns"][:5],
            "availability_history":sample["availability_history"],
            "fees":sample["fees"],"fees_verified":True,
        }},
    }
    store.save_cache()
    store.cache["funds"][code]["dates"].append(sample["dates"][5])
    store.cache["funds"][code]["returns"].append(sample["returns"][5])
    store.save_cache()
    with sqlite3.connect(CACHE_PATH) as connection:
        tables = {row[0] for row in connection.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        nav_count = connection.execute("SELECT COUNT(*) FROM nav_returns WHERE code=?", (code,)).fetchone()[0]
    assert {"fund_master","nav_returns","metadata","availability_history","runtime_state"} <= tables
    assert nav_count == 6
    store.save_model(model)
    reloaded = LocalStore()
    assert reloaded.model["version"] == MODEL_VERSION
    assert len(reloaded.cache["funds"][code]["dates"]) == 6
    checks.append(("OK", "SQLite 五表缓存按 code/date 增量写入；AI JSON 可序列化/重载"))

    complete_a = dict(smoke_funds[0])
    complete_a.update({"code":"880001","name":"同底层测试基金A","fees_verified":True})
    complete_a["fees"] = {
        "purchase_fee":0.012,"management_fee_annual":0.006,"custody_fee_annual":0.001,
        "sales_service_fee_annual":0.0,"redemption_fee_3y":0.0,"redemption_fee_5y":0.0,"redemption_fee_10y":0.0,
    }
    complete_a.update(_holding_costs(complete_a["fees"]))
    complete_c = dict(complete_a)
    complete_c.update({"code":"880002","name":"同底层测试基金C"})
    complete_c["fees"] = {
        "purchase_fee":0.0,"management_fee_annual":0.006,"custody_fee_annual":0.001,
        "sales_service_fee_annual":0.002,"redemption_fee_3y":0.0,"redemption_fee_5y":0.0,"redemption_fee_10y":0.0,
    }
    complete_c.update(_holding_costs(complete_c["fees"]))
    assert ranker._choose_share_classes([complete_a, complete_c], 3)[0]["code"] == "880002"
    assert ranker._choose_share_classes([complete_a, complete_c], 10)[0]["code"] == "880001"
    incomplete = dict(complete_a)
    incomplete["fees_verified"] = False
    incomplete["fees"] = dict(complete_a["fees"], management_fee_annual=None)
    assert math.isinf(_share_class_cost(incomplete, 5))
    checks.append(("OK", "A/C 持有期成本比较拒绝任何未验证成本字段"))

    corr_funds = _synthetic_funds(14, 900)
    for i in range(6):
        corr_funds[i]["returns"] = list(corr_funds[0]["returns"])
        corr_funds[i]["theme"] = "科技"
        corr_funds[i]["fund_company"] = "同一公司"
    corr_scored = ranker.score(corr_funds, LocalStore.default_model(), "均衡", {})
    corr_selected = ranker.select_portfolio(corr_scored, "均衡")
    assert len(corr_selected) == 10
    assert sum(item.get("theme") == "科技" for item in corr_selected) <= 2
    checks.append(("OK", "高相关/同主题/同公司 Top10 回归：推荐组合执行去同质化约束"))

    if full:
        funds = _synthetic_funds(26, 4000)
        trained = ranker.train(funds)
        assert len(trained.get("linear_weights") or []) == len(AdaptiveRanker.FEATURE_NAMES)
        assert trained.get("training_samples", 0) > 0
        assert trained.get("tuning_samples", 0) > 0
        assert trained.get("deployment_validation_samples", 0) > 0
        assert trained.get("validation_samples", 0) > 0
        boundaries = trained.get("split_boundaries") or {}
        assert boundaries.get("walk_forward_folds", 0) >= MIN_OOS_GATE_WINDOWS
        assert boundaries.get("purge_rule")
        assert trained.get("target_spec", {}).get("horizon") in {"3y","5y"}
        assert 0.70 <= trained.get("long_term_blend", 0.0) <= 0.95
        assert "production refit after freeze" in trained.get("selection_dataset", "")
        assert trained.get("evaluation_model") and trained.get("production_model")
        assert trained["production_model"].get("training_samples", 0) >= trained["evaluation_model"].get("training_samples", 0)
        assert trained.get("baseline_mode") in {"ensemble","ensemble_ml","lightgbm","ensemble_xgb","xgboost","ensemble_dual_tree","expert","defensive","low_volatility","quality_momentum"}
        assert isinstance(trained.get("asset_models"), dict)
        assert "ml_selection_rule" in boundaries
        if trained.get("optional_ml") is not None:
            assert trained.get("optional_ml_development_windows", 0) >= MIN_OOS_GATE_WINDOWS
        if trained.get("optional_tree2") is not None:
            assert trained.get("optional_tree2_development_windows", 0) >= MIN_OOS_GATE_WINDOWS
        untouched = trained.get("untouched_test_oos") or {}
        assert untouched.get("windows", 0) >= MIN_OOS_GATE_WINDOWS
        assert untouched.get("fold_purge_rule")
        assert untouched.get("portfolio_assumption") == "initial-equal-weight-buy-and-hold"
        rescored = ranker.score(funds, trained, "均衡", {})
        assert len(rescored) == len(funds)
        assert len(ranker.select_portfolio(rescored, "均衡")) == 10
        checks.append(("OK", "完整 anchored walk-forward：development选择3/5年目标、分层模型与可选LightGBM；untouched仅审计；冻结后production refit"))

        snapshots, info = ranker._build_snapshots(funds)
        assert snapshots and info.get("duplicate_shares_removed") == 0
        assert all(snapshot.get("cross_section_synchronized") is True for snapshot in snapshots)
        assert all(
            all(observed <= snapshot["feature_date"] for observed in snapshot.get("feature_observation_dates") or [])
            for snapshot in snapshots
        )
        checks.append(("OK", "完整 AI 回归：横截面同步且所有特征观测不晚于 feature_date"))

    assert all(Path(path).parent == BASE_DIR for path in (MODEL_PATH, CACHE_PATH, ALIPAY_FILE_PATH, SETTINGS_PATH, DEPS_DIR))
    checks.append(("OK", "AI、SQLite 缓存、可购快照、安装设置、本地依赖严格与脚本同级"))
    for status, text in checks:
        print(f"[{status}] {text}")
    if full:
        print("FULL-SELF-TEST OK")
    else:
        print("SMOKE-TEST OK")


def _network_self_test():
    source = FundDataSource()
    probes = ["000001", "110022", "161725"]
    checks = []
    try:
        catalog = {row["code"]: row for row in source.all_funds()}
    except Exception as exc:
        print(f"[FAIL] 基金目录/东方财富: {str(exc)[:240]}")
        raise SystemExit("NETWORK-SELF-TEST FAILED: 基金目录源不可达或格式已变化")
    present = [code for code in probes if code in catalog]
    checks.append(("基金目录", len(present) >= 2, f"命中 {len(present)}/{len(probes)}: {','.join(present)}"))
    for code in present[:3]:
        try:
            history = source.history(code)
            checks.append((f"{code} 历史净值", len(history.get("dates") or []) >= 450, f"{len(history.get('dates') or [])} 条"))
        except Exception as exc:
            checks.append((f"{code} 历史净值", False, str(exc)[:180]))
    try:
        latest = source.latest_many(present[:3])
        checks.append(("最新净值", latest.get("received", 0) >= max(1, len(present[:3]) - 1), f"{latest.get('received',0)}/{latest.get('requested',0)}"))
    except Exception as exc:
        checks.append(("最新净值", False, str(exc)[:180]))
    for code in present[:2]:
        try:
            meta = source.basic_metadata(code)
            checks.append((f"{code} 基本资料", bool(meta.get("metadata_checked_at")), f"公司={meta.get('fund_company') or '—'} 状态={meta.get('public_purchase_status') or '—'}"))
            checks.append((f"{code} 费率表", "fees_verified" in meta, f"完整={meta.get('fees_verified') is True}"))
        except Exception as exc:
            checks.append((f"{code} 基本资料/费率", False, str(exc)[:180]))
    if present:
        probe = {**catalog[present[0]], "latest_nav": None}
        try:
            verify = source._sina_verify_one(probe)
            checks.append(("新浪交叉验证", bool(verify.get("source")), verify.get("reason") or f"ok={verify.get('ok')}"))
        except Exception as exc:
            checks.append(("新浪交叉验证", False, str(exc)[:180]))
    failed = 0
    for name, ok, detail in checks:
        print(f"[{'OK' if ok else 'FAIL'}] {name}: {detail}")
        failed += int(not ok)
    if failed:
        raise SystemExit(f"NETWORK-SELF-TEST FAILED: {failed} 项；上面已标出具体数据源/解析阶段")
    print("NETWORK-SELF-TEST OK")


def _self_test(full=False):
    global BASE_DIR, CACHE_PATH, MODEL_PATH, ALIPAY_FILE_PATH, SETTINGS_PATH, DEPS_DIR
    original_paths = (BASE_DIR, CACHE_PATH, MODEL_PATH, ALIPAY_FILE_PATH, SETTINGS_PATH, DEPS_DIR)
    with tempfile.TemporaryDirectory(prefix="BestAlipayFunds-selftest-") as temp_dir:
        BASE_DIR = Path(temp_dir)
        CACHE_PATH = BASE_DIR / "BestAlipayFunds_cache.sqlite3"
        MODEL_PATH = BASE_DIR / "BestAlipayFunds_AI.json"
        ALIPAY_FILE_PATH = BASE_DIR / "BestAlipayFunds_AlipayAvailability.json"
        SETTINGS_PATH = BASE_DIR / "BestAlipayFunds_Settings.json"
        DEPS_DIR = BASE_DIR / "BestAlipayFunds_deps"
        try:
            _save_install_settings({"install_mode":"minimal", "lightgbm":False, "advanced_tree":False, "auto_update_model":True})
            _self_test_impl(full=full)
        finally:
            BASE_DIR, CACHE_PATH, MODEL_PATH, ALIPAY_FILE_PATH, SETTINGS_PATH, DEPS_DIR = original_paths

def _set_windows_dpi():
    if os.name != "nt":
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


def main():
    if sys.version_info < MIN_PYTHON:
        message = f"需要 Python {MIN_PYTHON[0]}.{MIN_PYTHON[1]} 或更高版本（64 位）。"
        print(message)
        raise SystemExit(2)
    if "--version" in sys.argv:
        print(VERSION)
        return
    if "--full-self-test" in sys.argv:
        _self_test(full=True)
        sys.stdout.flush(); sys.stderr.flush(); os._exit(0)
    if "--network-self-test" in sys.argv:
        _network_self_test()
        return
    if "--smoke-test" in sys.argv or "--self-test" in sys.argv:
        _self_test(full=False)
        sys.stdout.flush(); sys.stderr.flush(); os._exit(0)
    _set_windows_dpi()
    if "--configure-install" in sys.argv:
        _choose_install_mode_gui(force=True)
        return
    _choose_install_mode_gui(force=False)
    try:
        _validate_runtime(formal=(os.name == "nt"))
    except DataError as exc:
        print(f"启动检查失败：{exc}", file=sys.stderr); raise SystemExit(2)
    if "--console" in sys.argv:
        try:
            _run_console()
        except DataError as exc:
            local = _read_json(ALIPAY_FILE_PATH, {})
            last = AlipayAvailabilitySource._payload_time(local) if isinstance(local, dict) else ""
            print("\n公开基金/净值数据源不可用，暂时无法生成 Top 10。", file=sys.stderr)
            print(str(exc), file=sys.stderr)
            print(f"最后成功的支付宝可购声明时间：{last or '无'}", file=sys.stderr)
            print("程序会自动在‘签名支付宝可购源’与‘支付宝状态未知的公开基金候选模式’之间降级，无需用户配置环境变量。请保持网络连接后重试。", file=sys.stderr)
            raise SystemExit(3)
        return
    try:
        import tkinter as tk
        from tkinter import messagebox, ttk

        root = tk.Tk()
        FundsApp(root, tk, ttk, messagebox)
        root.mainloop()
    except ImportError:
        _run_console()
    except Exception as exc:
        try:
            import tkinter.messagebox as messagebox
            messagebox.showerror(APP_NAME, f"启动失败：{exc}")
        except Exception:
            print(f"启动失败：{exc}", file=sys.stderr)
        if not isinstance(exc, DataError):
            raise


if __name__ == "__main__":
    main()
