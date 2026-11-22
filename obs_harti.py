#!/usr/bin/env python3
"""
Hărți cu valorile ÎNREGISTRATE (ANM) pentru compararea cu modelele, pe grila comună ALADIN 2,3 km.

Pentru fiecare zi D (ultimele 10 zile):
  - tx  temperatura maximă a zilei D            (ANM: grid zilnic 1 km; până apare: interpolat din stații)
  - tn  temperatura minimă a nopții care se încheie în dimineața zilei D
  - p24 precipitații 24 h, ziua climatologică ANM (06–06 UTC): gridul ANM; până apare, radar + pluviometre
        (radar polarimetric propriu în est — radar_galati.py —, compozitul ANM în rest; factor mediu pe sursă +
        conditional merging, Ehret 2002); fără radar: kriging din pluviometre
  - precipitații 1 h: totalul zilei împărțit pe ore după radar (Lewis et al. 2018); ziua curentă: radar provizoriu
  - temperaturi: kriging cu regresie după altitudine, latitudine, longitudine (Hengl et al. 2007), validat zilnic
    prin validare încrucișată și față de gridul ANM (în jurnal); toate hărțile tăiate la granița României
  - wx  vântul maxim (medie 10 min), 06 UTC D – 06 UTC D+1, din observațiile orare la stații
  - gx  rafala maximă, același interval, din observațiile orare la stații

Surse (CC BY 4.0, Administrația Națională de Meteorologie, portalul opendata.geo.meteoromania.ro):
  - grid zilnic 1 km (COG): /data/grid/cog/{tmax|tmin|precip}/YYYY-MM-DD.tif   (apare cu 2–3 zile întârziere)
  - date zilnice la stații: /data/stations/by_year/YYYY.csv                    (apare a doua zi)
  - observații orare (24 h în urmă): api.meteogate.eu (EUMETNET E-SOH), arhivate local de acest script

Rulează din oră în oră (Task Scheduler). Publică pe GitHub Pages dacă există github.txt.
"""
import base64
import gzip
import json
import logging
import os
import re
import shutil
import struct
import sys
import time
import urllib.error
import urllib.request
import zlib
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone

import numpy as np

log = logging.getLogger("obs")

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
STORE = os.path.join(HERE, "arhiva_orara.json")
FORMAT = "obs1"
DAYS = 10
ODP = "https://opendata.geo.meteoromania.ro"
EDR = "https://api.meteogate.eu/eu-eumetnet-surface-observations/collections/observations"

# grila comună a tuturor hărților (ALADIN 2,3 km)
LON0, LAT0, DLON, DLAT, CW, CH = 19.0, 42.5, 0.03, 0.021, 367, 334
GLON, GLAT = np.meshgrid(LON0 + np.arange(CW) * DLON, LAT0 + np.arange(CH) * DLAT)
MISSING = -99.0
STEP = {"tx": 0.1, "tn": 0.1, "p24": 0.1, "wx": 0.5, "gx": 0.5, "t": 0.1, "pr": 0.1, "w": 0.5, "g": 0.5, "u": 0.1, "v": 0.1}
MIN_ST = 15                       # minimum de stații ca să desenăm o hartă interpolată
HOURLY_H = 72                     # câte ore de observații orare se afișează
FIELDS = ["tx", "tn", "p24", "wx", "gx"]
LAPSE = 0.0065


def http(url, tries=5, timeout=90):
    for k in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "HartiMeteo/1.0"})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code in (400, 404):
                raise
            if k == tries - 1:
                raise
        except Exception:
            if k == tries - 1:
                raise
        time.sleep(3 * (k + 1))


# ---------------- citire GeoTIFF (COG) ANM: float32, tile-uri 256, deflate ----------------
def read_cog(buf):
    le = buf[:2] == b"II"
    e = "<" if le else ">"
    ifd = struct.unpack(e + "I", buf[4:8])[0]
    n = struct.unpack(e + "H", buf[ifd:ifd + 2])[0]
    size = {1: 1, 2: 1, 3: 2, 4: 4, 12: 8, 16: 8}
    tags = {}
    for i in range(n):
        p = ifd + 2 + 12 * i
        tag, typ, cnt = struct.unpack(e + "HHI", buf[p:p + 8])
        sz = size.get(typ, 1) * cnt
        off = p + 8 if sz <= 4 else struct.unpack(e + "I", buf[p + 8:p + 12])[0]
        if typ == 3:
            v = struct.unpack(e + "%dH" % cnt, buf[off:off + 2 * cnt])
        elif typ == 4:
            v = struct.unpack(e + "%dI" % cnt, buf[off:off + 4 * cnt])
        elif typ == 12:
            v = struct.unpack(e + "%dd" % cnt, buf[off:off + 8 * cnt])
        elif typ == 2:
            v = buf[off:off + cnt].rstrip(b"\0").decode("latin-1")
        else:
            v = None
        tags[tag] = v
    w, h = tags[256][0], tags[257][0]
    tw, th = tags[322][0], tags[323][0]
    if tags.get(259, (1,))[0] != 8 or tags.get(339, (1,))[0] != 3 or tags.get(258, (32,))[0] != 32:
        raise RuntimeError("format GeoTIFF neașteptat (compresie %s, tip %s)" % (tags.get(259), tags.get(339)))
    pred = tags.get(317, (1,))[0]
    offs, cnts = tags[324], tags[325]
    ntx = (w + tw - 1) // tw
    out = np.full((((h + th - 1) // th) * th, ntx * tw), np.nan, np.float32)
    for i, (o, c) in enumerate(zip(offs, cnts)):
        raw = zlib.decompress(buf[o:o + c])
        if pred == 3:
            raise RuntimeError("predictor 3 nesuportat")
        a = np.frombuffer(raw, dtype=e + "f4").reshape(th, tw)
        ty, tx = divmod(i, ntx)
        out[ty * th:(ty + 1) * th, tx * tw:(tx + 1) * tw] = a
    out = out[:h, :w]
    nod = tags.get(42113)
    if nod:
        try:
            out[out == float(nod)] = np.nan
        except ValueError:
            pass
    out[out < -9000] = np.nan
    scale = tags[33550]
    tie = tags[33922]
    return out, tie[3], tie[4], scale[0], scale[1]          # tablou, lon stânga, lat sus, pași


def cog_to_grid(url):
    a, lonL, latT, dx, dy = read_cog(http(url, tries=2))
    h, w = a.shape
    # media celulelor de 1 km din jurul fiecărui punct al grilei comune (≈ 3x3)
    fx = (GLON - lonL) / dx - 0.5
    fy = (latT - GLAT) / dy - 0.5
    ix = np.round(fx).astype(int); iy = np.round(fy).astype(int)
    s = np.zeros(GLON.shape); n = np.zeros(GLON.shape)
    for di in (-1, 0, 1):
        for dj in (-1, 0, 1):
            x = ix + di; y = iy + dj
            ok = (x >= 0) & (y >= 0) & (x < w) & (y < h)
            v = np.full(GLON.shape, np.nan)
            v[ok] = a[y[ok], x[ok]]
            good = np.isfinite(v)
            s[good] += v[good]; n[good] += 1
    out = np.where(n >= 3, s / np.maximum(n, 1), np.nan)
    return out.astype(np.float32)


# ---------------- stații ----------------
def relief():
    for q in (os.path.join(HERE, "relief_aladin.npy"), os.path.join(HERE, "..", "HartiICON", "relief_aladin.npy"),
              os.path.join(HERE, "..", "HartiAladin4", "orog_aladin.npy")):
        if os.path.exists(q):
            a = np.load(q)
            if a.shape == (CH, CW):
                return a.astype(np.float32)
    raise RuntimeError("lipsește relieful comun (relief_aladin.npy)")


def stations():
    j = json.loads(http(ODP + "/data/stations/stations.geojson"))
    st = []
    for f in j["features"]:
        p = f["properties"]
        st.append({"id": f["id"], "name": p.get("name_display") or p.get("name"), "lon": float(p["lon"]),
                   "lat": float(p["lat"]), "z": float(p.get("elevation_m") or 0)})
    return st


def daily_csv(years):
    out = {}
    for y in years:
        try:
            txt = http(ODP + "/data/stations/by_year/%d.csv" % y, timeout=180).decode("utf-8", "replace")
        except Exception as e:
            log.warning("datele zilnice %d nu sunt disponibile (%s)", y, e)
            continue
        lines = txt.splitlines()
        hdr = lines[0].split(",")
        ix = {k: hdr.index(k) for k in ("wsi", "date", "r", "tn", "tx")}
        qi = hdr.index("qc") if "qc" in hdr else None
        for ln in lines[1:]:
            a = ln.split(",")
            if len(a) < len(hdr):
                continue
            d = a[ix["date"]]
            # doar înregistrările validate (qc = 0, ca în exemplele ANM); -999 = lipsă
            if qi is not None and a[qi].strip() not in ("0", ""):
                continue
            rec = {}
            for k in ("r", "tn", "tx"):
                try:
                    v = float(a[ix[k]])
                    rec[k] = None if (not np.isfinite(v) or v <= -99) else v
                except ValueError:
                    rec[k] = None
            if rec["r"] is not None and rec["r"] < 0:
                rec["r"] = None
            out[(a[ix["wsi"]], d)] = rec
    return out


def edr_ids():
    j = json.loads(http(EDR + "/locations?bbox=20.2,43.6,29.9,48.4", timeout=180))
    return sorted({f.get("id") for f in j.get("features", []) if str(f.get("id", "")).startswith("0-20000-0-15")})


def edr_station(wsi):
    try:
        j = json.loads(http(EDR + "/locations/" + wsi, tries=3, timeout=60))
    except Exception as e:
        return wsi, None, str(e)
    cov = (j.get("coverages") or [j])[0]
    tv = cov.get("domain", {}).get("axes", {}).get("t", {}).get("values", [])
    rg = cov.get("ranges", {})

    def vals(prefix):
        for k, r in rg.items():
            if k.startswith(prefix):
                yield r.get("values", [])
    rows = {}
    for i, t in enumerate(tv):
        ws = [v[i] for v in vals("wind_speed:10.0") if i < len(v) and v[i] is not None]
        gs = [v[i] for v in vals("wind_speed_of_gust:10.0") if i < len(v) and v[i] is not None]
        ta = [v[i] for v in vals("air_temperature:") if i < len(v) and v[i] is not None]
        td = [v[i] for v in vals("dew_point_temperature:") if i < len(v) and v[i] is not None]
        wd = [v[i] for v in vals("wind_from_direction:10.0") if i < len(v) and v[i] is not None]
        pr = [v[i] for v in vals("precipitation_amount:1.5:sum:PT1H") if i < len(v) and v[i] is not None]
        if ws or gs or ta or pr:
            rows[t[:13]] = [max(ws) if ws else None, max(gs) if gs else None, ta[0] if ta else None,
                            wd[0] if wd else None, max(0.0, pr[0]) if pr else None, td[0] if td else None]
    return wsi, rows, None


def update_store():
    try:
        store = json.load(open(STORE, encoding="utf-8"))
    except Exception:
        store = {}
    ids = edr_ids()
    ok = 0
    with ThreadPoolExecutor(max_workers=8) as ex:
        for wsi, rows, err in ex.map(edr_station, ids):
            if rows is None:
                continue
            ok += 1
            store.setdefault(wsi, {}).update(rows)
    lim = (datetime.now(timezone.utc) - timedelta(days=DAYS + 2)).strftime("%Y-%m-%dT%H")
    for wsi in list(store):
        store[wsi] = {t: v for t, v in store[wsi].items() if t >= lim}
    tmp = STORE + ".tmp"
    json.dump(store, open(tmp, "w", encoding="utf-8"), separators=(",", ":"))
    os.replace(tmp, STORE)
    log.info("observații orare: %d stații citite din %d", ok, len(ids))
    return store


def wind_daily(store, d):
    """vânt maxim și rafală maximă (km/h) pe 06 UTC d – 06 UTC d+1; și numărul de ore acoperite"""
    t0 = datetime(d.year, d.month, d.day, 6, tzinfo=timezone.utc)
    keys = [(t0 + timedelta(hours=k)).strftime("%Y-%m-%dT%H") for k in range(1, 25)]
    res = {}
    for wsi, rows in store.items():
        ws = [rows[k][0] for k in keys if k in rows and rows[k][0] is not None]
        gs = [rows[k][1] for k in keys if k in rows and rows[k][1] is not None]
        nh = sum(1 for k in keys if k in rows)
        if nh:
            res[wsi] = (max(ws) * 3.6 if ws else None, max(max(gs), max(ws) if ws else 0) * 3.6 if gs else None, nh)
    return res



# ---------------- radar ANM (compozit la 10 minute, ultimele 48 h) ----------------
RADAR = ODP + "/data/radar/composite.zarr/"
RCACHE = os.path.join(HERE, "radar_ore2")         # cumulate orare ale compozitului ANM pe grila comună (mm)
_RM = 6378137.0


def zstd_dec(b):
    try:
        from compression import zstd             # Python 3.14+
        return zstd.decompress(b)
    except ImportError:
        import zstandard
        return zstandard.ZstdDecompressor().decompress(b, max_output_size=50_000_000)


def _radar_index(meta):
    a = meta.get("attributes", {})
    tr = a.get("spatial:transform", [1600, 0, 1780800, 0, -1600, 6505600])
    ny, nx = a.get("spatial:shape", [1028, 1209])
    X = _RM * np.radians(GLON)
    Y = _RM * np.log(np.tan(np.pi / 4 + np.radians(GLAT) / 2))
    col = np.floor((X - tr[2]) / tr[0]).astype(int)
    row = np.floor((Y - tr[5]) / tr[4]).astype(int)
    ok = (col >= 0) & (row >= 0) & (col < nx) & (row < ny)
    return row, col, ok, ny, nx


def radar_update():
    """cumulează radarul pe ore (ora se încheie la HH:00) și le salvează în radar_ore/"""
    os.makedirs(RCACHE, exist_ok=True)
    meta = json.loads(http(RADAR + "zarr.json"))
    am = json.loads(http(RADAR + "dbr/zarr.json"))
    att = am.get("attributes", {})
    sf, ao = float(att.get("scale_factor", 0.2)), float(att.get("add_offset", -20.2))
    times = np.frombuffer(zstd_dec(http(RADAR + "time/c/0")), dtype="<i8")
    n = int(am["shape"][0])
    times = times[:n]
    row, col, ok, ny, nx = _radar_index(meta)
    have = {f[:10] for f in os.listdir(RCACHE) if f.endswith(".npy")} | processed_hours()
    if not os.path.exists(os.path.join(RCACHE, "frecventa.npz")):
        fs = sorted(f for f in os.listdir(RCACHE) if f.endswith(".npy"))[-48:]
        for f_ in fs:
            clutter_freq_update(np.load(os.path.join(RCACHE, f_)).astype(np.float32))
        mark_processed([f_[:10] for f_ in fs])
    hours = {}
    for i, t in enumerate(times):
        if t <= 0:
            continue
        H = int(-(-int(t) // 3600) * 3600)                       # ora (UTC) la care se încheie intervalul
        hours.setdefault(H, []).append(i)
    now = time.time()
    done = 0
    for H in sorted(hours):
        key = datetime.fromtimestamp(H, timezone.utc).strftime("%Y%m%d%H")
        idx = hours[H]
        if key in have or H > now or len(idx) < 5:
            continue
        acc = np.zeros(GLON.shape); cnt = np.zeros(GLON.shape)
        for i in idx:
            try:
                raw = np.frombuffer(zstd_dec(http(RADAR + "dbr/c/%d/0/0" % i, tries=3)), dtype=np.uint8).reshape(ny, nx)
            except Exception as e:
                log.warning("radar: cadrul %d nu poate fi citit (%s)", i, e)
                continue
            v = np.full(GLON.shape, 255, np.uint8)
            v[ok] = raw[row[ok], col[ok]]
            R = np.where(v == 0, 0.0, 10 ** ((v.astype(float) * sf + ao) / 10.0))
            R = np.minimum(R, 103.8)          # plafonul de grindină NEXRAD (53 dBZ în Z = 300 R^1.4, Fulton et al. 1998)
            good = v != 255
            acc[good] += R[good]; cnt[good] += 1
        if cnt.max() < 5:
            continue
        mm = np.where(cnt >= 5, acc / np.maximum(cnt, 1), np.nan)        # medie mm/h (≥ 5 din 6 cadre) = mm în acea oră
        mm[mm < 0.05] = 0.0
        np.save(os.path.join(RCACHE, key + ".npy"), mm.astype(np.float16))
        clutter_freq_update(mm)
        mark_processed([key])
        done += 1
    lim = (datetime.now(timezone.utc) - timedelta(days=DAYS + 2)).strftime("%Y%m%d%H")
    for f in os.listdir(RCACHE):
        if f.endswith(".npy") and f[:10] < lim:
            os.remove(os.path.join(RCACHE, f))
    log.info("radar: %d ore noi cumulate (%d cadre în arhiva ANM)", done, len(times))


_CLUTTER = None


def processed_hours():
    try:
        return set(json.load(open(os.path.join(RCACHE, "procesate.json"), encoding="utf-8")))
    except Exception:
        return set()


def mark_processed(keys):
    lim = (datetime.now(timezone.utc) - timedelta(days=4)).strftime("%Y%m%d%H")
    s = {k for k in processed_hours() | set(keys) if k >= lim}
    json.dump(sorted(s), open(os.path.join(RCACHE, "procesate.json"), "w", encoding="utf-8"))


def clutter_freq_update(mm):
    """frecvența orelor cu „ploaie” în fiecare punct (medie glisantă pe ~2 zile), păstrată separat de datele radar,
       ca să rămână disponibilă după ștergerea orelor"""
    p = os.path.join(RCACHE, "frecventa.npz")
    wet = (np.nan_to_num(mm) > 0.1).astype(np.float32)
    try:
        with np.load(p) as d:
            f, n = d["f"].astype(np.float32), int(d["n"])
        if f.shape != wet.shape:
            raise ValueError
    except Exception:
        f, n = wet.copy(), 0
    n += 1
    a = max(1.0 / n, 1.0 / 48)
    f = (1 - a) * f + a * wet
    np.savez(p + ".tmp.npz", f=f, n=n)
    os.replace(p + ".tmp.npz", p)


_CLUTTER = None


def clutter_mask():
    """pixeli cu „ploaie” în peste jumătate din ore (ultimele ~2 zile) și mult mai des decât împrejurimile (~30 km)
       = ecouri fixe (sol, mare), nu precipitații"""
    global _CLUTTER
    if _CLUTTER is None:
        _CLUTTER = np.zeros(GLON.shape, bool)
        try:
            with np.load(os.path.join(RCACHE, "frecventa.npz")) as d:
                wet, n = d["f"].astype(np.float32), int(d["n"])
        except Exception:
            wet, n = None, 0
        if wet is None or n < 24:
            fs = sorted(f for f in os.listdir(RCACHE) if f.endswith(".npy"))[-48:] if os.path.isdir(RCACHE) else []
            if len(fs) >= 24:
                wet = np.mean([np.nan_to_num(np.load(os.path.join(RCACHE, f)).astype(np.float32)) > 0.1 for f in fs], axis=0)
                n = len(fs)
        if wet is not None and n >= 24:
            from numpy.lib.stride_tricks import sliding_window_view as swv
            p = 7
            med = np.median(swv(np.pad(wet, p, mode="edge"), (2 * p + 1, 2 * p + 1)), axis=(-1, -2))
            _CLUTTER = (wet > 0.5) & (wet - med > 0.3)
            log.info("radar: %d pixeli cu ecouri fixe excluși (%.1f%% din grilă)", int(_CLUTTER.sum()), 100 * _CLUTTER.mean())
    return _CLUTTER


def radar_hour(T):
    p = os.path.join(RCACHE, T.strftime("%Y%m%d%H") + ".npy")
    if not os.path.exists(p):
        return None
    a = np.load(p).astype(np.float32)
    a[clutter_mask()] = np.nan
    return a


def radar_sum(t0, t1):
    """mm de la t0 la t1 (ore întregi, UTC); None dacă lipsește vreo oră"""
    out = None
    T = t0 + timedelta(hours=1)
    while T <= t1:
        a = radar_hour(T)
        if a is None:
            return None
        out = a if out is None else out + a
        T += timedelta(hours=1)
    return out



# ---------------- interpolare geostatistică ----------------
KXC = np.cos(np.radians(46.0)) * 111.32


def _km(lon, lat):
    return np.asarray(lon, dtype=np.float64) * KXC, np.asarray(lat, dtype=np.float64) * 110.57


class Kriging:
    """kriging ordinar (Journel & Huijbregts 1978) cu variogramă exponențială ajustată pe date (pepită, prag, rază)"""

    def __init__(self, x, y, z):
        self.x, self.y, self.z = x, y, z
        D = np.hypot(x[:, None] - x[None, :], y[:, None] - y[None, :])
        iu = np.triu_indices(len(z), 1)
        d = D[iu]; g = 0.5 * (z[iu[0]] - z[iu[1]]) ** 2
        bins = np.linspace(0, 250, 16)
        cls = np.digitize(d, bins)
        hd = np.array([d[cls == k].mean() for k in range(1, 16) if (cls == k).sum() >= 10])
        hg = np.array([g[cls == k].mean() for k in range(1, 16) if (cls == k).sum() >= 10])
        var = float(np.var(z))
        self.const = var <= 1e-9 or len(hd) < 4
        if self.const:
            return
        best = None
        for rng in (10, 20, 30, 45, 60, 80, 110, 150, 200, 300):
            for nug in (0.0, 0.05, 0.1, 0.2, 0.35, 0.5):
                for sill in (0.6, 0.8, 1.0, 1.2, 1.5):
                    m = var * (nug + (sill - nug) * (1 - np.exp(-3 * hd / rng)))
                    err = float(((m - hg) ** 2).sum())
                    if best is None or err < best[0]:
                        best = (err, rng, nug * var, sill * var)
        _, self.rng, self.c0, self.c1 = best
        n = len(z)
        A = np.ones((n + 1, n + 1)); A[:n, :n] = self.gam(D); A[n, n] = 0.0
        self.Ainv = np.linalg.pinv(A)

    def gam(self, h):
        return np.where(h > 0, self.c0 + (self.c1 - self.c0) * (1 - np.exp(-3 * h / self.rng)), 0.0)

    def predict(self, px, py):
        if self.const:
            return np.full(np.shape(px), float(np.mean(self.z))), None
        px = np.asarray(px, dtype=np.float64).ravel(); py = np.asarray(py, dtype=np.float64).ravel()
        n = len(self.z)
        out = np.empty(px.size); dmin = np.empty(px.size)
        for k0 in range(0, px.size, 20000):
            dd = np.hypot(px[k0:k0 + 20000, None] - self.x[None, :], py[k0:k0 + 20000, None] - self.y[None, :])
            b = np.ones((dd.shape[0], n + 1)); b[:, :n] = self.gam(dd)
            w = b @ self.Ainv.T
            out[k0:k0 + 20000] = w[:, :n] @ self.z
            dmin[k0:k0 + 20000] = dd.min(1)
        return out, dmin

    def loo(self):
        """valorile prezise în fiecare stație fără acea stație (formula lui Dubrule 1983, exactă pentru kriging)"""
        if self.const:
            n = len(self.z)
            return (self.z.sum() - self.z) / max(n - 1, 1)
        n = len(self.z)
        b = np.append(self.z, 0.0)
        e = self.Ainv @ b
        return self.z - e[:n] / np.diag(self.Ainv)[:n]


def ok_grid(lon, lat, vals, maxd=None):
    v = np.asarray(vals, dtype=np.float64); ok = np.isfinite(v)
    if ok.sum() < 12:
        return None
    x, y = _km(np.asarray(lon)[ok], np.asarray(lat)[ok])
    K = Kriging(x, y, v[ok])
    gx, gy = _km(GLON, GLAT)
    out, dmin = K.predict(gx, gy)
    if maxd and dmin is not None:
        out[dmin > maxd] = np.nan
    return out.reshape(GLON.shape).astype(np.float32)


def rk_fit(lon, lat, z, vals):
    """kriging cu regresie (Hengl et al. 2007; Odeh et al. 1995): tendința liniară după altitudine, latitudine și
       longitudine, ajustată în fiecare zi (deci și gradientul termic, inclusiv inversiunile), plus kriging ordinar
       pe reziduuri"""
    v = np.asarray(vals, dtype=np.float64); ok = np.isfinite(v)
    if ok.sum() < 15:
        return None
    lo, la, zz = np.asarray(lon)[ok], np.asarray(lat)[ok], np.asarray(z, dtype=np.float64)[ok]
    X = np.column_stack([np.ones(ok.sum()), zz / 1000.0, la - 46.0, lo - 25.0])
    beta, *_ = np.linalg.lstsq(X, v[ok], rcond=None)
    res = v[ok] - X @ beta
    x, y = _km(lo, la)
    return {"beta": beta, "K": Kriging(x, y, res), "ok": ok, "X": X, "v": v[ok], "x": x, "y": y}


def rk_grid(m, zf):
    X = np.column_stack([np.ones(GLON.size), zf.ravel() / 1000.0, GLAT.ravel() - 46.0, GLON.ravel() - 25.0])
    gx, gy = _km(GLON, GLAT)
    r, _ = m["K"].predict(gx, gy)
    return (X @ m["beta"] + r).reshape(GLON.shape).astype(np.float32)


def rk_loo(m):
    """validare încrucișată „lasă una afară”: regresia și krigingul refăcute fără stația respectivă"""
    X, v, x, y = m["X"], m["v"], m["x"], m["y"]
    n = len(v); pred = np.empty(n)
    K = m["K"]
    for i in range(n):
        keep = np.arange(n) != i
        b, *_ = np.linalg.lstsq(X[keep], v[keep], rcond=None)
        res = v[keep] - X[keep] @ b
        if K.const:
            pred[i] = X[i] @ b + res.mean(); continue
        D = np.hypot(x[keep][:, None] - x[keep][None, :], y[keep][:, None] - y[keep][None, :])
        A = np.ones((n, n)); A[:n - 1, :n - 1] = K.gam(D); A[n - 1, n - 1] = 0.0
        bb = np.ones(n); bb[:n - 1] = K.gam(np.hypot(x[keep] - x[i], y[keep] - y[i]))
        w = np.linalg.solve(A, bb)
        pred[i] = X[i] @ b + w[:n - 1] @ res
    return pred


def idw_loo(lon, lat, vals, z=None, lapse=0.0):
    v = np.asarray(vals, dtype=np.float64); ok = np.isfinite(v)
    lo, la = np.asarray(lon)[ok], np.asarray(lat)[ok]; vv = v[ok]
    if lapse:
        vv = vv + lapse * np.asarray(z, dtype=np.float64)[ok]
    x, y = _km(lo, la)
    D = np.hypot(x[:, None] - x[None, :], y[:, None] - y[None, :]); np.fill_diagonal(D, np.inf)
    k = min(8, len(vv) - 1)
    idx = np.argpartition(D, k - 1, axis=1)[:, :k]
    dd = np.take_along_axis(D, idx, 1); w = 1.0 / np.maximum(dd, 1.0) ** 2
    p = (w * vv[idx]).sum(1) / w.sum(1)
    if lapse:
        p = p - lapse * np.asarray(z, dtype=np.float64)[ok]
    return p, v[ok]


def stats(pred, obs):
    e = np.asarray(pred) - np.asarray(obs)
    return "EMA %.2f, eroare medie %+.2f, RMSE %.2f (n=%d)" % (np.mean(np.abs(e)), np.mean(e), np.sqrt(np.mean(e ** 2)), len(e))


# ---------------- granița României ----------------
_MASK = None


def ro_mask():
    """punctele grilei din România: aceleași cu ale gridului oficial ANM (unde gridul are valori); salvată local"""
    global _MASK
    if _MASK is not None:
        return _MASK
    p = os.path.join(HERE, "masca_romania.npy")
    if os.path.exists(p):
        m = np.load(p)
        if m.shape == GLON.shape:
            _MASK = m
            return m
    today = datetime.now(timezone.utc).date()
    for k in range(2, 15):
        try:
            g = cog_to_grid(ODP + "/data/grid/cog/tmax/%s.tif" % (today - timedelta(days=k)).isoformat())
            if np.isfinite(g).sum() > 30000:
                _MASK = np.isfinite(g)
                np.save(p, _MASK)
                log.info("masca României: %d puncte ale grilei (din gridul ANM)", int(_MASK.sum()))
                return _MASK
        except Exception:
            continue
    raise RuntimeError("masca României nu poate fi construită (gridul ANM nu e disponibil)")


def clip_ro(a):
    return None if a is None else np.where(ro_mask(), a, np.nan).astype(np.float32)


# ---------------- precipitații radar: estimarea polarimetrică proprie + compozitul ANM ----------------
QPE_DIR = os.path.join(HERE, "qpe")        # cumulul orar polarimetric scris de radar_galati.py (Medgidia, Bârnova, București)


def qpe_hour(T):
    """mm în ora încheiată la T, din estimarea polarimetrică proprie (NaN unde nu e validă); None dacă lipsește ora"""
    p = os.path.join(QPE_DIR, "ro_%s.npz" % T.strftime("%Y%m%d%H"))
    if not os.path.exists(p):
        return None
    try:
        with np.load(p) as d:
            a = d["mm"].astype(np.float32)
        return a if a.shape == GLON.shape else None
    except Exception:
        return None


def radar_pair(T):
    """(estimarea proprie, compozitul ANM) pentru ora încheiată la T"""
    return qpe_hour(T), radar_hour(T)


def day_radar(t0):
    """24 de ore (06–06 UTC): suma radar și sursa în fiecare punct — 1 = estimarea polarimetrică proprie (toate cele 24
       de ore valide), 2 = compozitul ANM (toate cele 24 de ore), 0 = necunoscut; plus orele, pentru împărțirea pe ore"""
    own, anm = [], []
    for k in range(1, 25):
        a, b = radar_pair(t0 + timedelta(hours=k))
        own.append(a); anm.append(b)
    nan = np.full(GLON.shape, np.nan, np.float32)
    O = np.stack([a if a is not None else nan for a in own])
    A = np.stack([b if b is not None else nan for b in anm])
    o24 = O.sum(0); a24 = A.sum(0)                                  # NaN dacă lipsește vreo oră
    src = np.where(np.isfinite(o24), 1, np.where(np.isfinite(a24), 2, 0)).astype(np.uint8)
    R24 = np.where(src == 1, o24, np.where(src == 2, a24, np.nan)).astype(np.float32)
    H = np.where((src == 1)[None], O, np.where((src == 2)[None], A, np.nan)).astype(np.float32)
    return R24, src, H


def gauge_cells(slon, slat):
    j = np.clip(np.round((np.asarray(slat) - LAT0) / DLAT).astype(int), 0, CH - 1)
    i = np.clip(np.round((np.asarray(slon) - LON0) / DLON).astype(int), 0, CW - 1)
    return j, i


def source_factors(R, src, slon, slat, G):
    """factorul mediu pluviometre/radar (Wilson & Brandes 1979), separat pentru fiecare sursă radar,
       din perechile în care măcar unul are > 0,1 mm; nevoie de ≥ 10 perechi și ≥ 5 mm radar"""
    G = np.asarray(G, dtype=np.float64)
    j, i = gauge_cells(slon, slat)
    Rs = R[j, i].astype(np.float64); Ss = src[j, i]
    out = {}
    for s in (1, 2):
        ok = (Ss == s) & np.isfinite(G) & np.isfinite(Rs) & ((G > 0.1) | (Rs > 0.1))
        if ok.sum() >= 10 and Rs[ok].sum() >= 5:
            out[s] = float(G[ok].sum() / Rs[ok].sum())
    return out


def merge_cm(R, src, slon, slat, G, ds=""):
    """îmbinare radar–pluviometre: 1) factorul mediu pe fiecare sursă radar; 2) „conditional merging”
       (Ehret 2002; Sinclair & Pegram 2005): câmp = kriging(pluviometre) + [radar − kriging(radar în punctele
       pluviometrelor)] — pluviometrele dau nivelul, radarul structura dintre ele; unde nu e radar: kriging(pluviometre)"""
    G = np.asarray(G, dtype=np.float64)
    f = source_factors(R, src, slon, slat, G)
    Ra = R.copy()
    for s, v in f.items():
        Ra = np.where(src == s, R * v, Ra)
    j, i = gauge_cells(slon, slat)
    Rs = Ra[j, i].astype(np.float64)
    okg = np.isfinite(G)
    if okg.sum() < 12:
        return None, f, 0
    lo, la = np.asarray(slon)[okg], np.asarray(slat)[okg]
    x, y = _km(lo, la)
    KG = Kriging(x, y, G[okg])
    gx, gy = _km(GLON, GLAT)
    Gk = KG.predict(gx, gy)[0].reshape(GLON.shape)
    okr = okg & np.isfinite(Rs)
    out = np.maximum(Gk, 0.0)
    n = int(okr.sum())
    if n >= 12:
        xr, yr = _km(np.asarray(slon)[okr], np.asarray(slat)[okr])
        KR = Kriging(xr, yr, Rs[okr])
        Rk = KR.predict(gx, gy)[0].reshape(GLON.shape)
        out = np.where(np.isfinite(Ra), np.maximum(Gk + (Ra - Rk), 0.0), np.maximum(Gk, 0.0))
        # validare „lasă una afară” în punctele pluviometrelor cu radar (Dubrule 1983 pentru ambele kriginguri)
        try:
            KG2 = Kriging(xr, yr, G[okr])
            cm = np.maximum(KG2.loo() + Rs[okr] - KR.loo(), 0.0)
            log.info("p24 %s — validare încrucișată la %d pluviometre: îmbinare radar+stații %s | doar stații (kriging) %s | doar radar %s; factori pluviometre/radar %s",
                     ds, n, stats(cm, G[okr]), stats(np.maximum(KG2.loo(), 0), G[okr]), stats(Rs[okr], G[okr]),
                     ", ".join("%s %.2f" % ({1: "polarimetric", 2: "compozit ANM"}[s], v) for s, v in f.items()) or "–")
        except Exception as e:
            log.info("validarea încrucișată nu a putut fi făcută (%s)", e)
    return out.astype(np.float32), f, n


# ---------------- interpolare din stații (până apare gridul ANM) ----------------
def idw(st_lon, st_lat, vals, zf=None, st_z=None, lapse=0.0, maxd=70.0):
    v = np.asarray(vals, dtype=np.float64)
    ok = np.isfinite(v)
    if ok.sum() < 8:
        return None
    lo = np.asarray(st_lon)[ok]; la = np.asarray(st_lat)[ok]; v = v[ok]
    if lapse:
        v = v + lapse * np.asarray(st_z)[ok]
    kx = np.cos(np.radians(46.0)) * 111.32
    gx = GLON.ravel()[:, None]; gy = GLAT.ravel()[:, None]
    d = np.hypot((gx - lo[None, :]) * kx, (gy - la[None, :]) * 110.57)
    k = min(8, len(v))
    idx = np.argpartition(d, k - 1, axis=1)[:, :k]
    dd = np.take_along_axis(d, idx, axis=1)
    w = 1.0 / np.maximum(dd, 1.0) ** 2
    out = (w * v[idx]).sum(1) / w.sum(1)
    out[dd.min(1) > maxd] = np.nan
    out = out.reshape(GLON.shape)
    if lapse:
        out = out - lapse * zf
    return out.astype(np.float32)


# ---------------- scriere ----------------
def med_residual(x):
    a = np.zeros_like(x); b = np.zeros_like(x); c = np.zeros_like(x)
    a[:, 1:] = x[:, :-1]; b[1:, :] = x[:-1, :]; c[1:, 1:] = x[:-1, :-1]
    mx = np.maximum(a, b); mn = np.minimum(a, b)
    p = np.where(c >= mx, mn, np.where(c <= mn, mx, a + b - c))
    p[0, 1:] = x[0, :-1]; p[1:, 0] = x[:-1, 0]; p[0, 0] = 0
    return x - p


def pack_residual(r):
    z = (r << 1) ^ (r >> 63)
    if z.max() >= 65536:
        raise ValueError("valori în afara intervalului")
    z = z.astype(np.uint16).ravel()
    return np.concatenate([(z & 255).astype(np.uint8), (z >> 8).astype(np.uint8)]).tobytes()


def enc_field(v, st):
    v = np.where(np.isfinite(v), v, MISSING).astype(np.float64)
    k = np.round(v / st).astype(np.int64)
    k0 = int(k.min())
    return k0, st, base64.b64encode(gzip.compress(pack_residual(med_residual(k - k0)), 9)).decode()


def write_js(path, var, key, obj):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("window.%s=window.%s||{};window.%s[%s]=" % (var, var, var, json.dumps(key))
                 + json.dumps(obj, separators=(",", ":")) + ";\n")


def r1(x, n=1):
    return None if x is None or not np.isfinite(x) else round(float(x), n)


# ---------------- rezultatele păstrate și ștergerea datelor radar ----------------
RES_DIR = os.path.join(HERE, "rezultate_precipitatii")


def disaggregate(P, R24, RH):
    """totalul zilei P împărțit pe cele 24 de ore după ponderile radar RH/R24 (Lewis et al. 2018); unde radarul
       nu are precipitații dar P > 0: uniform; unde nu e radar: necunoscut"""
    H = np.where((np.isfinite(R24) & (R24 > 0.05))[None], P[None] * RH / np.maximum(R24, 0.05)[None],
                 np.where(np.isfinite(R24)[None], P[None] / 24.0, np.nan))
    return np.maximum(H, 0).astype(np.float32)


def load_result(ds):
    p = os.path.join(RES_DIR, "zi_%s.npz" % ds)
    if not os.path.exists(p):
        return None
    try:
        with np.load(p, allow_pickle=False) as d:
            return {"P": d["P"].astype(np.float32), "H": d["H"].astype(np.float32), "src": str(d["src"]),
                    "rsrc": d["rsrc"].astype(np.uint8), "fac": {int(k): float(v) for k, v in json.loads(str(d["fac"])).items()}}
    except Exception as e:
        log.warning("rezultatul zilei %s nu poate fi citit (%s)", ds, e)
        return None


def save_result(ds, P, H, src_, rsrc, fac):
    os.makedirs(RES_DIR, exist_ok=True)
    p = os.path.join(RES_DIR, "zi_%s.npz" % ds)
    fac = {int(k): float(v) for k, v in (fac or {}).items()}
    np.savez_compressed(p + ".tmp.npz", P=P, H=H, src=np.array(src_), rsrc=rsrc, fac=np.array(json.dumps(fac)))
    os.replace(p + ".tmp.npz", p)
    log.info("precipitații %s: rezultatul (%s) păstrat — total zilnic și cele 24 de ore", ds, src_)
    return {"P": P, "H": H, "src": src_, "rsrc": rsrc, "fac": fac}


def drop_radar_hours(t0, ds):
    """după îmbinarea cu pluviometrele, orele radar ale zilei nu mai sunt necesare: se șterg (rămâne rezultatul)"""
    n = 0
    for k in range(1, 25):
        key = (t0 + timedelta(hours=k)).strftime("%Y%m%d%H")
        for p in (os.path.join(QPE_DIR, "ro_%s.npz" % key), os.path.join(RCACHE, key + ".npy")):
            if os.path.exists(p):
                try:
                    os.remove(p); n += 1
                except OSError as e:
                    log.warning("nu pot șterge %s (%s)", p, e)
        mark_processed([key])
    log.info("precipitații %s: %d fișiere radar orare șterse după îmbinare", ds, n)


def cleanup_results(days):
    keep = {d.isoformat() for d in days}
    if os.path.isdir(RES_DIR):
        for nm in os.listdir(RES_DIR):
            m = re.match(r"zi_(\d{4}-\d{2}-\d{2})\.npz$", nm)
            if m and m.group(1) not in keep and m.group(1) < min(keep):
                os.remove(os.path.join(RES_DIR, nm))
    # nicio oră radar mai veche de 48 h nu se păstrează
    lim = (datetime.now(timezone.utc) - timedelta(hours=48)).strftime("%Y%m%d%H")
    for d_, pre in ((QPE_DIR, "ro_"), (RCACHE, "")):
        if os.path.isdir(d_):
            for nm in os.listdir(d_):
                m = re.match(pre + r"(\d{10})\.np[yz]$", nm)
                if m and m.group(1) < lim:
                    os.remove(os.path.join(d_, nm))


def update():
    zf = relief()
    st = stations()
    now = datetime.now(timezone.utc)
    today = now.date()
    days = [today - timedelta(days=k) for k in range(DAYS - 1, -1, -1)]
    store = {}
    try:
        store = update_store()
    except Exception as e:
        log.warning("observațiile orare nu pot fi citite acum (%s)", e)
        try:
            store = json.load(open(STORE, encoding="utf-8"))
        except Exception:
            store = {}
    try:
        radar_update()
    except Exception as e:
        log.warning("compozitul radar ANM nu poate fi citit acum (%s)", e)
    ro_mask()
    daily = daily_csv(sorted({d.year for d in days} | {(days[-1] + timedelta(days=1)).year}))
    slon = [s["lon"] for s in st]; slat = [s["lat"] for s in st]; sz = [s["z"] for s in st]
    run0 = datetime(days[0].year, days[0].month, days[0].day, tzinfo=timezone.utc)
    tmp = DATA + "_nou"
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp)
    entries, srcs, stv, sth = {}, {}, {}, {}
    dayP = {}                # ziua climatologică → (P24 îmbinat, R24, sursa, orele radar), pentru împărțirea pe ore
    last_f = {}              # factorii pluviometre/radar ai ultimei zile încheiate (pentru orele provizorii)
    for d in days:
        ds = d.isoformat()
        f = {}
        src = {}
        rec = {s["id"]: daily.get((s["id"], ds)) or {} for s in st}
        jj, ii = gauge_cells(slon, slat)
        # gridul ANM: Tmax/Tmin poartă data zilei; precipitațiile poartă data de SFÂRȘIT a intervalului 06–06 UTC
        # (verificat: gridul din ziua D+1 = pluviometrele din ziua D, care acoperă 06 UTC D – 06 UTC D+1).
        # Gridul e folosit doar dacă se potrivește cu propriile stații ANM (control al calității).
        for key, var, col, gd, lim in (("tx", "tmax", "tx", d, 1.5), ("tn", "tmin", "tn", d, 1.5),
                                       ("p24", "precip", "r", d + timedelta(days=1), None)):
            try:
                g = cog_to_grid(ODP + "/data/grid/cog/%s/%s.tif" % (var, gd.isoformat()))
            except Exception:
                continue
            if np.isfinite(g).sum() <= 10000:
                continue
            sv_ = np.array([rec[s["id"]].get(col) if rec[s["id"]].get(col) is not None else np.nan for s in st], float)
            gv = g[jj, ii]
            ok_ = np.isfinite(sv_) & np.isfinite(gv)
            if ok_.sum() >= MIN_ST:
                mae = float(np.mean(np.abs(gv[ok_] - sv_[ok_])))
                thr = lim if lim is not None else max(1.0, 0.25 * float(np.mean(sv_[ok_])))
                if mae > thr:
                    log.warning("%s %s: gridul ANM diferă de stațiile ANM cu %.2f în medie (prag %.2f) — nu îl folosesc, interpolez din stații",
                                key, ds, mae, thr)
                    continue
                log.info("%s %s: gridul ANM față de stațiile ANM — diferență medie absolută %.2f (n=%d)", key, ds, mae, int(ok_.sum()))
            f[key] = g; src[key] = "grid"
        t0 = datetime(d.year, d.month, d.day, 6, tzinfo=timezone.utc)
        g_r = [rec[s["id"]].get("r") if rec[s["id"]].get("r") is not None else np.nan for s in st]
        ng = sum(1 for v in g_r if np.isfinite(v))
        res = load_result(ds)
        closed_p = now >= t0 + timedelta(days=1, minutes=20)
        R24 = rsrc = RH = None
        if closed_p and (res is None or (res["src"] == "radar-provizoriu" and ng >= MIN_ST)):
            R24, rsrc, RH = day_radar(t0)
            if not np.isfinite(R24).any():
                R24 = rsrc = RH = None
            if R24 is None and res is not None:            # orele radar au fost deja șterse: rezultatul provizoriu e câmpul radar
                R24, rsrc, RH = res["P"], res["rsrc"], res["H"]
        if R24 is not None:
            if ng >= MIN_ST:
                m, fac, n = merge_cm(R24, rsrc, slon, slat, g_r, ds)
                if m is not None:
                    res = save_result(ds, clip_ro(m), disaggregate(clip_ro(m), R24, RH), "radar+statii", rsrc, fac)
                    drop_radar_hours(t0, ds)
            elif now >= t0 + timedelta(days=2):
                # pluviometrele întârzie peste 24 h de la sfârșitul zilei: păstrez câmpul radar corectat cu ultimul factor,
                # înainte ca orele radar să depășească 48 h (se reîmbină când apar pluviometrele)
                Rp = np.where(rsrc == 1, R24 * last_f.get(1, 1.0), R24 * last_f.get(2, 1.0)).astype(np.float32)
                res = save_result(ds, clip_ro(Rp), disaggregate(clip_ro(Rp), R24, RH), "radar-provizoriu", rsrc, {})
                drop_radar_hours(t0, ds)
        if res is not None and res.get("fac"):
            last_f = res["fac"]
        if "p24" in f:
            if res is not None:                            # gridul ANM, împărțit pe ore după rezultatul păstrat
                dayP[ds] = (clip_ro(f["p24"]), disaggregate(clip_ro(f["p24"]), res["P"], res["H"]))
        elif res is not None and res["src"] == "radar+statii":
            f["p24"] = res["P"]; src["p24"] = "radar+statii"; dayP[ds] = (res["P"], res["H"])
        elif ng >= MIN_ST:
            g = ok_grid(slon, slat, g_r)
            if g is not None:
                f["p24"] = np.maximum(g, 0); src["p24"] = "statii"
        for key, col in (("tx", "tx"), ("tn", "tn")):
            vals = [rec[s["id"]].get(col) if rec[s["id"]].get(col) is not None else np.nan for s in st]
            if sum(1 for v in vals if np.isfinite(v)) < MIN_ST:
                continue
            m = rk_fit(slon, slat, sz, vals)
            if m is None:
                continue
            # metoda se alege zilnic prin validare încrucișată „lasă una afară”: kriging cu regresie sau IDW + 6,5 °C/km
            best = "rk"
            try:
                pr = rk_loo(m)
                pi, ob = idw_loo(slon, slat, vals, sz, LAPSE)
                best = "rk" if np.mean(np.abs(pr - m["v"])) <= np.mean(np.abs(pi - ob)) else "idw"
                gr = rk_grid(m, zf) if best == "rk" else idw(slon, slat, vals, zf, sz, LAPSE, maxd=1e9)
                extra = ""
                if key in f:
                    both = ro_mask() & np.isfinite(f[key]) & np.isfinite(gr)
                    extra = "; metoda aleasă față de gridul ANM: diferență medie absolută %.2f °C, medie %+.2f °C" % (
                        float(np.mean(np.abs(gr[both] - f[key][both]))), float(np.mean(gr[both] - f[key][both])))
                log.info("%s %s — validare încrucișată: kriging cu regresie %s | IDW+6,5 °C/km %s; gradient zilnic %.1f °C/km; aleasă: %s%s",
                         key, ds, stats(pr, m["v"]), stats(pi, ob), m["beta"][1], "kriging cu regresie" if best == "rk" else "IDW", extra)
            except Exception as e:
                log.info("%s %s: validarea nu a putut fi făcută (%s)", key, ds, e)
                gr = rk_grid(m, zf)
            if key not in f:
                f[key] = gr; src[key] = "statii"
        wd = wind_daily(store, d)
        for key, n in (("wx", 0), ("gx", 1)):
            vals = [(wd[s["id"]][n] if s["id"] in wd and wd[s["id"]][n] is not None else np.nan) for s in st]
            if sum(1 for v in vals if np.isfinite(v)) >= MIN_ST:
                f[key] = idw(slon, slat, vals, maxd=60.0)
        closed = now >= datetime(d.year, d.month, d.day, 6, tzinfo=timezone.utc) + timedelta(days=1, hours=1)
        if wd:
            src["wx"] = src["gx"] = "statii" + ("" if closed else "-partial")
        sv = {"tx": [], "tn": [], "r": [], "wx": [], "gx": []}
        for s in st:
            r = rec[s["id"]]
            sv["tx"].append(r1(r.get("tx"))); sv["tn"].append(r1(r.get("tn"))); sv["r"].append(r1(r.get("r")))
            w = wd.get(s["id"])
            sv["wx"].append(r1(w[0], 0) if w and w[0] is not None else None)
            sv["gx"].append(r1(w[1], 0) if w and w[1] is not None else None)
        if not f and not wd:
            continue
        h = int((datetime(d.year, d.month, d.day, 12, tzinfo=timezone.utc) - run0).total_seconds() // 3600)
        e = entries.setdefault(h, {"h": h, "f": {}, "src": {}})
        e["day"] = ds; e["src"].update(src)
        for key in ("tx", "tn", "p24", "wx", "gx"):
            e["f"][key] = clip_ro(f[key]) if key in f else np.full((CH, CW), np.nan, np.float32)
        srcs[ds] = src; stv[ds] = sv
        log.info("%s: %s", ds, ", ".join("%s=%s" % (k, src.get(k, "–")) for k in FIELDS))
    # observații orare: temperatura (kriging cu regresie), vântul, rafala; precipitațiile 1 h din radar
    t_end = now.replace(minute=0, second=0, microsecond=0)
    for k in range(HOURLY_H - 1, -1, -1):
        T = t_end - timedelta(hours=k)
        if T < run0:
            continue
        key = T.strftime("%Y-%m-%dT%H")
        rows = [store.get(s["id"], {}).get(key) for s in st]
        own, anm = radar_pair(T)
        D = (T - timedelta(hours=6, minutes=1)).date().isoformat()
        if sum(1 for x in rows if x) < 20 and own is None and anm is None and D not in dayP:
            continue
        col = lambda n: [(x[n] if x and len(x) > n and x[n] is not None else np.nan) for x in rows]
        ta, ws, gs, wd = col(2), col(0), col(1), col(3)
        h = int((T - run0).total_seconds() // 3600)
        e = entries.setdefault(h, {"h": h, "f": {}, "src": {}})
        m = rk_fit(slon, slat, sz, ta)
        if m is not None:
            try:
                pi, ob = idw_loo(slon, slat, ta, sz, LAPSE)
                use_rk = np.mean(np.abs(rk_loo(m) - m["v"])) <= np.mean(np.abs(pi - ob))
            except Exception:
                use_rk = True
            g = rk_grid(m, zf) if use_rk else idw(slon, slat, ta, zf, sz, LAPSE, maxd=1e9)
            e["f"]["t"] = clip_ro(g); e["src"]["t"] = "statii"
        # precipitații 1 h: ziua încheiată și îmbinată cu pluviometrele → împărțită pe ore după radar (Lewis et al. 2018,
        # CEH-GEAR1hr); altfel radar × factorul pluviometre/radar al ultimei zile (provizoriu)
        if D in dayP:
            hi = int(round((T - datetime.fromisoformat(D).replace(tzinfo=timezone.utc) - timedelta(hours=6)).total_seconds() / 3600)) - 1
            e["f"]["pr"] = clip_ro(dayP[D][1][hi]); e["src"]["pr"] = "radar+statii-zi"
        elif own is not None or anm is not None:
            nan = np.full(GLON.shape, np.nan, np.float32)
            o = own if own is not None else nan; a = anm if anm is not None else nan
            R = np.where(np.isfinite(o), o * last_f.get(1, 1.0), a * last_f.get(2, 1.0))
            e["f"]["pr"] = clip_ro(R); e["src"]["pr"] = "radar-provizoriu"
        kmh = [v * 3.6 for v in ws]
        if sum(1 for v in kmh if np.isfinite(v)) >= MIN_ST:
            e["f"]["w"] = clip_ro(idw(slon, slat, kmh, maxd=60.0)); e["src"]["w"] = "statii"
            uu = [(-s_ * np.sin(np.radians(d_)) if np.isfinite(s_) and np.isfinite(d_) else np.nan) for s_, d_ in zip(ws, wd)]
            vv = [(-s_ * np.cos(np.radians(d_)) if np.isfinite(s_) and np.isfinite(d_) else np.nan) for s_, d_ in zip(ws, wd)]
            if sum(1 for v in uu if np.isfinite(v)) >= MIN_ST:
                e["f"]["u"] = clip_ro(idw(slon, slat, uu, maxd=60.0)); e["f"]["v"] = clip_ro(idw(slon, slat, vv, maxd=60.0))
        gk = [v * 3.6 for v in gs]
        if sum(1 for v in gk if np.isfinite(v)) >= MIN_ST:
            e["f"]["g"] = clip_ro(idw(slon, slat, gk, maxd=60.0)); e["src"]["g"] = "statii"
        e["time"] = key
        sth[key] = {"t": [r1(v) for v in ta], "w": [r1(v * 3.6, 0) for v in ws], "g": [r1(v * 3.6, 0) for v in gs],
                    "wd": [r1(v, 0) for v in wd], "pr": [None] * len(st)}
    # verificare: suma orelor = totalul zilnic, pentru zilele împărțite pe ore
    for D, (P, _H) in dayP.items():
        hs = []
        t0 = datetime.fromisoformat(D).replace(tzinfo=timezone.utc) + timedelta(hours=6)
        for k in range(1, 25):
            hh = int((t0 + timedelta(hours=k) - run0).total_seconds() // 3600)
            if hh in entries and "pr" in entries[hh]["f"] and entries[hh]["src"].get("pr") == "radar+statii-zi":
                hs.append(entries[hh]["f"]["pr"])
        if len(hs) == 24:
            S24 = np.sum(hs, 0); ok = np.isfinite(S24) & np.isfinite(P)
            log.info("verificare %s: suma celor 24 de ore față de totalul zilnic — diferență maximă %.3f mm pe %d puncte",
                     D, float(np.max(np.abs(S24[ok] - P[ok]))) if ok.any() else 0.0, int(ok.sum()))
    cleanup_results(days)
    hours = sorted(entries)
    for h in hours:
        e = entries[h]
        out = {"h": h, "day": e.get("day"), "time": e.get("time"), "src": e["src"], "f": {}}
        for key, arr in e["f"].items():
            k0, stp, dd = enc_field(arr, STEP[key])
            out["f"][key] = {"k0": k0, "st": stp, "d": dd}
        write_js(os.path.join(tmp, "h%02d.js" % h), "ALARO_DATA", h, out)
    log.info("observații orare: %d ore (%s … %s)", len(sth), min(sth) if sth else "-", max(sth) if sth else "-")
    if not hours:
        raise RuntimeError("nu există încă date")
    with open(os.path.join(tmp, "stations.js"), "w", encoding="utf-8") as fh:
        fh.write("window.OBS_ST=" + json.dumps({"st": [[s["id"], s["name"], s["lon"], s["lat"], s["z"]] for s in st],
                                                "d": stv, "h": sth}, separators=(",", ":"), ensure_ascii=False) + ";\n")
    k0, stp, dd = enc_field(zf, 1)
    with open(os.path.join(tmp, "orog.js"), "w", encoding="utf-8") as fh:
        fh.write("window.ALARO_OROG=" + json.dumps({"w": CW, "h": CH, "k0": k0, "st": stp, "d": dd}) + ";\n")
    meta = {"format": FORMAT, "model": "anm", "run": run0.strftime("%Y%m%d%H"), "hours": hours, "pint": [[h - 1, h] for h in hours],
            "levels": [], "days": [d.isoformat() for d in days if d.isoformat() in srcs], "src": srcs,
            "grid": {"w": CW, "h": CH, "lon0": LON0, "lat0": LAT0, "dlon": DLON, "dlat": DLAT},
            "updated": now.strftime("%Y-%m-%dT%H:%M:%SZ")}
    sig = json.dumps([meta["days"], srcs, stv, sth], sort_keys=True)
    with open(os.path.join(tmp, "meta.js"), "w", encoding="utf-8") as fh:
        fh.write("window.ALARO_META=" + json.dumps(meta) + ";\n")
    old = None
    try:
        old = open(os.path.join(DATA, "semnatura.txt"), encoding="utf-8").read()
    except Exception:
        pass
    import hashlib
    sig = hashlib.md5(sig.encode()).hexdigest()
    if old == sig and "--force" not in sys.argv:
        shutil.rmtree(tmp, ignore_errors=True)
        log.info("nimic nou")
        return
    with open(os.path.join(tmp, "semnatura.txt"), "w", encoding="utf-8") as fh:
        fh.write(sig)
    old_dir = DATA + "_vechi"
    shutil.rmtree(old_dir, ignore_errors=True)
    if os.path.isdir(DATA):
        os.rename(DATA, old_dir)
    os.rename(tmp, DATA)
    shutil.rmtree(old_dir, ignore_errors=True)
    # verificare: gridul ANM față de stații
    for s in st:
        if s["id"] == "0-20000-0-15420":
            j = int(round((s["lat"] - LAT0) / DLAT)); i = int(round((s["lon"] - LON0) / DLON))
            log.info("verificare București-Băneasa: %s", "; ".join(
                "%s tx stație %s" % (ds, stv[ds]["tx"][st.index(s)]) for ds in list(stv)[-3:]))
    log.info("gata: %d zile", len(hours))


# ---------------- publicare pe GitHub Pages (doar fișierele schimbate) ----------------
GH_API = os.environ.get("ALARO_GH_API", "https://api.github.com")
GH_CONF = os.path.join(HERE, "github.txt")
GH_MARK = os.path.join(HERE, "github_publicat.txt")


def gh_config():
    if not os.path.exists(GH_CONF):
        return None
    conf = {}
    with open(GH_CONF, encoding="utf-8-sig") as fh:
        for line in fh:
            if "=" in line:
                k, v = line.split("=", 1)
                conf[k.strip().lower()] = v.strip()
    return conf if conf.get("repo") and conf.get("token") else None


def _gh_req(conf, method, url, data=None, ok404=False):
    body = json.dumps(data).encode() if data is not None else None
    req = urllib.request.Request(url, data=body, method=method, headers={
        "Authorization": "Bearer " + conf["token"], "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "HartiMeteo/1.0", "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=300) as r:
            return json.loads(r.read().decode() or "{}")
    except urllib.error.HTTPError as e:
        msg = e.read().decode("utf-8", "replace")[:300]
        if ok404 and e.code in (403, 404, 409, 422):
            return {"_status": e.code, "_msg": msg}
        raise RuntimeError("GitHub %s %s -> %s %s" % (method, url.split("github.com", 1)[-1], e.code, msg))


def gh(conf, method, path, data=None, ok404=False):
    url = "%s/repos/%s%s" % (GH_API, conf["repo"], path)
    for i in range(5):
        try:
            return _gh_req(conf, method, url, data, ok404)
        except RuntimeError:
            raise
        except (urllib.error.URLError, ConnectionError, TimeoutError, OSError) as e:
            if i == 4:
                raise
            log.warning("GitHub: conexiune întreruptă (%s), reîncerc...", e)
            time.sleep(5 * (i + 1))


def publish(force=False):
    conf = gh_config()
    if not conf or not os.path.exists(os.path.join(DATA, "meta.js")):
        return
    import hashlib
    files = [(n, os.path.join(HERE, n)) for n in ("index.html", "portal.html") if os.path.exists(os.path.join(HERE, n))]
    for root, _d, names in os.walk(DATA):
        for name in sorted(names):
            if name.endswith(".js"):
                full = os.path.join(root, name)
                files.append(("data/" + os.path.relpath(full, DATA).replace(os.sep, "/"), full))
    stamp = hashlib.md5(b"".join(open(p, "rb").read() for _n, p in files)).hexdigest()
    if not force and os.path.exists(GH_MARK) and open(GH_MARK, encoding="utf-8").read().strip() == stamp:
        return
    log.info("public pe GitHub (%s)...", conf["repo"])
    first = gh(conf, "POST", "/git/blobs", {"content": "", "encoding": "utf-8"}, ok404=True)
    if first.get("_status") == 409:
        gh(conf, "PUT", "/contents/README.md", {"message": "init", "content": base64.b64encode(
            "Valori înregistrate ANM (CC BY 4.0) pentru compararea cu modelele\n".encode()).decode()})
    existing = {}
    try:
        ref = gh(conf, "GET", "/git/refs/heads/gh-pages", ok404=True)
        if not ref.get("_status") and "object" in ref:
            com = gh(conf, "GET", "/git/commits/" + ref["object"]["sha"])
            t = gh(conf, "GET", "/git/trees/%s?recursive=1" % com["tree"]["sha"])
            existing = {e["sha"]: True for e in t.get("tree", []) if e.get("type") == "blob"}
    except Exception as e:
        log.warning("nu pot citi ce e publicat (%s)", e)
    radar_keep = {}
    try:
        if ref.get("object"):
            radar_keep = {e["path"]: e["sha"] for e in t.get("tree", []) if e.get("type") == "blob" and e["path"].startswith("radar")}
    except Exception:
        radar_keep = {}
    tree = [{"path": p, "mode": "100644", "type": "blob", "sha": s_} for p, s_ in radar_keep.items()]
    tree += [{"path": ".nojekyll", "mode": "100644", "type": "blob",
             "sha": gh(conf, "POST", "/git/blobs", {"content": "", "encoding": "utf-8"})["sha"]}]
    sent = 0
    for path, local in files:
        data = open(local, "rb").read()
        sha = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
        if sha not in existing:
            sha = gh(conf, "POST", "/git/blobs", {"content": base64.b64encode(data).decode(), "encoding": "base64"})["sha"]
            sent += 1
        tree.append({"path": path, "mode": "100644", "type": "blob", "sha": sha})
    tsha = gh(conf, "POST", "/git/trees", {"tree": tree})["sha"]
    csha = gh(conf, "POST", "/git/commits", {"message": "observatii " + stamp[:10], "tree": tsha, "parents": []})["sha"]
    r = gh(conf, "PATCH", "/git/refs/heads/gh-pages", {"sha": csha, "force": True}, ok404=True)
    if r.get("_status"):
        gh(conf, "POST", "/git/refs", {"ref": "refs/heads/gh-pages", "sha": csha})
    pg = gh(conf, "GET", "/pages", ok404=True)
    if pg.get("_status") in (403, 404):
        r = gh(conf, "POST", "/pages", {"source": {"branch": "gh-pages", "path": "/"}}, ok404=True)
        if r.get("_status"):
            log.warning("activează GitHub Pages manual: Settings > Pages > Branch: gh-pages / (root)")
    with open(GH_MARK, "w", encoding="utf-8") as fh:
        fh.write(stamp)
    owner, name = conf["repo"].split("/", 1)
    log.info("publicat: https://%s.github.io/%s/ (%d fișiere trimise)", owner.lower(), name, sent)


def main():
    try:
        update()
    finally:
        try:
            publish("--publica" in sys.argv)
        except Exception:
            log.exception("publicarea pe GitHub a eșuat (se reîncearcă la următoarea rulare)")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s",
                        handlers=[logging.FileHandler(os.path.join(HERE, "obs_harti.log"), encoding="utf-8")]
                        + ([logging.StreamHandler(sys.stdout)] if sys.stdout else []))
    try:
        main()
    except Exception:
        log.exception("actualizarea a eșuat")
        sys.exit(1)
