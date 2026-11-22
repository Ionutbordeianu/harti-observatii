#!/usr/bin/env python3
"""
Radar ANM — observație radar pentru Galați (cerc de 200 km) și estimarea cantitativă a precipitațiilor (QPE)
în aria acoperită, din volumele polare ale radarelor ANM Medgidia, Bârnova și București
(ODIM_H5, banda S, la 5 minute; date deschise ANM, CC BY 4.0).

Lanțul de procesare, pe fiecare volum (la 5 minute), după literatura de specialitate:
  1. citire parțială (HTTP Range) a celor 3 elevații de jos: DBZH, ZDR, KDP, RHOHV, VRAD; ETOP (produs ANM);
  2. blocarea fasciculului de relief (Bech et al. 2003, J. Atmos. Oceanic Technol. 20, 845–855), cu raza
     efectivă 4/3 și lățimea fasciculului din fișier; „hybrid scan”: în fiecare punct, cea mai joasă elevație
     blocată sub 50%, cu corecția reflectivității pentru blocarea parțială 10–50% (Fulton et al. 1998, Wea.
     Forecasting 13, 377–395);
  3. textura reflectivității și clasificarea hidrometeorilor fuzzy (Park et al. 2009, Wea. Forecasting 24,
     730–748), cu stratul de topire din volum (Giangrande et al. 2008, J. Appl. Meteor. Climatol. 47, 1354–1364);
     ecourile de sol / biologice sunt clase ale algoritmului; hartă statică de ecouri fixe după frecvența de
     apariție (practica OPERA/BALTRAD, Ośrodka et al. 2014) pentru turbine eoliene și ținte fixe;
  4. intensitatea după clasa de hidrometeori (algoritmul NEXRAD, Giangrande & Ryzhkov 2008, J. Appl. Meteor.
     Climatol. 47, 2445–2462);
  5. compozit „cel mai jos fascicul” din cele 3 radare;
  6. cumul orar: fiecare volum reprezintă 5 minute; ora (încheiată la HH:00) se calculează doar unde există
     ≥ 10 din 12 volume valide (lipsurile se compensează proporțional), altfel rămâne necunoscută;
  7. tipul precipitației la sol pe relieful real (baza stratului de topire și temperatura umedă la stații,
     Stull 2011); vânt VAD (Browning & Wexler 1968); deplasarea ecourilor prin corelație.

Ieșiri: pagina radar.html (cerc 200 km, valori exacte la mouse) și cumulul orar pe grila comună ALADIN
(qpe/ro_YYYYMMDDHH.npz), folosit de obs_harti.py pentru precipitațiile orare și zilnice îmbinate cu pluviometrele.
"""
import base64
import gzip
import hashlib
import http.client
import io
import json
import logging
import math
import os
import re
import ssl
import struct
import sys
import threading
import time
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone

import numpy as np

log = logging.getLogger("radar")
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "radar")
CACHE = os.path.join(HERE, "radar_cache")
QPE = os.path.join(HERE, "qpe")
HOST = "opendata.meteoromania.ro"
SRC = "https://%s/radar/" % HOST
RADARS = {"MED": "Medgidia", "BAR": "Bârnova", "BUC": "București"}
RCODES = list(RADARS)
VOLP = ["dBZ", "ZDR", "KDP", "RhoHV", "V"]          # volume polare necesare (Height = ETOP, opțional)
QMAP = {"dBZ": "DBZH", "ZDR": "ZDR", "KDP": "KDP", "RhoHV": "RHOHV", "V": "VRAD"}
NTILT = 3                                           # elevațiile de jos folosite în „hybrid scan”
KEEP_FRAMES = 19                                    # 3 ore la 10 minute (inclusiv capetele)
FRAME_SPAN_MIN = 180                                # fereastra de timp a paginii
BUDGET_S = 400                                      # timp maxim de procesare pe rulare (rularea e la 10 minute)
LOOKBACK_H = 6                                      # recuperare după oprirea calculatorului (orele mai vechi: compozitul ANM)
CENTER = (45.4353, 28.0080)                         # Galați
RADIUS = 200.0
KX = 111.32 * math.cos(math.radians(CENTER[0]))
KY = 110.57
# grila de lucru, 1 km: acoperă toată raza (230 km) a celor 3 radare
XW, XE, YS, YN = -392, 258, -368, 410
GX = np.arange(XW, XE + 1, dtype=np.float64)
GY = np.arange(YN, YS - 1, -1, dtype=np.float64)    # rândul 0 = nord
GH, GW = GY.size, GX.size
GLON = CENTER[1] + GX[None, :] / KX + 0 * GY[:, None]
GLAT = CENTER[0] + GY[:, None] / KY + 0 * GX[None, :]
# fereastra paginii radar: pătratul de ±200 km în jurul Galațiului
HALF = int(RADIUS)
PR0, PC0 = YN - HALF, -XW - HALF
PSL = (slice(PR0, PR0 + 2 * HALF + 1), slice(PC0, PC0 + 2 * HALF + 1))
PDIST = np.hypot(GX[None, PC0:PC0 + 2 * HALF + 1], GY[PR0:PR0 + 2 * HALF + 1, None])
INSIDE = PDIST <= RADIUS
BOUNDS = [float(GLON[0, PC0]) - 0.5 / KX, float(GLAT[PR0 + 2 * HALF, 0]) - 0.5 / KY,
          float(GLON[0, PC0 + 2 * HALF]) + 0.5 / KX, float(GLAT[PR0, 0]) + 0.5 / KY]
_merc = lambda la: np.log(np.tan(np.pi / 4 + np.radians(la) / 2))
_yT, _yB = _merc(BOUNDS[3]), _merc(BOUNDS[1])
_latr = np.degrees(2 * np.arctan(np.exp(_yT + (_yB - _yT) * (np.arange(2 * HALF + 1) + 0.5) / (2 * HALF + 1)))) - 90
MERC_ROWS = np.clip(np.round(HALF - (_latr - CENTER[0]) * KY).astype(int), 0, 2 * HALF)
# grila comună ALADIN (pentru precipitațiile pe România)
A_LON0, A_LAT0, A_DLON, A_DLAT, A_W, A_H = 19.0, 42.5, 0.03, 0.021, 367, 334
RE = 6371000.0
KE = 4.0 / 3.0
PLACES = [("Galați", 45.4353, 28.0080), ("Brăila", 45.2692, 27.9575), ("Tulcea", 45.1787, 28.8050), ("Focșani", 45.6967, 27.1837),
          ("Tecuci", 45.8496, 27.4268), ("Bârlad", 46.2316, 27.6694), ("Buzău", 45.1500, 26.8333), ("Râmnicu Sărat", 45.3800, 27.0600),
          ("Isaccea", 45.2700, 28.4600), ("Măcin", 45.2430, 28.1350), ("Hârșova", 44.6880, 27.9500), ("Slobozia", 44.5640, 27.3660),
          ("Vaslui", 46.6400, 27.7300), ("Adjud", 46.1000, 27.1700), ("Cahul (MD)", 45.9070, 28.1990), ("Reni (UA)", 45.4560, 28.2830),
          ("Ismail (UA)", 45.3500, 28.8370), ("Bujor", 45.8700, 27.9100), ("Ianca", 45.1350, 27.4750), ("Babadag", 44.8930, 28.7120),
          ("Constanța", 44.1733, 28.6383), ("Medgidia", 44.2500, 28.2700), ("Călărași", 44.2000, 27.3300), ("Bacău", 46.5670, 26.9140),
          ("Onești", 46.2500, 26.7700), ("Huși", 46.6730, 28.0620), ("Bolgrad (UA)", 45.6770, 28.6140), ("Comrat (MD)", 46.3000, 28.6560),
          ("Sulina", 45.1560, 29.6530), ("Urziceni", 44.7180, 26.6420), ("Ploiești", 44.9400, 26.0300), ("Fetești", 44.3850, 27.8300),
          ("Mahmudia", 45.0850, 29.0800), ("Panciu", 45.9080, 27.0870), ("Mărășești", 45.8800, 27.2300), ("Pogoanele", 44.9160, 27.0000),
          ("Iași", 47.1585, 27.6014), ("Suceava", 47.6514, 26.2556), ("Botoșani", 47.7486, 26.6694), ("Piatra Neamț", 46.9275, 26.3708),
          ("Roman", 46.9200, 26.9300), ("Miercurea Ciuc", 46.3600, 25.8000), ("Sfântu Gheorghe", 45.8636, 25.7875), ("Brașov", 45.6427, 25.5887),
          ("Târgu Mureș", 46.5425, 24.5575), ("Sibiu", 45.7983, 24.1256), ("Pitești", 44.8565, 24.8692), ("Târgoviște", 44.9254, 25.4567),
          ("Râmnicu Vâlcea", 45.1000, 24.3693), ("Craiova", 44.3302, 23.7949), ("Slatina", 44.4300, 24.3700), ("Alexandria", 43.9686, 25.3328),
          ("Giurgiu", 43.9037, 25.9699), ("București", 44.4268, 26.1025), ("Ruse (BG)", 43.8356, 25.9657), ("Silistra (BG)", 44.1170, 27.2600),
          ("Dobrich (BG)", 43.5726, 27.8273), ("Varna (BG)", 43.2141, 27.9147), ("Shumen (BG)", 43.2706, 26.9361), ("Mangalia", 43.8170, 28.5830),
          ("Chișinău (MD)", 47.0105, 28.8638), ("Bălți (MD)", 47.7617, 27.9289), ("Tiraspol (MD)", 46.8403, 29.6433), ("Odesa (UA)", 46.4825, 30.7233),
          ("Bilhorod-Dnistrovskîi (UA)", 46.1900, 30.3400), ("Deva", 45.8833, 22.9000), ("Cluj-Napoca", 46.7712, 23.6236), ("Bistrița", 47.1333, 24.5000),
          ("Vatra Dornei", 47.3450, 25.3600), ("Câmpulung Moldovenesc", 47.5300, 25.5500), ("Sinaia", 45.3500, 25.5500), ("Vrancea (munte)", 45.7400, 26.5700),
          ("Tulcea – Delta (Gorgova)", 45.1700, 29.1700), ("Fălticeni", 47.4600, 26.3000), ("Dorohoi", 47.9600, 26.4000), ("Hunedoara", 45.7500, 22.9000)]


# ---------------- acces HTTP (conexiuni persistente, citire parțială) ----------------
_TL = threading.local()
STATS = {"bytes": 0, "req": 0}
_SLOCK = threading.Lock()


def _conn(fresh=False):
    c = getattr(_TL, "c", None)
    if c is None or fresh:
        if c is not None:
            try:
                c.close()
            except Exception:
                pass
        c = http.client.HTTPSConnection(HOST, timeout=60, context=ssl.create_default_context())
        _TL.c = c
    return c


def http_get(path, rng=None, tries=4):
    """GET pe aceeași conexiune (keep-alive); rng = (start, end) inclusiv → (date, mărimea totală)"""
    for k in range(tries):
        try:
            c = _conn(fresh=k > 0)
            h = {"User-Agent": "HartiMeteo/2.0", "Connection": "keep-alive"}
            if rng:
                h["Range"] = "bytes=%d-%d" % rng
            c.request("GET", path, headers=h)
            r = c.getresponse()
            data = r.read()
            if r.status == 404:
                raise FileNotFoundError(path)
            if r.status not in (200, 206):
                raise IOError("HTTP %d %s" % (r.status, path))
            total = len(data)
            cr = r.getheader("Content-Range")
            if cr and "/" in cr:
                total = int(cr.rsplit("/", 1)[1])
            with _SLOCK:
                STATS["bytes"] += len(data); STATS["req"] += 1
            return data, total
        except FileNotFoundError:
            raise
        except Exception:
            if k == tries - 2:
                break
            time.sleep(2 * (k + 1))
    # rezervă: urllib (respectă proxy-ul configurat în sistem), fără conexiune persistentă
    req = urllib.request.Request(SRC.rsplit("/radar/", 1)[0] + path, headers={"User-Agent": "HartiMeteo/2.0", **({"Range": "bytes=%d-%d" % rng} if rng else {})})
    try:
        with urllib.request.urlopen(req, timeout=90) as r:
            data = r.read()
            total = len(data)
            cr = r.headers.get("Content-Range")
            if cr and "/" in cr:
                total = int(cr.rsplit("/", 1)[1])
    except urllib.error.HTTPError as e:
        if e.code == 404:
            raise FileNotFoundError(path)
        raise
    with _SLOCK:
        STATS["bytes"] += len(data); STATS["req"] += 1
    return data, total


class RangeFile(io.RawIOBase):
    """fișier la distanță citit pe bucăți de 16 kB (HTTP Range), pentru h5py"""
    BS = 16384

    def __init__(self, path):
        self.path = path; self.pos = 0; self.blocks = {}
        d, self.size = http_get(path, (0, self.BS - 1))
        self.blocks[0] = d

    def readable(self): return True
    def seekable(self): return True
    def tell(self): return self.pos

    def seek(self, off, whence=0):
        self.pos = off if whence == 0 else (self.pos + off if whence == 1 else self.size + off)
        return self.pos

    def readinto(self, b):
        n = min(len(b), self.size - self.pos)
        if n <= 0:
            return 0
        k0, k1 = self.pos // self.BS, (self.pos + n - 1) // self.BS
        miss = [k for k in range(k0, k1 + 1) if k not in self.blocks]
        if miss:
            a, z = miss[0], miss[-1]
            d, _ = http_get(self.path, (a * self.BS, min(self.size, (z + 1) * self.BS) - 1))
            for k in range(a, z + 1):
                self.blocks[k] = d[(k - a) * self.BS:(k - a + 1) * self.BS]
        out = b"".join(self.blocks[k] for k in range(k0, k1 + 1))
        o = self.pos - k0 * self.BS
        b[:n] = out[o:o + n]
        self.pos += n
        return n


class LocalFile(io.FileIO):
    pass


def open_src(code, ts, prod):
    loc = os.environ.get("RADAR_LOCAL")
    if loc:
        return open(os.path.join(loc, "%s_%s%s.hdf" % (code, ts, prod)), "rb")
    return RangeFile("/radar/%s/%s_%s%s.hdf" % (code, code, ts, prod))


def listing(code):
    """{ts: set(produse)} din indexul directorului radarului"""
    loc = os.environ.get("RADAR_LOCAL")
    if loc:
        names = "\n".join(os.listdir(loc))
    else:
        names = http_get("/radar/%s/" % code)[0].decode("latin-1")
    found = {}
    for ts, prod in re.findall(code + r"_(\d{16})(dBZ|V|ZDR|KDP|RhoHV|dBR|Height)\.hdf", names):
        found.setdefault(ts, set()).add(prod)
    return found


def ts_time(ts):
    return datetime.strptime(ts[:12], "%Y%m%d%H%M").replace(tzinfo=timezone.utc)


# ---------------- citire ODIM_H5 ----------------
def _attrs(g):
    out = {}
    for k, v in g.attrs.items():
        if isinstance(v, bytes):
            v = v.decode("latin-1")
        elif hasattr(v, "item") and np.size(v) == 1:
            v = v.item()
            if isinstance(v, bytes):
                v = v.decode("latin-1")
        out[k] = v
    return out


def _dset(f, name):
    g = f[name]
    w = _attrs(g["where"]) if "where" in g else {}
    wh = _attrs(g["what"]) if "what" in g else {}
    d = g["data1"]
    dw = _attrs(d["what"]) if "what" in d else {}
    raw = d["data"][()]
    gain = float(dw.get("gain", wh.get("gain", 1.0))); off = float(dw.get("offset", wh.get("offset", 0.0)))
    nod, und = dw.get("nodata", wh.get("nodata")), dw.get("undetect", wh.get("undetect"))
    return {"raw": raw, "gain": gain, "off": off, "nod": nod, "und": und, "q": str(dw.get("quantity", "")),
            "el": float(w.get("elangle", 0.0)), "rscale": float(w.get("rscale", 250.0)),
            "rstart": float(w.get("rstart", 0.0)) * 1000.0, "nrays": raw.shape[0], "nbins": raw.shape[1],
            "a1gate": int(w.get("a1gate", 0)), "where": w}


def read_volume(code, ts, prod, names):
    import h5py
    fh = open_src(code, ts, prod)
    try:
        f = h5py.File(fh, "r")
        root = {k: _attrs(f[k]) for k in ("what", "where", "how") if k in f}
        sets = {}
        for nm in names:
            if nm in f:
                sets[nm] = _dset(f, nm)
        f.close()
    finally:
        fh.close()
    return root, sets


def decode(ds):
    """valori fizice; NaN = fără date (nodata), -inf = sub pragul de detecție (undetect)"""
    v = ds["raw"].astype(np.float32) * ds["gain"] + ds["off"]
    if ds["nod"] is not None:
        v[ds["raw"] == ds["nod"]] = np.nan
    if ds["und"] is not None:
        v[ds["raw"] == ds["und"]] = -np.inf
    return v


# ---------------- relief și geometria fasciculului ----------------
_RZ = None


def relief_at(lat, lon):
    """altitudinea (m) din relieful comun ALADIN 2,3 km, biliniar; în afara domeniului (est de 30°E: Marea Neagră
       și câmpia Odesei, sud de 42,5°N) se ia 0 m"""
    global _RZ
    if _RZ is None:
        _RZ = np.load(os.path.join(HERE, "relief_aladin.npy")).astype(np.float64)
    z = _RZ
    fx = (np.asarray(lon) - A_LON0) / A_DLON; fy = (np.asarray(lat) - A_LAT0) / A_DLAT
    out = (fx >= 0) & (fy >= 0) & (fx <= z.shape[1] - 1) & (fy <= z.shape[0] - 1)
    i0 = np.clip(np.floor(fx).astype(int), 0, z.shape[1] - 2); j0 = np.clip(np.floor(fy).astype(int), 0, z.shape[0] - 2)
    wx = np.clip(fx - i0, 0, 1); wy = np.clip(fy - j0, 0, 1)
    v = (z[j0, i0] * (1 - wx) + z[j0, i0 + 1] * wx) * (1 - wy) + (z[j0 + 1, i0] * (1 - wx) + z[j0 + 1, i0 + 1] * wx) * wy
    return np.where(out, np.maximum(v, 0.0), 0.0)


_RELIEF_G = None


def relief_grid():
    global _RELIEF_G
    if _RELIEF_G is None:
        _RELIEF_G = relief_at(GLAT, GLON).astype(np.float32)
    return _RELIEF_G


def az_range(lat0, lon0, lat, lon):
    """azimutul (grade) și distanța pe sol (m) de la radar la puncte (sferă)"""
    p0, l0, p, l = map(np.radians, (lat0, lon0, lat, lon))
    dl = l - l0
    a = np.sin((p - p0) / 2) ** 2 + np.cos(p0) * np.cos(p) * np.sin(dl / 2) ** 2
    s = 2 * RE * np.arcsin(np.sqrt(np.clip(a, 0, 1)))
    az = np.degrees(np.arctan2(np.sin(dl) * np.cos(p), np.cos(p0) * np.sin(p) - np.sin(p0) * np.cos(p) * np.cos(dl))) % 360
    return az, s


def dest(lat0, lon0, az_deg, s):
    p0, l0, th, d = math.radians(lat0), math.radians(lon0), np.radians(az_deg), s / RE
    p = np.arcsin(np.sin(p0) * np.cos(d) + np.cos(p0) * np.sin(d) * np.cos(th))
    l = l0 + np.arctan2(np.sin(th) * np.sin(d) * np.cos(p0), np.cos(d) - np.sin(p0) * np.sin(p))
    return np.degrees(p), np.degrees(l)


def slant_from_ground(s, el_deg, h0):
    """distanța oblică r și înălțimea centrului fasciculului (m, deasupra nivelului mării), raza efectivă 4/3 (Doviak & Zrnić)"""
    ae = KE * RE
    el = math.radians(el_deg)
    h = np.zeros_like(s, dtype=np.float64)
    for _ in range(5):
        r = (ae + h) * np.sin(s / ae) / math.cos(el)
        h = np.sqrt(r ** 2 + ae ** 2 + 2 * r * ae * math.sin(el)) - ae
    return r, h + h0


def height_from_slant(r, el_deg, h0):
    ae = KE * RE
    el = math.radians(el_deg)
    h = np.sqrt(r ** 2 + ae ** 2 + 2 * r * ae * math.sin(el)) - ae
    s = ae * np.arcsin(r * math.cos(el) / (ae + h))
    return h + h0, s


def geometry(code, root, tilts):
    """pentru fiecare punct al grilei din raza radarului: raza, poarta pe fiecare elevație, elevația aleasă („hybrid
       scan”: cea mai joasă cu blocare cumulată < 50%), corecția de blocare (dB) și înălțimea fasciculului"""
    w = root.get("where", {}); how = root.get("how", {})
    lat0, lon0, h0 = float(w["lat"]), float(w["lon"]), float(w.get("height", 0.0))
    bw = float(how.get("beamwidth", how.get("beamwH", 1.0)) or 1.0)
    sig = json.dumps([code, round(lat0, 4), round(lon0, 4), round(h0), round(bw, 2),
                      [[round(t["el"], 2), t["nrays"], t["nbins"], t["rscale"], t["rstart"]] for t in tilts], GH, GW, 2])
    key = hashlib.md5(sig.encode()).hexdigest()[:10]
    p = os.path.join(CACHE, "geom_%s_%s.npz" % (code, key))
    if os.path.exists(p):
        with np.load(p) as d:
            return {k: d[k] for k in d.files}
    t0 = tilts[0]
    nr, nb, rs, r0 = t0["nrays"], t0["nbins"], t0["rscale"], t0["rstart"]
    # 1. blocarea fasciculului în coordonate polare (Bech et al. 2003): profilul reliefului pe fiecare rază
    rr = r0 + (np.arange(nb) + 0.5) * rs
    azc = (np.arange(nr) + 0.5) * 360.0 / nr
    hh0, ss0 = height_from_slant(rr, t0["el"], h0)
    la, lo = dest(lat0, lon0, azc[:, None], ss0[None, :])
    terr = relief_at(la, lo)                                        # (nr, nb)
    cbb = []
    for t in tilts:
        rrt = t["rstart"] + (np.arange(t["nbins"]) + 0.5) * t["rscale"]
        ht, _ = height_from_slant(rrt, t["el"], h0)
        a = rrt * math.tan(math.radians(bw) / 2.0)                  # raza fasciculului la -3 dB
        tt = terr[:, :t["nbins"]] if t["nbins"] <= nb else np.pad(terr, ((0, 0), (0, t["nbins"] - nb)), mode="edge")
        y = np.clip(tt - ht[None, :], -a[None, :], a[None, :])
        aa = np.broadcast_to(a[None, :], y.shape)
        pbb = (y * np.sqrt(np.maximum(aa ** 2 - y ** 2, 0)) + aa ** 2 * np.arcsin(y / aa) + math.pi * aa ** 2 / 2) / (math.pi * aa ** 2)
        cbb.append(np.maximum.accumulate(np.clip(pbb, 0, 1), axis=1).astype(np.float32))
    # 2. punctele grilei din raza radarului
    maxs = max(height_from_slant(t["rstart"] + t["nbins"] * t["rscale"], t["el"], h0)[1] for t in tilts)
    az, s = az_range(lat0, lon0, GLAT, GLON)
    pix = np.flatnonzero((s <= maxs).ravel())
    az = az.ravel()[pix]; s = s.ravel()[pix]
    nt = len(tilts)
    rays = np.zeros((nt, pix.size), np.int32)
    bins = np.full((nt, pix.size), -1, np.int32)
    hb = np.full((nt, pix.size), np.nan, np.float32)
    cb = np.ones((nt, pix.size), np.float32)
    for k, t in enumerate(tilts):
        r, h = slant_from_ground(s, t["el"], h0)
        ib = np.floor((r - t["rstart"]) / t["rscale"]).astype(np.int32)
        ok = (ib >= 0) & (ib < t["nbins"])
        bins[k, ok] = ib[ok]
        hb[k] = h
        rk = (np.floor(az / (360.0 / t["nrays"])).astype(np.int32)) % t["nrays"]
        rays[k] = rk
        cb[k, ok] = cbb[k][rk[ok], ib[ok]]
    tilt = np.full(pix.size, -1, np.int8)
    for k in range(nt - 1, -1, -1):
        good = (bins[k] >= 0) & (cb[k] < 0.5)
        tilt[good] = k
    sel = np.clip(tilt, 0, nt - 1)
    cbs = cb[sel, np.arange(pix.size)]
    corr = np.where((tilt >= 0) & (cbs >= 0.1), -10 * np.log10(np.maximum(1 - cbs, 0.5)), 0.0).astype(np.float32)
    g = {"pix": pix.astype(np.int32), "rays": rays, "bins": bins, "tilt": tilt, "corr": corr,
         "hbeam": np.where(tilt >= 0, hb[sel, np.arange(pix.size)], np.nan).astype(np.float32),
         "h_low": hb[0].astype(np.float32), "cbb0": cb[0].astype(np.float32), "s": (s / 1000.0).astype(np.float32),
         "lat0": np.float64(lat0), "lon0": np.float64(lon0), "h0": np.float64(h0)}
    np.savez_compressed(p + ".tmp.npz", **g)
    os.replace(p + ".tmp.npz", p)
    log.info("%s: geometrie nouă — %d puncte în rază; blocare la 0,5°: %.0f%% din puncte peste 50%%, %.0f%% între 10 și 50%%",
             code, pix.size, 100 * np.mean(cb[0] >= 0.5), 100 * np.mean((cb[0] >= 0.1) & (cb[0] < 0.5)))
    return g


# ---------------- procesarea unui volum ----------------
def texture(z):
    """SD(Z) de-a lungul razei pe 9 porți (~2 km), Park et al. 2009"""
    zz = np.where(np.isfinite(z), z, np.nan).astype(np.float64)
    k = 9
    zf = np.nan_to_num(zz, nan=0.0); n = np.isfinite(zz).astype(float)
    pad = ((0, 0), (k // 2 + 1, k // 2))
    c1 = np.cumsum(np.pad(zf, pad), 1); c2 = np.cumsum(np.pad(zf ** 2, pad), 1); cn = np.cumsum(np.pad(n, pad), 1)
    S1 = c1[:, k:] - c1[:, :-k]; S2 = c2[:, k:] - c2[:, :-k]; N = cn[:, k:] - cn[:, :-k]
    sd = np.sqrt(np.maximum(S2 / np.maximum(N, 1) - (S1 / np.maximum(N, 1)) ** 2, 0))
    return np.where(N >= 3, sd, np.nan).astype(np.float32)


def sample_image(ds, where, lat, lon):
    """produs cartografic ODIM (aeqd) → puncte"""
    pj = str(where.get("projdef", ""))
    lon0 = float(re.search(r"lon_0=([-\d.]+)", pj).group(1)); lat0 = float(re.search(r"lat_0=([-\d.]+)", pj).group(1))
    R = 6370997.0

    def fwd(la, lo):
        p0, l0, p, l = map(np.radians, (lat0, lon0, la, lo))
        c = np.arccos(np.clip(np.sin(p0) * np.sin(p) + np.cos(p0) * np.cos(p) * np.cos(l - l0), -1, 1))
        k = np.where(c > 1e-9, c / np.maximum(np.sin(c), 1e-12), 1.0)
        return R * k * np.cos(p) * np.sin(l - l0), R * k * (np.cos(p0) * np.sin(p) - np.sin(p0) * np.cos(p) * np.cos(l - l0))
    xll, yll = fwd(float(where["LL_lat"]), float(where["LL_lon"]))
    xur, yur = fwd(float(where["UR_lat"]), float(where["UR_lon"]))
    v = decode(ds)
    ny, nx = v.shape
    x, y = fwd(lat, lon)
    col = np.floor((x - xll) / ((xur - xll) / nx)).astype(int); row = np.floor((yur - y) / ((yur - yll) / ny)).astype(int)
    ok = (col >= 0) & (row >= 0) & (col < nx) & (row < ny)
    out = np.full(np.shape(lat), np.nan, np.float32)
    out[ok] = v[row[ok], col[ok]]
    return out


# ---------------- profilul vertical al reflectivității (VPR) ----------------
#   Germann & Joss (2002, J. Appl. Meteor. 41, 542–557; MeteoSwiss): profilul „mesobeta” = reflectivitatea medie pe
#   straturi de înălțime într-un cilindru de 70 km în jurul radarului, din toate elevațiile volumului, integrată în
#   timp cu ponderea „pwe” (volumul de precipitații × descreștere exponențială, constanta de timp ~100 min).
#   Corecția: ecoul măsurat de fascicul (profilul ponderat cu forma gaussiană a fasciculului) e adus la nivelul
#   solului (Joss & Lee 1995; Germann & Joss 2002): ΔZ = 10·log10( P(sol) / ∫P·f ).
#   Profilele convective nu se corectează (practica Met Office, Kitchen et al. 1994: Z ≥ 30 dBZ la 1,5 km
#   deasupra izotermei 0 °C ⇒ fără corecție VPR).
VPR_DH = 200.0              # m, grosimea straturilor
VPR_HMAX = 12000.0
VPR_RMIN, VPR_RMAX = 5000.0, 70000.0
VPR_TAU_MIN = 100.0
VPR_NMIN = 500              # porți (ponderate) pe strat ca stratul să fie folosit
VPR_MAXDB = 10.0            # siguranță: corecția limitată la ±10 dB
VPR_NB = int(VPR_HMAX / VPR_DH)


def vpr_observe(sz, sr, h0):
    """sume pe straturi de 200 m: Σz (liniar, porțile „sub prag” = 0) și numărul de porți; RhoHV < 0,85 cu ecou
       = ecou nemeteorologic (Park et al. 2009), exclus"""
    SZ = np.zeros(VPR_NB); NN = np.zeros(VPR_NB)
    for nm, dz in sz.items():
        Z = decode(dz)
        rr = dz["rstart"] + (np.arange(Z.shape[1]) + 0.5) * dz["rscale"]
        sel = (rr >= VPR_RMIN) & (rr <= VPR_RMAX)
        if not sel.any():
            continue
        Z = Z[:, sel]; rr = rr[sel]
        hh, _ = height_from_slant(rr, dz["el"], h0)
        ok = ~np.isnan(Z)
        if nm in sr and decode(sr[nm]).shape == decode(dz).shape:
            P = decode(sr[nm])[:, sel]
            with np.errstate(invalid="ignore"):
                ok &= ~(np.isfinite(Z) & (Z >= 5) & np.isfinite(P) & (P < 0.85))
        z = np.where(np.isfinite(Z), 10 ** (np.where(np.isfinite(Z), Z, 0) / 10.0), 0.0)
        kb = np.clip((hh / VPR_DH).astype(int), 0, VPR_NB - 1)
        SZ += np.bincount(np.broadcast_to(kb[None, :], Z.shape)[ok], weights=z[ok], minlength=VPR_NB)
        NN += np.bincount(np.broadcast_to(kb[None, :], Z.shape)[ok], minlength=VPR_NB)
    return SZ, NN


def vpr_update(prev, obs, now):
    """integrarea în timp „pwe” (Germann & Joss 2002): sumele vechi scad cu exp(−Δt/τ), cele noi se adaugă;
       media Σz/N e astfel ponderată cu volumul de precipitații"""
    SZ, NN = obs
    if prev:
        dt = (now - datetime.fromisoformat(prev["t"])).total_seconds() / 60.0
        e = math.exp(-max(dt, 0.0) / VPR_TAU_MIN)
        SZ = SZ + e * np.asarray(prev["sz"]); NN = NN + e * np.asarray(prev["n"])
    return {"t": now.isoformat(), "sz": [round(float(x), 3) for x in SZ], "n": [round(float(x), 1) for x in NN]}


def vpr_profile(st, fl, h0=0.0):
    """profilul mediu (z liniar pe straturi), înălțimea de referință „la sol” și dacă e utilizabil (stratiform)"""
    if not st:
        return None
    SZ = np.asarray(st["sz"]); NN = np.asarray(st["n"])
    ok = NN >= VPR_NMIN
    if ok.sum() < 5:
        return None
    hc = (np.arange(VPR_NB) + 0.5) * VPR_DH
    P = np.where(ok, SZ / np.maximum(NN, 1e-9), np.nan)
    # nivelul de referință: primele două straturi văzute aflate la cel puțin 500 m deasupra radarului — dedesubt,
    # până la 70 km, porțile sunt dominate de ecourile de sol rămase (de ex. turbinele eoliene de lângă Medgidia)
    cand = np.flatnonzero(ok & (hc >= h0 + 500.0))
    if cand.size < 2:
        return None
    k0 = int(cand[0])
    ref = float(np.nanmean(P[k0:k0 + 2]))
    if not ref > 10 ** (5 / 10.0):                       # sub 5 dBZ în medie: prea puține precipitații pentru un profil
        return None
    # extrapolare: sub primul strat văzut profilul e constant (Germann & Joss 2002); deasupra ultimului, fără ecou
    P[:k0] = P[k0]
    last = int(np.flatnonzero(ok)[-1]); P[last + 1:] = 0.0
    P = np.where(np.isfinite(P), P, 0.0)
    if fl is not None and np.isfinite(fl):
        kc = int(min(max((fl + 1500.0) / VPR_DH, 0), VPR_NB - 1))
        if ok[kc] and 10 * math.log10(max(P[kc], 1e-6)) >= 30.0:
            return {"conv": True}
    return {"P": P, "hc": hc, "ref": ref, "href": float(hc[k0 + 1]), "conv": False}


def vpr_correction(prof, hbeam, s_km, bw_deg):
    """ΔZ (dB) pentru fiecare punct: profilul la sol / profilul văzut de fascicul (gaussian, lățimea la −3 dB = bw)"""
    out = np.zeros(hbeam.shape, np.float32)
    if not prof or prof.get("conv"):
        return out
    P, hc = prof["P"], prof["hc"]
    m = np.isfinite(hbeam) & (hbeam > prof["href"])
    if not m.any():
        return out
    sig = np.maximum(s_km[m] * 1000.0 * math.tan(math.radians(bw_deg) / 2.0) / math.sqrt(2 * math.log(2)), VPR_DH / 2)
    res = np.empty(m.sum(), np.float64)
    for a in range(0, m.sum(), 20000):
        hb = hbeam[m][a:a + 20000].astype(np.float64)[:, None]; sg = sig[a:a + 20000][:, None]
        w = np.exp(-0.5 * ((hc[None, :] - hb) / sg) ** 2)
        pb = (w * P[None, :]).sum(1) / np.maximum(w.sum(1), 1e-12)
        res[a:a + 20000] = 10 * np.log10(prof["ref"] / np.maximum(pb, 1e-6))
    out[m] = np.clip(res, -VPR_MAXDB, VPR_MAXDB)
    return out


def melting_layer(code, ts):
    """strat de topire din elevațiile 4–10°, distanțe 5–60 km: porți cu RhoHV 0,90–0,97, ZDR 0,8–2,5 dB și
       Z 20–47 dBZ (criteriile Giangrande et al. 2008); bază / mijloc / vârf = percentilele 20 / 50 / 80 ale
       înălțimilor (m deasupra nivelului mării). None dacă sunt sub 300 de porți.
       Întoarce și observația pentru profilul vertical (toate elevațiile 1–10, distanțe 5–70 km)."""
    names = ["dataset%d" % k for k in range(1, 11)]
    root, sz = read_volume(code, ts, "dBZ", names)
    _, sd = read_volume(code, ts, "ZDR", names[3:])
    _, sr = read_volume(code, ts, "RhoHV", names)
    h0 = float(root["where"].get("height", 0.0))
    vobs = vpr_observe(sz, sr, h0)
    hs = []
    for nm, dz in sz.items():
        if nm not in sd or nm not in sr or not (4.0 <= dz["el"] <= 10.5):
            continue
        Z, D, P = decode(dz), decode(sd[nm]), decode(sr[nm])
        if Z.shape != D.shape or Z.shape != P.shape:
            continue
        rr = dz["rstart"] + (np.arange(Z.shape[1]) + 0.5) * dz["rscale"]
        hh, _ = height_from_slant(rr, dz["el"], h0)
        with np.errstate(invalid="ignore"):
            m = (P >= 0.90) & (P <= 0.97) & (D >= 0.8) & (D <= 2.5) & (Z >= 20) & (Z <= 47)
        m &= ((rr > 5000) & (rr < 60000))[None, :]
        if m.any():
            hs.append(np.broadcast_to(hh[None, :], m.shape)[m])
    a = np.concatenate(hs) if hs else np.zeros(0)
    if a.size < 300:
        return None, vobs
    return [float(np.percentile(a, 20)), float(np.percentile(a, 50)), float(np.percentile(a, 80)), int(a.size)], vobs


def vad(dv, h0):
    """vânt orizontal din viteza Doppler (VAD, Browning & Wexler 1968), porți la 10–30 km"""
    v = decode(dv)
    nr, nb = v.shape
    rs, r0 = dv["rscale"], dv["rstart"]
    i0, i1 = int((10000 - r0) / rs), int((30000 - r0) / rs)
    vr = v[:, i0:i1]
    az = np.radians((np.arange(nr) + 0.5) * 360.0 / nr)
    ok = np.isfinite(vr)
    if ok.sum() < 300:
        return None
    A = np.stack([np.ones(ok.sum()), np.sin(np.broadcast_to(az[:, None], vr.shape)[ok]), np.cos(np.broadcast_to(az[:, None], vr.shape)[ok])], 1)
    c, *_ = np.linalg.lstsq(A, vr[ok], rcond=None)
    el = dv["el"]
    u = c[1] / math.cos(math.radians(el)); w = c[2] / math.cos(math.radians(el))
    hm, _ = height_from_slant(20000.0, el, h0)
    return {"u": float(u), "v": float(w), "h": float(hm), "el": el}


def process_radar(code, ts, want_ml):
    tn = ["dataset%d" % k for k in range(1, NTILT + 1)]
    root, sz = read_volume(code, ts, "dBZ", tn)
    tilts = [sz[n] for n in tn if n in sz]
    if len(tilts) < 1 or "where" not in root or "lat" not in root["where"]:
        raise ValueError("volum incomplet")
    els = [t["el"] for t in tilts]
    if els != sorted(els) or els[0] > 1.0:
        raise ValueError("ordinea elevațiilor neașteptată: %s" % els)
    g = geometry(code, root, tilts)
    pix, tilt = g["pix"], g["tilt"]
    have = tilt >= 0
    ar = np.arange(pix.size)
    k = np.clip(tilt, 0, len(tilts) - 1)

    def pick(sets):
        out = np.full(pix.size, np.nan, np.float32)
        for kk, nm in enumerate(tn[:len(tilts)]):
            if nm not in sets:
                continue
            arr = decode(sets[nm]) if isinstance(sets[nm], dict) else sets[nm]
            m = have & (k == kk)
            if arr.shape != (tilts[kk]["nrays"], tilts[kk]["nbins"]):
                continue
            out[m] = arr[g["rays"][kk][m], g["bins"][kk][m]]
        return out
    res = {"code": code, "ts": ts, "pix": pix, "hbeam": g["hbeam"], "h_low": g["h_low"], "cbb0": g["cbb0"], "s": g["s"],
           "lat": float(g["lat0"]), "lon": float(g["lon0"]), "h0": float(g["h0"]), "elev": els[0],
           "wl": root.get("how", {}).get("wavelength")}
    Z = pick(sz)
    res["Z"] = np.where(np.isfinite(Z), Z + g["corr"], Z)        # corecția de blocare parțială (dB)
    res["SDZ"] = pick({nm: texture(np.where(np.isfinite(decode(sz[nm])), decode(sz[nm]), np.nan)) for nm in tn if nm in sz})
    for p in ("ZDR", "KDP", "RhoHV"):
        try:
            _, ss = read_volume(code, ts, p, tn)
            res[p] = pick(ss)
        except Exception as e:
            log.warning("%s %s: %s lipsește (%s)", code, ts[:12], p, e)
            res[p] = np.full(pix.size, np.nan, np.float32)
    try:
        _, sv = read_volume(code, ts, "V", tn + ["dataset4"])
        res["V"] = pick(sv)
        res["vad"] = vad(sv["dataset4"], res["h0"]) if "dataset4" in sv else None
    except Exception as e:
        res["V"] = np.full(pix.size, np.nan, np.float32); res["vad"] = None
    res["etop"] = np.full(pix.size, np.nan, np.float32)
    try:
        r2, s2 = read_volume(code, ts, "Height", ["dataset1"])
        if "dataset1" in s2:
            wh = dict(r2.get("where", {}))
            e = sample_image(s2["dataset1"], wh, GLAT.ravel()[pix], GLON.ravel()[pix])
            e = np.where(np.isfinite(e) & (e > 0), e, np.nan)
            if np.nanmax(np.append(e, 0)) > 100:
                e = e / 1000.0
            res["etop"] = e.astype(np.float32)
    except Exception:
        pass
    res["ml"] = None; res["vobs"] = None
    res["bw"] = float(root.get("how", {}).get("beamwidth", root.get("how", {}).get("beamwH", 1.0)) or 1.0)
    if want_ml:
        try:
            res["ml"], res["vobs"] = melting_layer(code, ts)
        except Exception as e:
            log.info("%s: stratul de topire nu poate fi estimat (%s)", code, e)
    for p in ("Z", "ZDR", "KDP", "RhoHV", "SDZ", "V"):
        res[p] = np.where(have, res[p], np.nan).astype(np.float32)
    res["valid"] = have & ~np.isnan(res["Z"])
    try:
        res["wl"] = float(res["wl"])
    except (TypeError, ValueError):
        res["wl"] = None
    return res


# ---------------- clasificarea hidrometeorilor ----------------
# Clasele algoritmului de clasificare a hidrometeorilor (Park et al. 2009, Wea. Forecasting 24, 730–748),
# plus „fără ecou” pe poziția 0. Funcții de apartenență trapezoidale pe Z, ZDR, log KDP, RhoHV și SD(Z);
# textura ΦDP nu este publicată de ANM și lipsește din calcul.
CLASSES = ["fără ecou", "ecouri de sol / propagare anormală", "ecouri biologice (insecte, păsări)", "ninsoare uscată",
           "ninsoare umedă (strat de topire)", "cristale de gheață", "măzăriche (graupel)", "picături mari",
           "ploaie slabă–moderată", "ploaie puternică", "ploaie cu grindină"]
CLS_COL = ["#00000000", "#8a8a8a", "#b89a6a", "#bfe6ff", "#f6b12f", "#e9d8ff", "#c06ad6", "#58c45b", "#2fb35a", "#0b6e2b", "#e2391f"]


def _trap(x, a, b, c, d):
    x = np.asarray(x, dtype=np.float64)
    up = np.clip((x - a) / np.maximum(b - a, 1e-9), 0, 1)
    dn = np.clip((d - x) / np.maximum(d - c, 1e-9), 0, 1)
    return np.where(np.isfinite(x), np.minimum(up, dn), np.nan)


def hca(Z, ZDR, KDP, RHO, SDZ, beam_h, ml):
    """clasificare fuzzy (Park et al. 2009); ml = (bază, mijloc, vârf) strat de topire în m, sau None"""
    f1 = -0.50 + 2.50e-3 * Z + 7.50e-4 * Z ** 2
    f2 = 0.68 - 4.81e-2 * Z + 2.92e-3 * Z ** 2
    f3 = 1.42 + 6.67e-2 * Z + 4.85e-4 * Z ** 2
    g1 = -44.0 + 0.8 * Z
    g2 = -22.0 + 0.5 * Z
    LK = np.where(np.isfinite(KDP), np.where(KDP > 0, 10 * np.log10(np.maximum(KDP, 1e-6)), -30.0), np.nan)   # KDP lipsă = nefolosit
    LK = np.where(Z >= 40, LK, np.nan)     # KDP e prea zgomotos la reflectivități mici: folosit doar peste 40 dBZ (Park et al. 2009)
    # (Z, ZDR, LKDP, RhoHV, SD(Z)) — câte 4 puncte ale trapezului; ponderi după Park et al. (2009)
    P = {
        1: ((15, 20, 70, 80), (-4, -2, 1, 2), (-30, -25, 10, 20), (0.5, 0.6, 0.9, 0.95), (2, 4, 35, 50)),
        2: ((5, 10, 20, 30), (0, 2, 10, 12), (-30, -25, 10, 10), (0.3, 0.5, 0.8, 0.83), (1, 2, 4, 7)),
        3: ((5, 10, 35, 40), (-0.3, 0.0, 0.3, 0.6), (-30, -25, 10, 20), (0.95, 0.98, 1.0, 1.01), (0, 0.5, 3, 6)),
        4: ((25, 30, 50, 60), (0.5, 1.0, 2.0, 3.0), (-30, -25, 10, 20), (0.88, 0.92, 0.95, 0.985), (0, 0.5, 3, 6)),
        5: ((0, 5, 20, 25), (0.1, 0.4, 3.0, 3.3), (-5, 0, 10, 15), (0.95, 0.98, 1.0, 1.01), (0, 0.5, 3, 6)),
        6: ((25, 35, 50, 55), (-0.3, 0.0, f1, f1 + 0.3), (-30, -25, 10, 20), (0.9, 0.97, 1.0, 1.01), (0, 0.5, 3, 6)),
        7: ((20, 25, 45, 50), (f2 - 0.3, f2, f3, f3 + 1.0), (g1 - 1, g1, g2, g2 + 1), (0.92, 0.95, 1.0, 1.01), (0, 0.5, 3, 6)),
        8: ((5, 10, 45, 50), (f1 - 0.3, f1, f2, f2 + 0.5), (g1 - 1, g1, g2, g2 + 1), (0.95, 0.97, 1.0, 1.01), (0, 0.5, 3, 6)),
        9: ((40, 45, 55, 60), (f1 - 0.3, f1, f2, f2 + 0.5), (g1 - 1, g1, g2, g2 + 1), (0.92, 0.95, 1.0, 1.01), (0, 0.5, 3, 6)),
        10: ((45, 50, 75, 80), (-0.3, 0.0, f1, f1 + 0.5), (-10, -4, g1, g1 + 1), (0.75, 0.8, 0.97, 1.0), (0, 0.5, 3, 6)),
    }
    W = {1: (0.2, 0.4, 1.0, 1.0, 0.6), 2: (0.4, 0.6, 1.0, 0.8, 0.8), 3: (1.0, 0.8, 0.6, 1.0, 0.6),
         4: (0.6, 0.8, 0.4, 1.0, 0.6), 5: (1.0, 0.6, 1.0, 0.6, 0.6), 6: (0.8, 1.0, 0.6, 1.0, 0.6),
         7: (0.8, 1.0, 1.0, 0.6, 0.6), 8: (1.0, 0.8, 1.0, 1.0, 0.6), 9: (1.0, 0.8, 1.0, 1.0, 0.6),
         10: (1.0, 0.8, 1.0, 0.8, 0.6)}
    X = (Z, ZDR, LK, RHO, SDZ)
    score = np.full((11,) + Z.shape, -1.0)
    for k, pars in P.items():
        num = np.zeros(Z.shape); den = np.zeros(Z.shape)
        for x, (a, b, c, d), w in zip(X, pars, W[k]):
            m = _trap(x, a, b, c, d)
            ok = np.isfinite(m)
            num += np.where(ok, w * m, 0.0); den += np.where(ok, w, 0.0)
        score[k] = np.where(den > 0, num / np.maximum(den, 1e-9), -1.0)
    # clasele definite de intensitate nu pot fi alese în afara intervalului lor de reflectivitate (apartenență 0 pe Z):
    # ploaie puternică sub 40 dBZ, ploaie cu grindină sub 45 dBZ (agregarea aditivă le-ar putea alege altfel)
    for k in (9, 10):
        a, b_, c_, d_ = P[k][0]
        score[k][~((Z > a) & (Z < d_))] = -1
    # constrângeri după poziția fasciculului față de stratul de topire (Park et al. 2009, sect. 3)
    if ml is not None and beam_h is not None:
        bh = np.nan_to_num(beam_h, nan=0.0)
        below = bh < ml[0]; above = bh > ml[2]
        for k in (3, 4, 5, 6):
            score[k][below] = -1           # sub stratul de topire: fără zăpadă/cristale/măzăriche
        for k in (7, 8, 9):
            score[k][above] = -1           # deasupra lui: fără ploaie
        score[4][~(~below & ~above)] = np.minimum(score[4][~(~below & ~above)], 0.5)   # zăpada umedă e favorizată doar în strat
    c = np.argmax(score, 0).astype(np.uint8)
    c[~(np.isfinite(Z) & (Z >= 5))] = 0
    conf = np.max(score, 0)
    return c, conf



# ---------------- temperatura umedă ----------------
def wet_bulb(t, td):
    """temperatura umedă (°C), Stull (2011) din T și umezeala relativă"""
    es = lambda x: 6.112 * np.exp(17.67 * x / (x + 243.5))
    rh = np.clip(100 * es(td) / es(t), 1, 100)
    return (t * np.arctan(0.151977 * np.sqrt(rh + 8.313659)) + np.arctan(t + rh) - np.arctan(rh - 1.676331)
            + 0.00391838 * rh ** 1.5 * np.arctan(0.023101 * rh) - 4.686035)



# ---------------- intensitate ----------------
def rain_rate(Z, ZDR, KDP, cls, wl_cm):
    """intensitatea (mm/h) în funcție de clasa de hidrometeori — algoritmul NEXRAD de estimare polarimetrică
       (Giangrande & Ryzhkov 2008, J. Appl. Meteor. Climatol. 47, 2445–2462), banda S:
         ploaie, ploaie puternică, picături mari: R(Z,ZDR) = 1.42e-2 Z^0.77 Zdr^-1.67
         ploaie cu grindină: R(KDP) = 44 |KDP|^0.822 (dacă KDP lipsește: R(Z) cu plafon 53 dBZ)
         măzăriche 0.8·R(Z); ninsoare umedă (strat de topire) 0.6·R(Z); ninsoare uscată și cristale 2.8·R(Z),
         cu R(Z) = 1.70e-2 Z^0.714.
       Banda C: aceleași reguli cu relațiile Bringi & Chandrasekar (2001). ZDR în afara intervalului fizic al ploii
       (−0.5…5 dB) → R(Z)."""
    zdb = np.nan_to_num(Z, nan=-30.0)
    zl = 10 ** (zdb / 10.0)
    zdr_db = np.asarray(ZDR, dtype=np.float64)
    zdr_ok = np.isfinite(zdr_db) & (zdr_db >= -0.5) & (zdr_db <= 5.0)
    zdr = 10 ** (np.where(zdr_ok, zdr_db, 0.0) / 10.0)
    kdp = np.asarray(KDP, dtype=np.float64)
    zc = 10 ** (np.minimum(zdb, 53.0) / 10.0)          # plafon de 53 dBZ (practica NEXRAD) pentru grindină
    if wl_cm is not None and wl_cm < 7:     # banda C
        RZ = lambda z: (z / 200.0) ** (1 / 1.6)
        rzd = 6.7e-3 * zl ** 0.927 * zdr ** -3.43
        rk = 24.68 * np.abs(np.nan_to_num(kdp)) ** 0.81
    else:                                   # banda S
        RZ = lambda z: 1.70e-2 * z ** 0.714
        rzd = 1.42e-2 * zl ** 0.770 * zdr ** -1.67
        rk = 44.0 * np.abs(np.nan_to_num(kdp)) ** 0.822
    rz = RZ(zl)
    rain = np.where(zdr_ok, rzd, rz)
    r = np.zeros(zl.shape)
    r = np.where(np.isin(cls, (7, 8, 9)), rain, r)
    r = np.where(cls == 10, np.where(np.isfinite(kdp) & (kdp > 0), rk, RZ(zc)), r)
    r = np.where(cls == 6, 0.8 * rz, r)
    r = np.where(cls == 4, 0.6 * rz, r)
    r = np.where(np.isin(cls, (3, 5)), 2.8 * rz, r)
    r = np.where(np.isfinite(Z), np.clip(r, 0, 200), 0.0)
    return r.astype(np.float32)


# ---------------- deplasare ----------------
def motion(prev, cur, dt_min):
    a = np.nan_to_num(prev, nan=0.0); b = np.nan_to_num(cur, nan=0.0)
    a = np.where(a > 15, a - 15, 0); b = np.where(b > 15, b - 15, 0)
    if (a > 0).mean() < 0.01 or (b > 0).mean() < 0.01:
        return None
    F = np.fft.rfft2(a) * np.conj(np.fft.rfft2(b))
    cc = np.fft.irfft2(F, s=a.shape)
    k = int(np.argmax(cc)); dy, dx = np.unravel_index(k, cc.shape)
    if dy > a.shape[0] // 2: dy -= a.shape[0]
    if dx > a.shape[1] // 2: dx -= a.shape[1]
    dy, dx = -dy, -dx                      # deplasarea ecourilor de la prev la cur (pixeli = km)
    if abs(dx) > 40 or abs(dy) > 40:
        return None
    vx, vy = dx / (dt_min / 60.0), -dy / (dt_min / 60.0)     # km/h, est / nord
    spd = math.hypot(vx, vy)
    to = (math.degrees(math.atan2(vx, vy)) + 360) % 360
    return {"vx": vx, "vy": vy, "kmh": spd, "spre": to}


def bearing_txt(deg):
    names = ["N", "NNE", "NE", "ENE", "E", "ESE", "SE", "SSE", "S", "SSV", "SV", "VSV", "V", "VNV", "NV", "NNV"]
    return names[int((deg % 360) / 22.5 + 0.5) % 16]



# ---------------- palete ----------------
PAL = {
    "dbz": ([5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65],
            ["#9ad6f2", "#5bb4e6", "#2f86d0", "#29a85c", "#57c84d", "#a7dc42", "#f2e33a", "#f6b12f", "#f07b26", "#e2391f", "#b5162a", "#ce38c4", "#ffffff"]),
    "rate": ([0.1, 0.5, 1, 2, 4, 7, 10, 20, 30, 50, 80],
             ["#c6e9ff", "#8fd0ff", "#4fa8f0", "#2a75d0", "#2fb35a", "#9bd543", "#f2e33a", "#f6a12f", "#e8452b", "#b8163c", "#d23fd0"]),
    "vrad": ([-30, -20, -14, -9, -5, -2, -0.5, 0.5, 2, 5, 9, 14, 20, 30],
             ["#0b3d91", "#1a5fc7", "#2f86e6", "#62aef2", "#9dd1f7", "#cfe9fb", "#e0e0e0", "#fbd3c9", "#f7a68f", "#f07a5d", "#e2492f", "#c21f1f", "#8f0d0d", "#5c0505"]),
    "zdr": ([-2, -0.5, 0, 0.3, 0.6, 1, 1.5, 2, 3, 4, 6],
            ["#3d3d9c", "#5a7fd6", "#7fb6e6", "#a9e0d2", "#7fd18b", "#c8e65a", "#f2e33a", "#f6b12f", "#ec6b26", "#d0302a", "#a3197a"]),
    "kdp": ([-1, -0.25, 0.1, 0.3, 0.6, 1, 1.5, 2.5, 4],
            ["#6b6bb5", "#a6a6d6", "#d8f0e0", "#9be08e", "#58c45b", "#f2e33a", "#f69a2f", "#e2391f", "#a3197a"]),
    "rho": ([0.70, 0.80, 0.85, 0.90, 0.93, 0.95, 0.97, 0.98, 0.99, 0.995],
            ["#3d1f6b", "#6c3fa8", "#3d6fd6", "#3fb3d6", "#5fd18b", "#b8e05a", "#f2e33a", "#f6a12f", "#e8452b", "#b5162a"]),
    "etop": ([0.5, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12],
             ["#cfe9fb", "#9dd1f7", "#62aef2", "#2fb35a", "#9bd543", "#f2e33a", "#f6b12f", "#ec6b26", "#d0302a", "#a3197a", "#ffffff"]),
    "acc": ([0.1, 0.5, 1, 2, 5, 10, 15, 20, 30, 50, 75, 100],
            ["#c6e9ff", "#8fd0ff", "#4fa8f0", "#2a75d0", "#2fb35a", "#9bd543", "#f2e33a", "#f6a12f", "#e8452b", "#b8163c", "#d23fd0", "#7a1fa2"]),
    "beam": ([0, 500, 1000, 1500, 2000, 2500, 3000, 4000],
             ["#1d7a3b", "#57b05a", "#a7d06a", "#e8e26a", "#f2b84a", "#e8803a", "#d0482a", "#9c1d2a"]),
}




# ---------------- hartă statică de ecouri fixe ----------------
# Ecourile fixe (sol, clădiri, turbine eoliene, propagare anormală persistentă) se recunosc după frecvența de apariție:
# un punct cu ecou în peste jumătate din volume și mult mai des decât împrejurimile (~30 km) este ecou nemeteorologic —
# principiul hărților de ecouri fixe din lanțurile operaționale OPERA/BALTRAD (Ośrodka et al. 2014, Atmos. Meas. Tech.).
# Precipitația, chiar persistentă, apare pe arii largi, deci nu depășește mult frecvența din jur. Turbinele eoliene
# trec de filtrele polarimetrice și Doppler (pale în mișcare), de aceea e nevoie de harta statică (Isom et al. 2009).
CLUT_ALPHA_MIN = 1.0 / 576          # memorie ~2 zile la 5 minute
CLUT_MIN_N = 12                     # o oră de volume înainte de a fi aplicată


def clutter_update(code, res):
    pix = res["pix"]
    p = os.path.join(CACHE, "clutter_%s.npz" % code)
    ind = np.where(res["valid"], (np.nan_to_num(res["Z"], nan=-99.0, neginf=-99.0) >= 20).astype(np.float32), np.nan)
    f, n = None, 0
    try:
        with np.load(p) as d:
            if d["f"].shape == pix.shape:
                f, n = d["f"].astype(np.float32), int(d["n"])
    except Exception:
        pass
    old = os.path.join(CACHE, "ecouri_fixe_%s.npz" % code)
    if f is None and os.path.exists(old):
        # pornire din harta versiunii anterioare (grilă de 1 km ±172 km în jurul Galațiului, aceeași proiecție)
        try:
            with np.load(old) as d:
                fo, no = d["f"].astype(np.float32), int(d["n"])
            if fo.shape == (345, 345):
                full = np.full((GH, GW), np.nan, np.float32)
                full[YN - 172:YN - 172 + 345, -172 - XW:-172 - XW + 345] = fo
                fv = full.ravel()[pix]
                f, n = np.nan_to_num(fv).astype(np.float32), no
                log.info("%s: harta de ecouri fixe pornită din versiunea anterioară (%d cadre)", code, no)
        except Exception as e:
            log.info("%s: harta veche de ecouri fixe nu poate fi folosită (%s)", code, e)
    if f is None:
        f = np.where(np.isfinite(ind), ind, 0).astype(np.float32)
    n += 1
    a = max(1.0 / n, CLUT_ALPHA_MIN)
    f = np.where(np.isfinite(ind), (1 - a) * f + a * np.nan_to_num(ind), f).astype(np.float32)
    try:
        np.savez(p + ".tmp.npz", f=f, n=n)
        os.replace(p + ".tmp.npz", p)
    except OSError as e:
        log.warning("%s: harta de ecouri fixe nu poate fi salvată (%s)", code, e)
    if n < CLUT_MIN_N:
        return np.zeros(pix.shape, bool), n
    full = np.zeros(GH * GW, np.float32); full[pix] = f
    full = full.reshape(GH, GW)
    from numpy.lib.stride_tricks import sliding_window_view as swv
    k = 3
    H, W = GH - GH % k, GW - GW % k
    fc = full[:H, :W].reshape(H // k, k, W // k, k).mean((1, 3))
    q = 5
    med = np.median(swv(np.pad(fc, q, mode="edge"), (2 * q + 1, 2 * q + 1)), axis=(-1, -2))
    med = np.repeat(np.repeat(med, k, 0), k, 1)
    med = np.pad(med, ((0, GH - med.shape[0]), (0, GW - med.shape[1])), mode="edge").ravel()[pix]
    return (f > 0.5) & (f - med > 0.3), n


# ---------------- temperatura la sol din stații ----------------
_MET = {}


def met_points(lat, lon, h):
    """T, Td și temperatura umedă la sol în puncte: stațiile ANM aduse la nivelul mării (T −6,5 °C/km, Td −2 °C/km),
       interpolate IDW (8 vecini, ≤ 150 km) și readuse la altitudinea reliefului; None dacă nu sunt date"""
    if "st" not in _MET:
        _MET["st"] = None
        try:
            store = json.load(open(os.path.join(HERE, "arhiva_orara.json"), encoding="utf-8"))
            st = json.loads(open(os.path.join(HERE, "data", "stations.js"), encoding="utf-8").read().split("=", 1)[1].rstrip().rstrip(";"))["st"]
            keys = sorted({k for v in store.values() for k in v})
            for key in keys[::-1][:3]:
                pts = [(s[2], s[3], s[4], store[s[0]][key]) for s in st if s[0] in store and key in store[s[0]]]
                pts = [(lo, la, z, float(r[2]), float(r[5])) for lo, la, z, r in pts if len(r) > 5 and r[2] is not None and r[5] is not None]
                if len(pts) >= 15:
                    a = np.array(pts, float)
                    _MET["st"] = (a[:, 0], a[:, 1], a[:, 3] + 0.0065 * a[:, 2], a[:, 4] + 0.0020 * a[:, 2], key, len(pts))
                    break
        except Exception as e:
            log.info("temperatura la stații nu e disponibilă (%s)", e)
    if _MET["st"] is None or len(lat) == 0:
        return None
    lo, la, tsl, dsl, key, n = _MET["st"]
    T = np.full(len(lat), np.nan); D = np.full(len(lat), np.nan)
    for a in range(0, len(lat), 50000):
        d = np.hypot((lon[a:a + 50000, None] - lo[None, :]) * KX, (lat[a:a + 50000, None] - la[None, :]) * KY)
        k = min(8, len(lo))
        idx = np.argpartition(d, k - 1, axis=1)[:, :k]
        dd = np.take_along_axis(d, idx, 1); w = 1.0 / np.maximum(dd, 2.0) ** 2
        t = (w * tsl[idx]).sum(1) / w.sum(1); td = (w * dsl[idx]).sum(1) / w.sum(1)
        far = dd.min(1) > 150
        t[far] = np.nan; td[far] = np.nan
        T[a:a + 50000] = t; D[a:a + 50000] = td
    T = T - 0.0065 * h; D = np.minimum(D - 0.0020 * h, T)
    return {"T": T, "Td": D, "Tw": wet_bulb(T, D), "key": key, "n": n}


SFC = ["–", "ploaie", "lapoviță (ploaie cu ninsoare)", "ninsoare", "ploaie care îngheață (polei)", "grindină / măzăriche"]
SFC_COL = ["#00000000", "#2fb35a", "#f6b12f", "#7fd0ff", "#ff4fa3", "#e2391f"]


def surface_type(cls, h, mlb, met):
    """tipul precipitației la sol pe relieful real (vectori de puncte cu precipitații):
       - cu strat de topire detectat (baza mlb, m): ninsoare unde relieful e peste bază, lapoviță în cei 300 m de sub
         bază, ploaie dedesubt; T ≤ 0 °C la sol sub un strat cald → ploaie care îngheață; Tw ≤ 0 °C → ninsoare;
       - fără strat de topire: după temperatura umedă la sol (ninsoare ≤ 1 °C, lapoviță 1–2 °C, ploaie > 2 °C;
         Matsuo et al. 1981; Ding et al. 2014);
       - fără nicio informație de temperatură: după clasa radar (zăpadă în fascicul → ninsoare);
       - grindina/măzărichea după clasa radar."""
    t = np.ones(cls.shape, np.uint8)
    has_ml = np.isfinite(mlb)
    t[has_ml & (h >= mlb - 300)] = 2
    t[has_ml & (h >= mlb)] = 3
    if met is not None:
        T, Tw = met["T"], met["Tw"]
        okm = np.isfinite(Tw)
        t[has_ml & okm & (T <= 0.0) & (h < mlb - 500)] = 4
        t[has_ml & okm & (Tw <= 0.0) & (h >= mlb - 500)] = 3
        nm = ~has_ml & okm
        t[nm & (Tw <= 2.0)] = 2
        t[nm & (Tw <= 1.0)] = 3
        none = ~has_ml & ~okm
    else:
        none = ~has_ml
    t[none & np.isin(cls, (3, 4, 5))] = 3
    t[np.isin(cls, (6, 10))] = 5
    return t


# ---------------- cumul orar ----------------
def hour_end(ts):
    t = ts_time(ts)
    return t.replace(minute=0) + timedelta(hours=1)


class Hours:
    """sume pe ore (încheiate la HH:00) pe grila de 1 km: S = Σ R·5/60 (mm), N = numărul de volume valide"""

    def __init__(self):
        self.h = {}

    def get(self, he):
        k = he.strftime("%Y%m%d%H")
        if k not in self.h:
            p = os.path.join(QPE, "h1_%s.npz" % k)
            S = np.zeros(GH * GW, np.float32); N = np.zeros(GH * GW, np.uint8); done = []
            if os.path.exists(p):
                try:
                    with np.load(p) as d:
                        S, N, done = d["S"].astype(np.float32), d["N"].astype(np.uint8), list(d["done"])
                except Exception as e:
                    log.warning("cumulul orei %s nu poate fi citit (%s); îl refac", k, e)
            self.h[k] = {"S": S, "N": N, "done": [str(x) for x in done], "dirty": False}
        return self.h[k]

    def add(self, ts, rate, qvalid):
        e = self.get(hour_end(ts))
        if ts[:12] in e["done"]:
            return
        e["S"] += np.where(qvalid, rate * (5.0 / 60.0), 0.0).astype(np.float32)
        e["N"] += qvalid.astype(np.uint8)
        e["done"].append(ts[:12]); e["dirty"] = True

    def save(self):
        for k, e in self.h.items():
            if e["dirty"]:
                p = os.path.join(QPE, "h1_%s.npz" % k)
                np.savez_compressed(p + ".tmp.npz", S=e["S"], N=e["N"], done=np.array(e["done"]))
                os.replace(p + ".tmp.npz", p)
                e["dirty"] = False


_AIDX = None


def to_aladin(mm):
    """media punctelor de 1 km din fiecare celulă a grilei ALADIN (2,35 × 2,33 km); NaN unde sub jumătate sunt valide"""
    global _AIDX
    if _AIDX is None:
        ci = np.round((GLON.ravel() - A_LON0) / A_DLON).astype(np.int64)
        cj = np.round((GLAT.ravel() - A_LAT0) / A_DLAT).astype(np.int64)
        ok = (ci >= 0) & (ci < A_W) & (cj >= 0) & (cj < A_H)
        cell = np.where(ok, cj * A_W + ci, -1)
        tot = np.bincount(cell[ok], minlength=A_W * A_H)
        _AIDX = (cell, ok, tot)
    cell, ok, tot = _AIDX
    v = mm.ravel()
    good = ok & np.isfinite(v)
    s = np.bincount(cell[good], weights=v[good], minlength=A_W * A_H)
    n = np.bincount(cell[good], minlength=A_W * A_H)
    out = np.where((n >= 1) & (n * 2 >= tot), s / np.maximum(n, 1), np.nan)
    return out.reshape(A_H, A_W).astype(np.float32)


def finalize_hours(hours, avail_minutes, now, sdone):
    """închide orele complete: mm = S·12/N unde N ≥ 10 (≥ 83% din volume), altfel necunoscut"""
    done_any = []
    for nm in sorted(os.listdir(QPE)):
        m = re.match(r"h1_(\d{10})\.npz$", nm)
        if not m:
            continue
        he = datetime.strptime(m.group(1), "%Y%m%d%H").replace(tzinfo=timezone.utc)
        if now < he + timedelta(minutes=20):
            continue
        e = hours.get(he)
        slots = [(he - timedelta(minutes=60 - 5 * i)).strftime("%Y%m%d%H%M") for i in range(12)]
        pending = [s for s in slots if s not in e["done"] and s not in sdone and s in avail_minutes]
        if pending and now < he + timedelta(hours=LOOKBACK_H):
            continue
        N = e["N"].astype(np.float32)
        mm = np.where(N >= 10, e["S"] * 12.0 / np.maximum(N, 1), np.nan).reshape(GH, GW).astype(np.float32)
        k = m.group(1)
        np.savez_compressed(os.path.join(QPE, "k1_%s.npz" % k), mm=mm.astype(np.float16) if False else mm,
                            nvol=np.array(len(e["done"])))
        ro = to_aladin(mm)
        np.savez_compressed(os.path.join(QPE, "ro_%s.npz" % k), mm=ro, nvol=np.array(len(e["done"])),
                            lon0=A_LON0, lat0=A_LAT0, dlon=A_DLON, dlat=A_DLAT)
        os.remove(os.path.join(QPE, nm))
        hours.h.pop(k, None)
        done_any.append(k)
        log.info("ora %s UTC închisă: %d volume compozit; valid pe %.0f%% din România; maxim %.1f mm/h",
                 k, len(e["done"]), 100 * np.mean(np.isfinite(ro)), float(np.nanmax(np.append(ro.ravel(), 0))))
    # păstrare: 1 km 26 de ore (cumulul de 24 h al paginii), grila ALADIN cel mult 48 de ore — obs_harti.py le șterge
    # mai devreme, imediat după îmbinarea zilei cu pluviometrele (rămâne doar rezultatul)
    lim1 = (now - timedelta(hours=26)).strftime("%Y%m%d%H"); lim2 = (now - timedelta(hours=48)).strftime("%Y%m%d%H")
    for nm in os.listdir(QPE):
        m = re.match(r"(k1|ro|h1)_(\d{10})\.npz$", nm)
        if m and ((m.group(1) == "k1" and m.group(2) < lim1) or (m.group(1) == "ro" and m.group(2) < lim2)
                  or (m.group(1) == "h1" and m.group(2) < lim2)):
            os.remove(os.path.join(QPE, nm))
    return done_any


def accum_1km(n_hours, now):
    """suma ultimelor n ore încheiate (1 km); NaN unde lipsește vreo oră"""
    he = now.replace(minute=0, second=0, microsecond=0)
    for _ in range(3):
        if os.path.exists(os.path.join(QPE, "k1_%s.npz" % he.strftime("%Y%m%d%H"))):
            break
        he -= timedelta(hours=1)
    out = None; got = 0
    for i in range(n_hours):
        p = os.path.join(QPE, "k1_%s.npz" % (he - timedelta(hours=i)).strftime("%Y%m%d%H"))
        if not os.path.exists(p):
            return None, he, got
        with np.load(p) as d:
            a = d["mm"].astype(np.float32)
        out = a if out is None else out + a
        got += 1
    return out, he, got


# ---------------- compozitele recente (pentru deplasare și prognoză) ----------------
COMP_KEEP_MIN = 180


def save_comp(m, C):
    """intensitatea compozită (mm/h; NaN = nevăzut / ecou fix) la fiecare 5 minute, păstrată 3 ore"""
    r = np.where(C["qvalid"] | (C["valid"] & (C["cls"] != 1)), C["rate"], np.nan).astype(np.float16)
    p = os.path.join(CACHE, "comp_%s.npy" % m)
    np.save(p, r)
    # reflectivitatea compozită a ecourilor de precipitații (dBZ; „fără ecou” = NC_ZZERO; NaN = nevăzut)
    z = np.where(C["valid"] & (C["cls"] != 1), np.where((C["cls"] >= 3) & np.isfinite(C["Z"]), C["Z"], NC_ZZERO), np.nan).astype(np.float16)
    np.save(os.path.join(CACHE, "compz_%s.npy" % m), z)
    lim = (ts_time(m + "0000") - timedelta(minutes=COMP_KEEP_MIN)).strftime("%Y%m%d%H%M")
    for nm in os.listdir(CACHE):
        mm = re.match(r"compz?_(\d{12})\.npy$", nm)
        if mm and mm.group(1) < lim:
            os.remove(os.path.join(CACHE, nm))


def load_comp(m, kind=""):
    p = os.path.join(CACHE, "comp%s_%s.npy" % (kind, m))
    return np.load(p).astype(np.float32) if os.path.exists(p) else None


# ---------------- clasificare, control al calității, intensitate (pe un radar) ----------------
def classify(res, ml, prof=None):
    """HCA + ecouri fixe + intensitate pentru un radar; ml = [bază, mijloc, vârf] (m) sau None;
       prof = profilul vertical (VPR) al radarului"""
    Z = np.where(np.isfinite(res["Z"]), res["Z"], np.nan)
    bh = res["hbeam"]
    mlt = None if ml is None else tuple(np.full(Z.shape, float(x)) for x in ml[:3])
    c, cf = hca(Z, res["ZDR"], res["KDP"], res["RhoHV"], res["SDZ"], bh, mlt)
    fixed, nfr = clutter_update(res["code"], res)
    echo = np.isfinite(Z) & (Z >= 5)
    c = np.where(echo & fixed, 1, c).astype(np.uint8)
    res["fixed_km2"] = int((fixed & echo).sum()); res["clut_n"] = nfr
    res["cls"] = c
    res["rate"] = np.where(c >= 3, rain_rate(Z, res["ZDR"], res["KDP"], c, res["wl"]), 0.0).astype(np.float32)
    # QPE: punct valid dacă radarul vede (elevație neblocată) și nu e ecou fix / de sol (care ar putea ascunde ploaia)
    res["qvalid"] = res["valid"] & ~fixed & (c != 1)
    res["mlb"] = np.nan if ml is None else float(ml[0])
    res["dzv"] = vpr_correction(prof, res["hbeam"], res["s"], res.get("bw", 1.0))
    res["vpr_conv"] = bool(prof and prof.get("conv"))


def composite(per):
    """compozit „cel mai jos fascicul”: în fiecare punct, radarul cu fasciculul (ales după blocare) cel mai jos"""
    n = GH * GW
    C = {"h": np.full(n, np.inf, np.float32), "who": np.full(n, -1, np.int8)}
    for p in ("Z", "ZDR", "KDP", "RhoHV", "SDZ", "etop", "rate", "mlb", "dzv", "wl"):
        C[p] = np.full(n, np.nan, np.float32)
    C["cls"] = np.zeros(n, np.uint8); C["qvalid"] = np.zeros(n, bool); C["valid"] = np.zeros(n, bool)
    for i, code in enumerate(RCODES):
        r = per.get(code)
        if r is None:
            continue
        ok = r["valid"]
        idx = r["pix"][ok]
        take = r["hbeam"][ok] < C["h"][idx]
        idx = idx[take]; sel = np.flatnonzero(ok)[take]
        C["h"][idx] = r["hbeam"][sel]; C["who"][idx] = i
        for p in ("Z", "ZDR", "KDP", "RhoHV", "SDZ", "etop", "rate", "dzv"):
            C[p][idx] = r[p][sel]
        C["mlb"][idx] = r["mlb"]; C["wl"][idx] = r["wl"] if r["wl"] else np.nan
        C["cls"][idx] = r["cls"][sel]; C["qvalid"][idx] = r["qvalid"][sel]; C["valid"][idx] = True
    for k in C:
        C[k] = C[k].reshape(GH, GW)
    # pete izolate (sub 3 vecini cu precipitații din 8) = zgomot; pe compozit, ca să nu depindă de radar
    met = C["cls"] >= 3
    nb = sum(np.roll(np.roll(met, di, 0), dj, 1) for di in (-1, 0, 1) for dj in (-1, 0, 1)) - met
    lone = met & (nb < 3)
    C["cls"][lone] = 0; C["rate"][lone] = 0.0
    C["rate"] = np.where(C["valid"], np.where(C["cls"] >= 3, C["rate"], 0.0), np.nan).astype(np.float32)
    C["etop"] = np.where(C["cls"] >= 3, C["etop"], np.nan).astype(np.float32)
    for p in ("ZDR", "KDP", "RhoHV"):
        C[p] = np.where(C["cls"] >= 3, C[p], np.nan).astype(np.float32)
    C["h"] = np.where(np.isfinite(C["h"]), C["h"], np.nan).astype(np.float32)
    # tip la sol
    S = np.zeros((GH, GW), np.uint8)
    pm = C["cls"] >= 3
    if pm.any():
        lat, lon = GLAT[pm], GLON[pm]
        hz = relief_grid()[pm].astype(np.float64)
        met_ = met_points(lat, lon, hz)
        S[pm] = surface_type(C["cls"][pm], hz, C["mlb"][pm].astype(np.float64), met_)
        C["met_key"] = met_["key"] if met_ else None
    else:
        C["met_key"] = None
    C["sfc"] = S
    # intensitatea la sol după corecția VPR (doar ecouri de precipitații necorvective, fără grindină/măzăriche)
    C["rate_nv"] = C["rate"].copy()
    v = pm & (np.nan_to_num(C["dzv"]) != 0) & ~np.isin(C["cls"], (6, 10)) & (S != 5)
    if v.any():
        C["rate"][v] = vpr_rate(C["Z"][v] + C["dzv"][v], C["ZDR"][v], C["cls"][v], S[v], C["wl"][v])
    C["vpr_px"] = int(v.sum())
    return C


def vpr_rate(Zg, ZDR, cls, sfc, wl):
    """intensitatea la sol din reflectivitatea adusă la sol: ploaie (și polei) — relațiile de ploaie ale algoritmului
       NEXRAD (R(Z,ZDR) unde fasciculul e în ploaie, altfel R(Z)); lapoviță — 0,6·R(Z) (ninsoare umedă, Giangrande &
       Ryzhkov 2008); ninsoare — Z = 2000·S² (Gunn & Marshall 1958, echivalent în apă). Coeficienții de clasă aplicați
       în fascicul deasupra stratului de topire (0,6 / 2,8) nu se mai folosesc aici: profilul îi înlocuiește."""
    out = np.zeros(Zg.shape, np.float32)
    for band_c in (False, True):
        b = (np.nan_to_num(wl, nan=10.0) < 7) == band_c
        if not b.any():
            continue
        wlc = 5.3 if band_c else 10.7
        rain_cls = np.where(np.isin(cls[b], (7, 8, 9)), cls[b], 8)
        zdr = np.where(np.isin(cls[b], (7, 8, 9)), ZDR[b], np.nan)
        r_rain = rain_rate(Zg[b], zdr, np.full(b.sum(), np.nan), rain_cls, wlc)
        zl = 10 ** (np.nan_to_num(Zg[b], nan=-30.0) / 10.0)
        rz = (zl / 200.0) ** (1 / 1.6) if band_c else 1.70e-2 * zl ** 0.714
        snow = np.sqrt(zl / 2000.0)
        sb = sfc[b]
        r = np.where(sb == 3, snow, np.where(sb == 2, 0.6 * rz, r_rain))
        out[b] = np.clip(np.where(np.isfinite(Zg[b]), r, 0.0), 0, 200)
    return out



# ---------------- date pentru pagină (valori exacte la mouse) ----------------
MISS, UNDET = -32768, -32767


def pack(fields, r0, c0, h, w):
    """gzip( 'RGD1' + lungime + antet JSON + matrice int16 ); valoare = întreg / scară"""
    hdr = {"r0": r0, "c0": c0, "h": h, "w": w, "f": []}
    blobs = []
    for name, arr, sc in fields:
        a = np.asarray(arr, dtype=np.float64)
        q = np.full(a.shape, MISS, np.int32)
        fin = np.isfinite(a)
        q[fin] = np.clip(np.round(a[fin] * sc), -32700, 32700)
        q[np.isneginf(a)] = UNDET
        blobs.append(q.astype("<i2").tobytes()); hdr["f"].append([name, sc])
    hj = json.dumps(hdr).encode()
    return gzip.compress(b"RGD1" + struct.pack("<I", len(hj)) + hj + b"".join(blobs), 6)


def crop(full):
    return full[PSL]


def radar_crop(r, name, fill=np.nan, dtype=np.float32):
    a = np.full(GH * GW, fill, dtype)
    a[r["pix"]] = r[name]
    return a.reshape(GH, GW)[PSL]


def bbox(mask):
    rows = np.flatnonzero(mask.any(1)); cols = np.flatnonzero(mask.any(0))
    if rows.size == 0:
        return 0, 0, 1, 1
    return int(rows[0]), int(cols[0]), int(rows[-1] - rows[0] + 1), int(cols[-1] - cols[0] + 1)


def write_frame(key, C, per, a1, a24, Hz=None):
    files = []
    fn = "%s_C.dat" % key
    sl = PSL
    fields = [("dbz", np.where(C["valid"], C["Z"], np.nan)[sl], 2), ("rate", C["rate"][sl], 100),
              ("sfc", np.where(C["valid"], C["sfc"], np.nan)[sl], 1), ("cls", np.where(C["valid"], C["cls"], np.nan)[sl], 1),
              ("zdr", C["ZDR"][sl], 100), ("kdp", C["KDP"][sl], 100), ("rho", C["RhoHV"][sl], 1000),
              ("etop", C["etop"][sl], 10), ("who", np.where(C["who"] >= 0, C["who"], np.nan)[sl], 1)]
    if a1 is not None:
        fields.append(("a1", a1[sl], 10))
    if a24 is not None:
        fields.append(("a24", a24[sl], 10))
    if Hz is not None:
        fields += [("vil", Hz["vil"][sl], 10), ("mesh", Hz["mesh"][sl], 10), ("poh", Hz["poh"][sl], 1), ("wg", Hz["wg"][sl], 1),
                   ("et18", Hz["et18"][sl] / 1000.0, 10), ("hail", Hz["hail"][sl].astype(float), 1),
                   ("wind", Hz["wind"][sl].astype(float), 1), ("risk", Hz["risk"][sl].astype(float), 1)]
    with open(os.path.join(OUT, fn), "wb") as fh:
        fh.write(pack(fields, 0, 0, 2 * HALF + 1, 2 * HALF + 1))
    files.append(fn)
    for code, r in per.items():
        cov = radar_crop(r, "valid", False, bool)
        r0, c0, h, w = bbox(cov)
        s2 = (slice(r0, r0 + h), slice(c0, c0 + w))
        Zf = radar_crop(r, "Z")
        flds = [("dbz", Zf[s2], 2), ("rate", radar_crop(r, "rate")[s2], 100), ("cls", radar_crop(r, "cls", 0, np.float32)[s2], 1),
                ("v", radar_crop(r, "V")[s2], 10), ("zdr", radar_crop(r, "ZDR")[s2], 100), ("kdp", radar_crop(r, "KDP")[s2], 100),
                ("rho", radar_crop(r, "RhoHV")[s2], 1000), ("etop", radar_crop(r, "etop")[s2], 10)]
        clsr = flds[2][1]
        clsr[~cov[s2]] = np.nan
        for i, (nm, arr, sc) in enumerate(flds):
            if nm in ("zdr", "kdp", "rho", "etop"):
                flds[i] = (nm, np.where(clsr >= 3, arr, np.nan), sc)
        fn = "%s_%s.dat" % (key, code)
        with open(os.path.join(OUT, fn), "wb") as fh:
            fh.write(pack(flds, r0, c0, h, w))
        files.append(fn)
        # geometria radarului (fixă): înălțimea fasciculului ales și blocarea la elevația cea mai joasă
        gp = os.path.join(OUT, "geo_%s.dat" % code)
        gk = hashlib.md5(r["pix"].tobytes() + r["hbeam"].tobytes()).hexdigest()[:10]
        need = True
        if os.path.exists(gp) and os.path.exists(gp + ".key"):
            need = open(gp + ".key").read().strip() != gk
        if need:
            hb = radar_crop(r, "hbeam")[s2]; cb = radar_crop(r, "cbb0")[s2]
            hb[~cov[s2] & ~np.isfinite(hb)] = np.nan
            with open(gp, "wb") as fh:
                fh.write(pack([("beam", hb, 1), ("cbb", cb, 100), ("agl", hb - relief_grid()[PSL][s2], 1)], r0, c0, h, w))
            open(gp + ".key", "w").write(gk)
    return files


def doppler_line(per, Hz):
    """vântul măsurat Doppler în nucleele convective, la mai puțin de 1 km deasupra solului (componenta radială =
       limita de jos a vitezei reale)"""
    if Hz is None:
        return []
    best = None
    rel = relief_grid().ravel()
    for code, r in per.items():
        agl = r["hbeam"] - rel[r["pix"]]
        m = np.isfinite(r["V"]) & (np.nan_to_num(r["Z"], nan=-99, neginf=-99) >= 35) & (agl < 1000) & (r["cls"] >= 3)
        if not m.any():
            continue
        k = int(np.argmax(np.where(m, np.abs(r["V"]), -1)))
        v = abs(float(r["V"][k])) * 3.6
        if best is None or v > best[0]:
            best = (v, int(r["pix"][k]), code, float(agl[k]))
    if best is None or best[0] < 40:
        return []
    i, j = divmod(best[1], GW)
    if not (0 <= i - PR0 <= 2 * HALF and 0 <= j - PC0 <= 2 * HALF):
        return []
    return ["Vânt măsurat Doppler în nucleele de precipitații, sub 1 km deasupra solului: până la %.0f km/h %s (radar %s, componenta radială — viteza reală e cel puțin atât)." % (
        best[0], where_txt(i - PR0, j - PC0), RADARS[best[2]])]


HZ_FC = (("mesh", 10), ("poh", 1), ("wg", 1), ("vil", 10), ("et18", 10), ("risk", 1))


def write_nowcast(key, nc, Hz, ftyp=None):
    """prognoza: intensitatea (f), reflectivitatea (z) și tipul la sol (t) la +10 … +120 min;
       produsele de volum și zonele de risc mutate cu celulele (persistență lagrangiană, ca TRT) la +10 … +60 min"""
    fields = []
    for lead in range(10, 121, 10):
        fields.append(("f%d" % lead, nc["fc"][lead // NC_DT - 1][PSL], 100))
        if nc.get("fz"):
            fields.append(("z%d" % lead, nc["fz"][lead // NC_DT - 1][PSL], 2))
        if ftyp:
            fields.append(("t%d" % lead, ftyp[lead], 1))
    if Hz is not None and nc.get("mot"):
        for lead in range(10, 61, 10):
            for nm, sc in HZ_FC:
                F = Hz[nm].astype(np.float32) / (1000.0 if nm == "et18" else 1.0)
                if nm in ("risk",):
                    A = advect_nearest(F, nc["mot"], lead)
                else:
                    A = advect_nearest(np.nan_to_num(F), nc["mot"], lead)
                    A = np.where(A > 0, A, np.nan)
                fields.append(("%s%d" % ({"risk": "r", "et18": "e"}.get(nm, nm), lead), A[PSL], sc))
    with open(os.path.join(OUT, "%s_N.dat" % key), "wb") as fh:
        fh.write(pack(fields, 0, 0, 2 * HALF + 1, 2 * HALF + 1))


def extra_lines(C, nc, Hz, mot, verif, hz_note, iso):
    L = []
    c0 = HALF
    if nc and nc.get("fc"):
        fc = nc["fc"]
        g = [float(np.nanmax(np.append(f[PSL][c0 - 2:c0 + 3, c0 - 2:c0 + 3], -1))) for f in fc]
        now_r = float(np.nanmax(np.append(np.nan_to_num(C["rate"][PSL][c0 - 2:c0 + 3, c0 - 2:c0 + 3]), 0)))
        if now_r >= 0.1:
            stop = next(((k + 1) * NC_DT for k, v in enumerate(g) if 0 <= v < 0.1), None)
            L.append("Prognoză Galați: plouă acum (%.1f mm/h); " % now_r + ("precipitațiile se opresc în ~%d min." % stop if stop else "precipitațiile continuă cel puțin 2 ore."))
        else:
            start = next(((k + 1) * NC_DT for k, v in enumerate(g) if v >= 0.1), None)
            mx = max([v for v in g if v >= 0] or [0])
            L.append("Prognoză Galați: " + ("precipitații în ~%d min, maxim %.1f mm/h în următoarele 2 ore." % (start, mx) if start
                                             else "fără precipitații în următoarele 2 ore (extrapolarea ecourilor existente)."))
    elif nc and nc.get("why"):
        L.append("Prognoza pe 2 ore: nu se face acum — %s." % nc["why"])
    if mot:
        L.append("Câmpul de deplasare (TREC, %d vectori, corelație medie %.2f): spre %s cu ~%.0f km/h în medie." % (mot["n"], mot["cc"], bearing_txt(mot["spre"]), mot["kmh"]))
    if hz_note:
        L.append("Atenție: " + hz_note + ".")
    if Hz is not None:
        I = INSIDE
        mesh = np.where(I, np.nan_to_num(Hz["mesh"][PSL]), 0); wg = np.where(I, np.nan_to_num(Hz["wg"][PSL]), 0)
        hz = Hz["hail"][PSL]; wd = Hz["wind"][PSL]
        if (hz > 0).any() or (wd > 0).any():
            if (hz >= 2).any():
                i, j = np.unravel_index(int(np.argmax(mesh)), mesh.shape)
                L.append("GRINDINĂ — %s: zonă de %d km², diametru maxim estimat %.1f cm %s (MESH)." % (
                    "RISC SEVER (≥ 5 cm)" if (hz == 3).any() else "risc mediu (≥ 2 cm)", int((hz >= 2).sum()), mesh[i, j] / 10, where_txt(i, j)))
            elif (hz == 1).any():
                L.append("Grindină posibilă (probabilitate ≥ 50%%, dimensiuni sub 2 cm) pe %d km²." % int((hz == 1).sum()))
            if (wd >= 1).any():
                i, j = np.unravel_index(int(np.argmax(wg)), wg.shape)
                L.append("VIJELIE — %s: rafale estimate la sol până la %.0f km/h %s (potențial din VIL și vârful ecourilor, Stewart 1991)." % (
                    "RISC SEVER (≥ 90 km/h)" if (wd == 2).any() else "risc mediu (≥ 60 km/h)", wg[i, j], where_txt(i, j)))
            if mot and mot["kmh"] >= 5:
                L.append("Zonele de risc se deplasează spre %s cu ~%.0f km/h (conturul estimat la 30 și 60 min e pe hartă)." % (bearing_txt(mot["spre"]), mot["kmh"]))
        else:
            vmax = float(np.nanmax(np.append(np.where(I, Hz["vil"][PSL], np.nan), 0)))
            L.append("Nuclee convective analizate în volumul complet: fără semnătură de grindină mare sau rafale ≥ 60 km/h (VIL maxim %.0f kg/m²)." % vmax)
        if iso:
            L.append("Izoterma 0 °C ~%.1f km, −20 °C ~%.1f km (model ICON prin Open-Meteo)." % (
                np.mean([p[2] for p in iso["pts"]]) / 1000, np.mean([p[3] for p in iso["pts"]]) / 1000))
    if verif:
        parts = ["la %d min: CSI %s (persistență %s)" % (k, v["csi"], v["csi_pers"]) for k, v in sorted(verif.items()) if v.get("csi") is not None]
        if parts:
            L.append("Verificarea prognozelor anterioare (precipitații ≥ 0,5 mm/h): " + "; ".join(parts) + ".")
    return L


# ---------------- vizibilitate pe anotimpuri ----------------
def png_rgba(rgba):
    import zlib
    h, w, _ = rgba.shape
    raw = b"".join(b"\x00" + rgba[r].tobytes() for r in range(h))

    def chunk(t, d):
        return struct.pack(">I", len(d)) + t + d + struct.pack(">I", zlib.crc32(t + d) & 0xffffffff)
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b""))


def visibility(C):
    """zona în care fasciculul cel mai jos neblocat trece peste înălțimea tipică a norilor cu precipitații ai anotimpului
       (înălțime deasupra reliefului)"""
    agl = (C["h"] - relief_grid())[PSL]
    bm = np.where(np.isfinite(agl), agl, 1e9)
    vis = []
    for name, H, why in (("iarnă", 1500, "ninsoarea din nori joși (vârfuri de 2–4 km) se vede doar unde fasciculul e sub ~1,5 km deasupra solului"),
                         ("primăvară / toamnă", 2500, "ploaia stratiformă cu strat de topire la 1–2,5 km"),
                         ("vară", 4000, "averse și furtuni cu nori de peste 6–10 km")):
        rr = 0
        for rad in range(5, int(RADIUS) + 1):
            if bm[PDIST <= rad].max() > H:
                break
            rr = rad
        mask = bm > H
        rgba = np.zeros(bm.shape + (4,), np.uint8)
        stripe = ((np.add.outer(np.arange(bm.shape[0]), np.arange(bm.shape[1])) // 3) % 3 == 0)
        rgba[mask & stripe] = (200, 200, 200, 120)
        rgba[mask & ~stripe] = (40, 40, 40, 70)
        edge = mask & ~np.roll(mask, 1, 0) | mask & ~np.roll(mask, -1, 0) | mask & ~np.roll(mask, 1, 1) | mask & ~np.roll(mask, -1, 1)
        rgba[edge] = (255, 200, 60, 230)
        rgba[~INSIDE] = 0
        rgba = rgba[MERC_ROWS]                 # rânduri în proiecția hărții (Mercator), ca imaginea să cadă exact
        fnv = "vis_%d.png" % len(vis)
        with open(os.path.join(OUT, fnv), "wb") as fh:
            fh.write(png_rgba(rgba))
        vis.append({"name": name, "h": H, "r": rr, "why": why, "png": fnv,
                    "pct": round(100.0 * float((~mask & INSIDE).sum()) / float(INSIDE.sum())),
                    "galati": round(float(bm[HALF, HALF]))})
    return vis


# ---------------- buletin ----------------
def bearing_txt(deg):
    names = ["N", "NNE", "NE", "ENE", "E", "ESE", "SE", "SSE", "S", "SSV", "SV", "VSV", "V", "VNV", "NV", "NNV"]
    return names[int((deg % 360) / 22.5 + 0.5) % 16]


def where_txt(i, j):
    """(i, j) în fereastra paginii"""
    lat, lon = GLAT[PR0 + i, 0], GLON[0, PC0 + j]
    best = min(PLACES, key=lambda p: math.hypot((p[2] - lon) * KX, (p[1] - lat) * KY))
    d = math.hypot((best[2] - lon) * KX, (best[1] - lat) * KY)
    if d < 8:
        return "la " + best[0]
    b = (math.degrees(math.atan2((lon - best[2]) * KX, (lat - best[1]) * KY)) + 360) % 360
    return "la %d km %s de %s" % (round(d / 5) * 5 if d >= 10 else round(d), bearing_txt(b), best[0])


def bulletin(t, C, per, mot, a1, a1h):
    I = INSIDE
    Z = np.where(np.isfinite(C["Z"]), C["Z"], np.nan)[PSL]; R = C["rate"][PSL]; ET = C["etop"][PSL]
    Cl = C["cls"][PSL]; S = C["sfc"][PSL]
    n = I.sum()
    met = (Cl >= 3) & I
    cov = lambda thr: 100.0 * np.sum(met & (np.nan_to_num(Z, nan=-99) >= thr)) / n
    lines = []
    loc = t.astimezone(timezone(timedelta(hours=2)))
    head = "Observație radar · zona Galați (rază %d km) · %s UTC (%s ora României)" % (RADIUS, t.strftime("%d.%m.%Y %H:%M"), loc.strftime("%H:%M"))
    if cov(15) < 0.5:
        lines.append("Fără ecouri de precipitații semnificative în zonă (sub 0,5% din suprafață peste 15 dBZ).")
    else:
        zi = np.where(met, np.nan_to_num(Z, nan=-99), -99)
        i, j = np.unravel_index(int(np.argmax(zi)), zi.shape)
        lines.append("Precipitații pe %.0f%% din zonă (ecouri ≥15 dBZ); %.0f%% peste 30 dBZ, %.1f%% peste 45 dBZ." % (cov(15), cov(30), cov(45)))
        lines.append("Reflectivitate maximă %.0f dBZ %s." % (zi[i, j], where_txt(i, j)))
        rr = np.where(met, np.nan_to_num(R, nan=0), 0)
        i2, j2 = np.unravel_index(int(np.argmax(rr)), rr.shape)
        if rr[i2, j2] >= 0.1:
            lines.append("Intensitate maximă %.1f mm/h %s; medie pe suprafața cu precipitații %.1f mm/h." % (
                rr[i2, j2], where_txt(i2, j2), float(np.mean(rr[met & (rr > 0.1)])) if (met & (rr > 0.1)).any() else 0))
        tot = np.sum((S > 0) & met)
        if tot:
            part = {k: 100.0 * np.sum((S == k) & met) / tot for k in range(1, len(SFC))}
            txt = ", ".join("%s %.0f%%" % (SFC[k], v) for k, v in sorted(part.items(), key=lambda x: -x[1]) if v >= 1)
            lines.append("Tipul precipitațiilor la sol, pe relieful real (radar%s): %s." % (
                " + temperatura umedă la stații, ora " + C["met_key"][11:13] + " UTC" if C.get("met_key") else ", fără date de temperatură la sol", txt))
            if part.get(3, 0) >= 1:
                sn = (S == 3) & met
                ii, jj = np.nonzero(sn)
                lines.append("Ninsoare pe aproximativ %d km², mai ales %s." % (int(sn.sum()), where_txt(int(ii.mean()), int(jj.mean()))))
        hcls = {k: 100.0 * np.sum((Cl == k) & I) / max(1, np.sum(met)) for k in range(3, len(CLASSES))}
        top = sorted(((v, k) for k, v in hcls.items() if v >= 3), reverse=True)[:3]
        if top:
            lines.append("În fasciculul radar (clasificare polarimetrică): " + ", ".join("%s %.0f%%" % (CLASSES[k], v) for v, k in top) + ".")
        if np.sum((Cl == 10) & I) >= 3:
            lines.append("Semnătură polarimetrică de grindină în fascicul pe %d km² (vezi și estimarea din volumul complet)." % int(np.sum((Cl == 10) & I)))
        et = np.where(met, np.nan_to_num(ET, nan=0), 0)
        if et.max() > 0:
            i3, j3 = np.unravel_index(int(np.argmax(et)), et.shape)
            lines.append("Vârful ecourilor (produsul ANM): maxim %.1f km %s." % (et[i3, j3], where_txt(i3, j3)))
        if mot:
            lines.append("Deplasarea ecourilor: spre %s cu ~%.0f km/h." % (bearing_txt(mot["spre"]), mot["kmh"]))
        c0 = HALF
        zc = np.nan_to_num(np.where(met, Z, np.nan)[c0 - 2:c0 + 3, c0 - 2:c0 + 3], nan=-99).max()
        if zc >= 15:
            lines.append("Precipitații în prezent deasupra municipiului Galați (%.1f mm/h)." % float(np.nan_to_num(R[c0, c0])))
        elif mot and mot["kmh"] >= 5:
            ux, uy = mot["vx"] / mot["kmh"], mot["vy"] / mot["kmh"]
            for dkm in range(5, 151, 5):
                jj = int(round(c0 - ux * dkm)); ii = int(round(c0 + uy * dkm))
                if 0 <= ii < Z.shape[0] and 0 <= jj < Z.shape[1] and met[ii, jj] and np.nan_to_num(Z[ii, jj], nan=-99) >= 15:
                    lines.append("Precipitațiile din amonte se află la ~%d km de Galați; sosire estimată în ~%d min, dacă direcția se menține." % (
                        dkm, round(dkm / mot["kmh"] * 60 / 5) * 5))
                    break
    if a1 is not None and np.isfinite(a1[PSL][I]).any():
        g = a1[PSL][HALF, HALF]
        lines.append("Cumul radar în ora %s–%s UTC: Galați %s; maxim în zonă %.1f mm %s." % (
            (a1h - timedelta(hours=1)).strftime("%H:%M"), a1h.strftime("%H:%M"),
            "%.1f mm" % g if np.isfinite(g) else "necunoscut", float(np.nanmax(np.where(I, a1[PSL], np.nan))) if np.isfinite(a1[PSL][I]).any() else 0,
            where_txt(*np.unravel_index(int(np.nanargmax(np.where(I, np.nan_to_num(a1[PSL], nan=-1), -1))), I.shape))))
    mls = ["%s: bază %.1f km, vârf %.1f km" % (RADARS[k], v["ml"][0] / 1000, v["ml"][2] / 1000) for k, v in per.items() if v.get("ml")]
    if mls and cov(15) >= 0.5:
        lines.append("Stratul de topire (din volum, deasupra nivelului mării) — " + "; ".join(mls) + ".")
    vads = ["%s: %s %.0f km/h la ~%.0f m" % (RADARS[k], bearing_txt((math.degrees(math.atan2(-v["vad"]["u"], -v["vad"]["v"])) + 360) % 360),
                                             math.hypot(v["vad"]["u"], v["vad"]["v"]) * 3.6, v["vad"]["h"]) for k, v in per.items() if v.get("vad")]
    if vads:
        lines.append("Vânt din viteza Doppler (VAD, deasupra radarului): " + "; ".join(vads) + ".")
    lines.append("Surse: " + ", ".join("%s %s UTC" % (RADARS[k], ts_time(v["ts"]).strftime("%H:%M")) for k, v in per.items())
                 + (". Lipsește: " + ", ".join(RADARS[k] for k in RCODES if k not in per) if len(per) < len(RCODES) else "") + ".")
    return head, lines


# =====================================================================================================
# DEPLASARE ȘI PROGNOZĂ IMEDIATĂ (nowcasting) PE 2 ORE
#   - câmpul de deplasare: TREC (Rinehart & Garvey 1978, Nature 273) — corelația încrucișată normalizată între
#     două compozite la 10 minute, pe ferestre de 24 km, cu controlul calității vectorilor (corelație minimă,
#     filtrul median al vecinilor, ca în COTREC, Li et al. 1995) și interpolare gaussiană într-un câmp continuu;
#   - extrapolarea: schema semi-lagrangiană înapoi, pas de 5 minute (Germann & Zawadzki 2002, Mon. Wea. Rev. 130);
#   - evoluția: S-PROG (Seed 2003, J. Appl. Meteor. 42, 381–388) — câmpul în dBR descompus în 8 cascade spectrale,
#     fiecare evoluând după un model AR(2) estimat din ultimele 3 compozite (structurile mici, mai puțin previzibile,
#     se estompează mai repede), recompunere și potrivirea distribuției cu observația (probability matching);
#     același lanț ca în pysteps (Pulkkinen et al. 2019, Geosci. Model Dev. 12).
# =====================================================================================================
NC_DT = 5                     # pasul (minute) = intervalul volumelor
NC_STEPS = 24                 # 2 ore
NC_ZERO = -15.0               # dBR pentru „fără precipitații” (R < 0,1 mm/h → 0,03 mm/h)
NC_LEVELS = 8
NC_ZTHR = 10.0                # dBZ: pragul de ecou pentru prognoza reflectivității
NC_ZZERO = 5.0                # valoarea „fără ecou” (pragul − 5 dB, ca în pysteps)


def to_dbr(R):
    R = np.asarray(R, dtype=np.float64)
    return np.where(np.isfinite(R) & (R >= 0.1), 10 * np.log10(np.maximum(R, 0.1)), NC_ZERO)


def from_dbr(D):
    return np.where(D > 10 * math.log10(0.1) - 1e-6, 10 ** (D / 10.0), 0.0)


def _down2(a):
    H, W = a.shape[0] // 2 * 2, a.shape[1] // 2 * 2
    return a[:H, :W].reshape(H // 2, 2, W // 2, 2).mean((1, 3))


def _box_sums(I, ys, xs, h):
    """sumele pe ferestre (2h × 2h) centrate în (ys, xs) dintr-o imagine integrală I (cu bordură de 0)"""
    y0, y1 = ys - h, ys + h
    x0, x1 = xs - h, xs + h
    return I[y1[:, None], x1[None, :]] - I[y0[:, None], x1[None, :]] - I[y1[:, None], x0[None, :]] + I[y0[:, None], x0[None, :]]


def _integral(a):
    I = np.zeros((a.shape[0] + 1, a.shape[1] + 1))
    I[1:, 1:] = a.cumsum(0).cumsum(1)
    return I


def trec(A, B, dt_min, km=2.0, half=6, step=6, smax=8):
    """A = câmpul anterior, B = câmpul curent (dBR, grilă de `km` km). Pentru fiecare fereastră din A se caută
       deplasarea (±smax pixeli) cu corelația maximă în B. Întoarce centrele (rând, coloană) și vitezele (km/h)
       spre est (u) și spre nord (v), plus corelația."""
    H, W = A.shape
    ys = np.arange(half + smax, H - half - smax, step); xs = np.arange(half + smax, W - half - smax, step)
    n = (2 * half) ** 2
    IA, IAA = _integral(A), _integral(A * A)
    SA, SAA = _box_sums(IA, ys, xs, half), _box_sums(IAA, ys, xs, half)
    IR = _integral((A > NC_ZERO + 0.5).astype(float))
    frac = _box_sums(IR, ys, xs, half) / n
    best = np.full(SA.shape, -2.0); bdy = np.zeros(SA.shape); bdx = np.zeros(SA.shape)
    C = {}
    Bp = np.pad(B, smax, mode="constant", constant_values=NC_ZERO)
    for dy in range(-smax, smax + 1):
        for dx in range(-smax, smax + 1):
            Bs = Bp[smax + dy:smax + dy + H, smax + dx:smax + dx + W]        # Bs[y, x] = B[y+dy, x+dx]
            SB, SBB, SAB = _box_sums(_integral(Bs), ys, xs, half), _box_sums(_integral(Bs * Bs), ys, xs, half), _box_sums(_integral(A * Bs), ys, xs, half)
            va = SAA - SA * SA / n; vb = SBB - SB * SB / n
            r = np.where((va > 1e-6) & (vb > 1e-6), (SAB - SA * SB / n) / np.sqrt(np.maximum(va * vb, 1e-12)), -1.0)
            C[(dy, dx)] = r
            better = r > best
            best = np.where(better, r, best); bdy = np.where(better, dy, bdy); bdx = np.where(better, dx, bdx)
    # poziție sub-pixel: parabolă pe vecinii maximului
    sy = np.zeros(best.shape); sx = np.zeros(best.shape)
    for idx in np.ndindex(best.shape):
        dy, dx = int(bdy[idx]), int(bdx[idx])
        if abs(dy) < smax:
            a, b_, c = C[(dy - 1, dx)][idx], best[idx], C[(dy + 1, dx)][idx]
            den = a - 2 * b_ + c
            sy[idx] = 0.5 * (a - c) / den if den < -1e-9 else 0.0
        if abs(dx) < smax:
            a, b_, c = C[(dy, dx - 1)][idx], best[idx], C[(dy, dx + 1)][idx]
            den = a - 2 * b_ + c
            sx[idx] = 0.5 * (a - c) / den if den < -1e-9 else 0.0
    fy = (bdy + np.clip(sy, -0.5, 0.5)) * km; fx = (bdx + np.clip(sx, -0.5, 0.5)) * km
    u = fx / (dt_min / 60.0); v = -fy / (dt_min / 60.0)
    ok = (best >= 0.45) & (frac >= 0.10) & (np.abs(bdy) < smax) & (np.abs(bdx) < smax)
    Y, X = np.meshgrid(ys, xs, indexing="ij")
    return Y, X, u, v, best, ok


def motion_field(Rs, dt_min=10, logf=False, smax=8):
    """Rs = [R(t−10 min), R(t)] pe grila de 1 km → câmpul dens (u, v) în km/h, vectorii pentru săgeți, statistici
       (logf=True: câmpurile sunt deja logaritmice / scalate, cu NC_ZERO = „nimic”)"""
    A = _down2(Rs[0] if logf else to_dbr(Rs[0])); B = _down2(Rs[1] if logf else to_dbr(Rs[1]))
    Y, X, u, v, cc, ok = trec(A, B, dt_min, smax=smax)
    if ok.sum() < 3:
        return None
    # controlul calității: vectorul trebuie să difere cu < 20 km/h de mediana vecinilor valizi pe ~50 km (Li et al. 1995)
    yy, xx, uu, vv, cw = Y[ok] * 2.0, X[ok] * 2.0, u[ok], v[ok], cc[ok]
    keep = np.ones(uu.size, bool)
    if uu.size >= 5:
        D = np.hypot(yy[:, None] - yy[None, :], xx[:, None] - xx[None, :])
        for i in range(uu.size):
            nb = (D[i] <= 50) & (D[i] > 0)
            if nb.sum() >= 3 and math.hypot(uu[i] - np.median(uu[nb]), vv[i] - np.median(vv[nb])) > 20:
                keep[i] = False
    yy, xx, uu, vv, cw = yy[keep], xx[keep], uu[keep], vv[keep], cw[keep]
    if uu.size < 3:
        return None
    um, vm = float(np.average(uu, weights=cw)), float(np.average(vv, weights=cw))
    # câmp dens pe o grilă de 4 km (interpolare gaussiană, σ = 40 km; spre media domeniului unde nu sunt vectori)
    G = 8.0
    gy = np.arange(0, GH, G); gx = np.arange(0, GW, G)
    Gy, Gx = np.meshgrid(gy, gx, indexing="ij")
    py, px = Gy.ravel(), Gx.ravel()
    U = np.empty(py.size); V = np.empty(py.size); w0 = 0.3
    for a in range(0, py.size, 2000):
        d2 = (py[a:a + 2000, None] - yy[None, :]) ** 2 + (px[a:a + 2000, None] - xx[None, :]) ** 2
        w = np.exp(-d2 / (2 * 40.0 ** 2)) * cw[None, :]
        U[a:a + 2000] = ((w * uu[None, :]).sum(1) + w0 * um) / (w.sum(1) + w0)
        V[a:a + 2000] = ((w * vv[None, :]).sum(1) + w0 * vm) / (w.sum(1) + w0)
    U = U.reshape(Gy.shape); V = V.reshape(Gy.shape)
    # pe grila de 1 km (biliniar)
    ry = np.arange(GH) / G; rx = np.arange(GW) / G
    Uf = bilinear(U, ry[:, None] + 0 * rx[None, :], rx[None, :] + 0 * ry[:, None], edge=True)
    Vf = bilinear(V, ry[:, None] + 0 * rx[None, :], rx[None, :] + 0 * ry[:, None], edge=True)
    return {"u": Uf.astype(np.float32), "v": Vf.astype(np.float32), "um": um, "vm": vm,
            "vec": (yy, xx, uu, vv, cw), "n": int(uu.size), "ccm": float(np.mean(cw))}


def bilinear(F, y, x, edge=False):
    """interpolare biliniară în F la poziții fracționare (rând y, coloană x); NaN în afara grilei (sau marginea, edge=True)"""
    H, W = F.shape
    if edge:
        y = np.clip(y, 0, H - 1); x = np.clip(x, 0, W - 1)
    out = (y >= 0) & (x >= 0) & (y <= H - 1) & (x <= W - 1)
    yc = np.clip(y, 0, H - 1); xc = np.clip(x, 0, W - 1)
    y0 = np.clip(np.floor(yc).astype(int), 0, H - 2); x0 = np.clip(np.floor(xc).astype(int), 0, W - 2)
    wy = yc - y0; wx = xc - x0
    v = (F[y0, x0] * (1 - wy) * (1 - wx) + F[y0 + 1, x0] * wy * (1 - wx) + F[y0, x0 + 1] * (1 - wy) * wx + F[y0 + 1, x0 + 1] * wy * wx)
    return np.where(out, v, np.nan)


def sl_steps(mot, nsteps, dt_min=NC_DT):
    """deplasările cumulate ale schemei semi-lagrangiene înapoi (Germann & Zawadzki 2002): pentru fiecare pas n,
       originea (în pixeli de 1 km) a punctului care ajunge în fiecare pixel după n·dt"""
    U = mot["u"] * dt_min / 60.0          # km (= pixeli) spre est într-un pas
    V = -mot["v"] * dt_min / 60.0         # pixeli în jos (rând) într-un pas
    Y, X = np.meshgrid(np.arange(GH, dtype=np.float64), np.arange(GW, dtype=np.float64), indexing="ij")
    # un pas: punctul de mijloc al traiectoriei (2 iterații)
    dy1, dx1 = -V, -U
    for _ in range(2):
        my, mx = Y + dy1 / 2, X + dx1 / 2
        dy1 = -bilinear(V, my, mx, edge=True); dx1 = -bilinear(U, my, mx, edge=True)
    out = []
    Dy_prev = Dx_prev = None
    for n in range(nsteps):
        # D_{n+1}(x) = D_1(x) + D_n(x + D_1(x))
        if n == 0:
            Dy, Dx = dy1.copy(), dx1.copy()
        else:
            Dy = dy1 + bilinear(Dy_prev, Y + dy1, X + dx1, edge=True)
            Dx = dx1 + bilinear(Dx_prev, Y + dy1, X + dx1, edge=True)
        Dy_prev, Dx_prev = Dy, Dx
        out.append((Y + Dy, X + Dx))
    return out


def cascade_weights(shape, n=NC_LEVELS):
    """filtre gaussiene în log(număr de undă), normalizate să însumeze 1 (descompunerea în cascadă din pysteps)"""
    H, W = shape
    ky = np.fft.fftfreq(H) * H; kx = np.fft.rfftfreq(W) * W
    L = max(H, W)
    r = np.hypot(ky[:, None] * (L / H), kx[None, :] * (L / W))
    lr = np.log(np.maximum(r, 0.5))
    centres = np.linspace(np.log(0.5), np.log(L / 2.0), n)
    s = (centres[1] - centres[0])
    Wk = np.array([np.exp(-0.5 * ((lr - c) / s) ** 2) for c in centres])
    return Wk / Wk.sum(0)


def decompose(D, Wk):
    F = np.fft.rfft2(D)
    return np.array([np.fft.irfft2(F * w, s=D.shape) for w in Wk])


def adjust_lag2(g1, g2):
    """corecția coeficientului de autocorelație la pasul 2 înainte de estimarea AR(2), ca în pysteps
       (pysteps.timeseries.autoregression.adjust_lag2_corrcoef2, folosită în S-PROG): (1) condiția de staționaritate
       γ2 > 2γ1² − 1 și (2) condiția ca funcția de autocorelație a procesului AR(2) să descrească fără oscilații
       (γ2 ≥ [3γ1² − 2 + 2(1 − γ1²)^1,5] / γ1²). Fără a doua condiție, la scările mari γ1 ≈ γ2 ≈ 1 dau φ2 ≈ −1:
       un proces neamortizat care extrapolează liniar schimbarea dintre ultimele imagini (inele și pete false)."""
    g2 = max(g2, 2 * g1 * g1 - 1 + 1e-6)
    if g1 > 0:
        g2 = max(g2, (3 * g1 * g1 - 2 + 2 * (1 - g1 * g1) ** 1.5) / (g1 * g1))
    return min(g2, 0.999)


def sprog_log(D, mot, valid, zero, steps=None):
    """S-PROG pe câmpuri logaritmice (dBR sau dBZ) D = [t−10, t−5, t], valoarea „fără precipitații” = zero.
       Întoarce câmpurile logaritmice prognozate la +5 … +120 min (NaN unde originea nu e văzută de radar)."""
    steps = steps or sl_steps(mot, NC_STEPS)
    aligned = []
    for k, Dk in enumerate(D):
        lag = len(D) - 1 - k
        if lag == 0:
            aligned.append(Dk); continue
        oy, ox = steps[lag - 1]
        a = bilinear(Dk, oy, ox)
        aligned.append(np.where(np.isfinite(a), a, zero))
    Wk = cascade_weights(D[-1].shape)
    cas = [decompose(a, Wk) for a in aligned]
    mu = cas[-1].mean((1, 2)); sd = cas[-1].std((1, 2)) + 1e-9
    norm = [((c - mu[:, None, None]) / sd[:, None, None]).astype(np.float32) for c in cas]
    del cas
    m = valid
    phi = []
    for k in range(Wk.shape[0]):
        x0, x1, x2 = norm[0][k][m], norm[1][k][m], norm[2][k][m]
        g1 = float(np.corrcoef(x2, x1)[0, 1]) if x2.std() > 0 and x1.std() > 0 else 0.0
        g2 = float(np.corrcoef(x2, x0)[0, 1]) if x2.std() > 0 and x0.std() > 0 else 0.0
        g1 = min(max(g1, 0.0), 0.999)
        g2 = adjust_lag2(g1, g2)
        p1 = g1 * (1 - g2) / (1 - g1 * g1); p2 = (g2 - g1 * g1) / (1 - g1 * g1)
        phi.append((p1, p2, g1, g2))
    obs_sorted = np.sort(D[-1][m])
    cprev, ccur = norm[1].copy(), norm[2].copy()
    outs = []
    for n in range(NC_STEPS):
        cnext = np.array([phi[k][0] * ccur[k] + phi[k][1] * cprev[k] for k in range(len(phi))])
        cprev, ccur = ccur, cnext
        Df = (ccur * sd[:, None, None] + mu[:, None, None]).sum(0)
        vals = Df[m]
        order = np.argsort(vals)
        pm = np.empty_like(vals); pm[order] = obs_sorted
        Dm = np.full(Df.shape, zero); Dm[m] = pm
        oy, ox = steps[n]
        Fn = bilinear(Dm, oy, ox)
        vis = bilinear(valid.astype(np.float64), oy, ox)
        outs.append(np.where(np.isfinite(Fn) & (vis >= 0.5), Fn, np.nan).astype(np.float32))
    return outs, phi


def sprog(Rs, mot, valid, steps=None):
    """intensitatea: S-PROG în dBR (R < 0,1 mm/h → −15 dBR)"""
    outs, phi = sprog_log([to_dbr(R) for R in Rs], mot, valid, NC_ZERO, steps)
    return [np.where(np.isfinite(F), from_dbr(F), np.nan).astype(np.float32) for F in outs], phi


def nowcast(m):
    """prognoza pentru momentul m (yyyymmddHHMM); folosește compozitele de la m−10, m−5, m"""
    t = ts_time(m + "0000")
    keys = [(t - timedelta(minutes=k)).strftime("%Y%m%d%H%M") for k in (10, 5, 0)]
    Rs = [load_comp(k) for k in keys]
    if any(r is None for r in Rs):
        return None
    valid = np.isfinite(Rs[0]) & np.isfinite(Rs[1]) & np.isfinite(Rs[2])
    if (np.nan_to_num(Rs[2]) >= 0.1).sum() < 200:
        return {"mot": None, "fc": None, "why": "prea puține precipitații pentru estimarea deplasării"}
    mot = motion_field([Rs[0], Rs[2]], 10)
    if mot is None:
        return {"mot": None, "fc": None, "why": "deplasarea nu poate fi estimată (corelație slabă între compozite)"}
    steps = sl_steps(mot, NC_STEPS)
    fc, phi = sprog(Rs, mot, valid, steps)
    out = {"mot": mot, "fc": fc, "phi": phi, "steps": steps}
    # reflectivitatea: același lanț S-PROG direct pe dBZ (pysteps lucrează și pe reflectivitate)
    Zs = [load_comp(k, "z") for k in keys]
    if all(z is not None for z in Zs):
        vz = valid & np.isfinite(Zs[0]) & np.isfinite(Zs[1]) & np.isfinite(Zs[2])
        Dz = [np.where(np.isfinite(z), np.where(z >= NC_ZTHR, z, NC_ZZERO), NC_ZZERO).astype(np.float64) for z in Zs]
        fz, _ = sprog_log(Dz, mot, vz, NC_ZZERO, steps)
        out["fz"] = [np.where(np.isfinite(F) & (F < NC_ZTHR), -np.inf, F).astype(np.float32) for F in fz]
        # pentru verificare: extrapolarea lagrangiană simplă a reflectivității (fără evoluție; referința din pysteps)
        out["zlag"] = {}
        for lead in ZV_LEADS:
            oy, ox = steps[lead // NC_DT - 1]
            F = bilinear(Dz[-1], oy, ox); vis = bilinear(vz.astype(np.float64), oy, ox)
            out["zlag"][lead] = np.where(np.isfinite(F) & (vis >= 0.5), F, np.nan).astype(np.float32)
    return out


def verify_nowcast(m, R_obs):
    """verificarea prognozelor emise acum 60 și 120 de minute față de observația de acum (pragul 0,5 mm/h, în cerc);
       comparat cu persistența (observația de la emiterea prognozei)"""
    t = ts_time(m + "0000")
    res = {}
    obs = R_obs[PSL]
    for lead in (60, 120):
        issue = (t - timedelta(minutes=lead)).strftime("%Y%m%d%H%M")
        p = os.path.join(CACHE, "fc_%s_%03d.npy" % (issue, lead))
        q = load_comp(issue)
        if not os.path.exists(p):
            continue
        fc = np.load(p).astype(np.float32)
        ok = INSIDE & np.isfinite(fc) & np.isfinite(obs)
        if ok.sum() < 1000:
            continue

        def csi(f):
            o = obs[ok] >= 0.5; ff = f[ok] >= 0.5
            h = np.sum(o & ff); mi = np.sum(o & ~ff); fa = np.sum(~o & ff)
            return (h / (h + mi + fa) if h + mi + fa else float("nan")), int(o.sum())
        c, n_obs = csi(fc)
        cp = csi(q[PSL])[0] if q is not None else float("nan")
        res[lead] = {"csi": None if not np.isfinite(c) else round(float(c), 2),
                     "csi_pers": None if not np.isfinite(cp) else round(float(cp), 2), "n": n_obs}
    return res


# ---------------- verificarea prognozei reflectivității (comparația variantelor) ----------------
#   Variante: A = S-PROG direct pe dBZ (actuală); B = varianta anterioară: intensitatea S-PROG (dBR) adusă în dBZ cu
#   Marshall–Palmer Z = 200·R^1,6; L = extrapolare lagrangiană fără evoluție; P = persistența (imaginea de la emitere).
#   Scoruri standard de verificare a prognozei imediate (WMO/WWRP JWGFVR; pysteps): CSI pe praguri și FSS
#   (Roberts & Lean 2008, vecinătate 9 km), cumulate pe toate cazurile cu ecouri ≥ 20 dBZ observate.
ZV_LEADS = (30, 60)
ZV_THR = (20, 35, 45)
ZV_FSS_N = 9


def mp_dbz(R):
    R = np.asarray(R, np.float64)
    return np.where(np.isfinite(R), np.where(R >= 0.1, 10 * np.log10(200.0 * np.maximum(R, 0.1) ** 1.6), NC_ZZERO), np.nan)


def save_zforecasts(m, nc):
    if not nc.get("fz"):
        return
    for lead in ZV_LEADS:
        k = lead // NC_DT - 1
        for v, F in (("A", nc["fz"][k]), ("B", mp_dbz(nc["fc"][k])), ("L", nc["zlag"][lead])):
            F = np.where(np.isneginf(F), NC_ZZERO, F)
            np.save(os.path.join(CACHE, "fcz%s_%s_%03d.npy" % (v, m, lead)), F[PSL].astype(np.float16))
    lim = (ts_time(m + "0000") - timedelta(minutes=COMP_KEEP_MIN)).strftime("%Y%m%d%H%M")
    for nm in os.listdir(CACHE):
        mm = re.match(r"fcz[ABL]_(\d{12})_\d{3}\.npy$", nm)
        if mm and mm.group(1) < lim:
            os.remove(os.path.join(CACHE, nm))


def _boxmean(a, n):
    c = np.pad(a, ((n // 2 + 1, n // 2), (n // 2 + 1, n // 2))).cumsum(0).cumsum(1)
    return (c[n:, n:] - c[:-n, n:] - c[n:, :-n] + c[:-n, :-n]) / float(n * n)


def verify_reflectivity(m):
    """compară variantele de prognoză a reflectivității cu observația de acum; cumulează scorurile în verif_z.json"""
    p = os.path.join(CACHE, "verif_z.json")
    try:
        V = json.load(open(p, encoding="utf-8"))
    except Exception:
        V = {"since": m, "cases": {}, "s": {}}
    zo = load_comp(m, "z")
    if zo is None:
        return V
    obs = zo[PSL].astype(np.float64)
    t = ts_time(m + "0000")
    for lead in ZV_LEADS:
        issue = (t - timedelta(minutes=lead)).strftime("%Y%m%d%H%M")
        key = "%s+%d" % (issue, lead)
        if key in V["cases"]:
            continue
        fcs = {}
        for v in "ABL":
            q = os.path.join(CACHE, "fcz%s_%s_%03d.npy" % (v, issue, lead))
            if os.path.exists(q):
                fcs[v] = np.load(q).astype(np.float64)
        zp = load_comp(issue, "z")
        if len(fcs) < 3 or zp is None:
            continue
        fcs["P"] = zp[PSL].astype(np.float64)
        ok = INSIDE & np.isfinite(obs)
        for F in fcs.values():
            ok &= np.isfinite(F)
        if (ok & (obs >= 20)).sum() < 200:
            continue
        V["cases"][key] = 1
        for v, F in fcs.items():
            S = V["s"].setdefault(v, {}).setdefault(str(lead), {})
            for thr in ZV_THR:
                o = ok & (obs >= thr); f = ok & (F >= thr)
                c = S.setdefault(str(thr), [0, 0, 0, 0.0, 0.0])
                c[0] += int((o & f).sum()); c[1] += int((o & ~f).sum()); c[2] += int((~o & f).sum())
                po = _boxmean(o.astype(np.float64), ZV_FSS_N)[ok]; pf = _boxmean(f.astype(np.float64), ZV_FSS_N)[ok]
                c[3] += float(((pf - po) ** 2).sum()); c[4] += float((pf ** 2 + po ** 2).sum())
    V["cases"] = {k: 1 for k in sorted(V["cases"])[-2000:]}
    json.dump(V, open(p, "w", encoding="utf-8"))
    return V


def zverif_summary(V):
    names = {"A": "S-PROG pe dBZ", "B": "intensitate→dBZ (anterioară)", "L": "extrapolare simplă", "P": "persistență"}
    out = []
    for lead in ZV_LEADS:
        parts = []
        for v in "ABLP":
            S = V.get("s", {}).get(v, {}).get(str(lead))
            if not S:
                continue
            seg = []
            for thr in ZV_THR:
                h, mi, fa, num, den = S[str(thr)]
                csi = h / (h + mi + fa) if h + mi + fa else float("nan")
                fss = 1 - num / den if den else float("nan")
                seg.append("%d dBZ CSI %.2f FSS %.2f" % (thr, csi, fss))
            parts.append("%s: %s" % (names[v], ", ".join(seg)))
        if parts:
            out.append("+%d min — " % lead + " | ".join(parts))
    return out


def save_forecasts(m, fc):
    for lead in (60, 120):
        np.save(os.path.join(CACHE, "fc_%s_%03d.npy" % (m, lead)), fc[lead // NC_DT - 1][PSL].astype(np.float16))
    lim = (ts_time(m + "0000") - timedelta(minutes=COMP_KEEP_MIN)).strftime("%Y%m%d%H%M")
    for nm in os.listdir(CACHE):
        mm = re.match(r"fc_(\d{12})_\d{3}\.npy$", nm)
        if mm and mm.group(1) < lim:
            os.remove(os.path.join(CACHE, nm))


# =====================================================================================================
# PRODUSE DIN VOLUMUL COMPLET (doar când există convecție: reflectivitate ≥ 40 dBZ în aria radarului)
#   - VIL, apa lichidă integrată pe verticală (Greene & Clark 1972, J. Appl. Meteor. 11), Z plafonat la 56 dBZ;
#   - vârful ecourilor de 18 dBZ (ET) și înălțimea ecoului de 45 dBZ;
#   - grindina: SHI/MESH (Witt et al. 1998, Wea. Forecasting 13, 286–303) cu izotermele 0 °C și −20 °C
#     (model numeric ICON prin Open-Meteo), POH = 29·ln(ΔH) + 50, ΔH = H45 − H0 (Waldvogel et al. 1979;
#     forma din algoritmul NEXRAD, Witt et al. 1998);
#   - rafala la sol în furtuni: potențialul de rafală din VIL și vârful ecourilor (Stewart 1991, NWS Southern
#     Region; folosit de NWS pentru furtunile „puls” de vară): W = √(20,628571·VIL − 3,125·10⁻⁶·ET²) m/s.
#   Praguri de risc (categoriile ESSL / ESWD): grindină mare ≥ 2 cm (risc mediu), foarte mare ≥ 5 cm (risc sever);
#   rafale ≥ 60 km/h (risc mediu, prag de avertizare ANM), ≥ 90 km/h (risc sever, „severe wind gust” ESSL ≥ 25 m/s).
# =====================================================================================================
def isotherms(now):
    """înălțimea izotermelor 0 °C și −20 °C (m, deasupra mării) în 9 puncte ale domeniului, ora curentă; cache 1 oră"""
    p = os.path.join(CACHE, "izoterme.json")
    try:
        j = json.load(open(p, encoding="utf-8"))
        if j.get("hour") == now.strftime("%Y%m%d%H"):
            return j
    except Exception:
        pass
    lats = [43.6, 45.4, 47.2]; lons = [25.6, 27.8, 30.0]
    pts = [(a, b) for a in lats for b in lons]
    lev = [925, 850, 700, 600, 500, 400, 300]
    hv = ["freezing_level_height"] + ["temperature_%dhPa" % l for l in lev] + ["geopotential_height_%dhPa" % l for l in lev]
    url = ("https://api.open-meteo.com/v1/forecast?latitude=%s&longitude=%s&hourly=%s&forecast_days=2&timezone=GMT"
           % (",".join(str(a) for a, _ in pts), ",".join(str(b) for _, b in pts), ",".join(hv)))
    req = urllib.request.Request(url, headers={"User-Agent": "HartiMeteo/2.0"})
    with urllib.request.urlopen(req, timeout=60) as r:
        data = json.loads(r.read().decode())
    if isinstance(data, dict):
        data = [data]
    key = now.strftime("%Y-%m-%dT%H:00")
    out = {"hour": now.strftime("%Y%m%d%H"), "pts": []}
    for (la, lo), d in zip(pts, data):
        h = d["hourly"]; i = h["time"].index(key)
        h0 = h["freezing_level_height"][i]
        T = [h["temperature_%dhPa" % l][i] for l in lev]; Z = [h["geopotential_height_%dhPa" % l][i] for l in lev]
        h20 = None
        for k in range(len(lev) - 1):
            if T[k] is None or T[k + 1] is None:
                continue
            if T[k] >= -20 >= T[k + 1]:
                h20 = Z[k] + (Z[k + 1] - Z[k]) * (T[k] + 20) / (T[k] - T[k + 1] + 1e-9)
                break
        if h0 is not None and h20 is not None:
            out["pts"].append([la, lo, float(h0), float(h20)])
    if len(out["pts"]) >= 4:
        json.dump(out, open(p, "w", encoding="utf-8"))
        return out
    raise RuntimeError("izotermele nu pot fi calculate din model")


def nwp_surface(now):
    """INCA (Haiden et al. 2011): în prognoza imediată temperatura = analiza la stații + tendința modelului numeric.
       Aici: T 2 m, Td 2 m și izoterma 0 °C din ICON (Open-Meteo) în 9 puncte, orele now−1 … now+3; cache 1 oră."""
    p = os.path.join(CACHE, "icon_sol.json")
    try:
        j = json.load(open(p, encoding="utf-8"))
        if j.get("hour") == now.strftime("%Y%m%d%H"):
            return j
    except Exception:
        pass
    lats = [43.6, 45.4, 47.2]; lons = [25.6, 27.8, 30.0]
    pts = [(a, b) for a in lats for b in lons]
    url = ("https://api.open-meteo.com/v1/forecast?latitude=%s&longitude=%s&hourly=temperature_2m,dew_point_2m,freezing_level_height"
           "&models=icon_seamless&past_days=1&forecast_days=2&timezone=GMT"
           % (",".join(str(a) for a, _ in pts), ",".join(str(b) for _, b in pts)))
    req = urllib.request.Request(url, headers={"User-Agent": "HartiMeteo/2.0"})
    with urllib.request.urlopen(req, timeout=60) as r:
        data = json.loads(r.read().decode())
    if isinstance(data, dict):
        data = [data]
    h0 = now.replace(minute=0, second=0, microsecond=0)
    hours = [(h0 + timedelta(hours=k)).strftime("%Y-%m-%dT%H:00") for k in range(-1, 4)]
    out = {"hour": now.strftime("%Y%m%d%H"), "t0": (h0 - timedelta(hours=1)).strftime("%Y%m%d%H"), "pts": []}
    for (la, lo), d in zip(pts, data):
        h = d["hourly"]
        try:
            ii = [h["time"].index(k) for k in hours]
            rows = [[h["temperature_2m"][i], h["dew_point_2m"][i], h["freezing_level_height"][i]] for i in ii]
        except (ValueError, KeyError):
            continue
        if all(v is not None for r_ in rows for v in r_):
            out["pts"].append([la, lo, rows])
    if len(out["pts"]) >= 4:
        json.dump(out, open(p, "w", encoding="utf-8"))
        return out
    raise RuntimeError("temperatura la sol din model nu e disponibilă")


def nwp_trend(nwp, t_an, t_fc, lat, lon):
    """tendința modelului între momentul analizei și momentul prognozei (interpolare liniară în timp între ore,
       IDW în spațiu): (ΔT, ΔTd, ΔH0) în puncte"""
    t0 = datetime.strptime(nwp["t0"], "%Y%m%d%H").replace(tzinfo=timezone.utc)

    def at(t):
        x = (t - t0).total_seconds() / 3600.0
        k = int(min(max(math.floor(x), 0), 3)); f = min(max(x - k, 0.0), 1.0)
        return np.array([[(1 - f) * a + f * b for a, b in zip(r[2][k], r[2][k + 1])] for r in nwp["pts"]])
    D = at(t_fc) - at(t_an)
    P = np.array([[r[0], r[1]] for r in nwp["pts"]], float)
    d = np.hypot((lat[:, None] - P[None, :, 0]) * KY, (lon[:, None] - P[None, :, 1]) * KX)
    w = 1.0 / np.maximum(d, 5.0) ** 2; w /= w.sum(1, keepdims=True)
    return w @ D[:, 0], w @ D[:, 1], w @ D[:, 2]


def fc_surface_types(C, nc, t, Hz):
    """tipul precipitației la sol în prognoză, ca INCA: precipitația prognozată (S-PROG) + relieful + temperatura la sol
       prognozată = analiza de acum la stații + tendința ICON; baza stratului de topire = cea observată acum + tendința
       izotermei 0 °C din ICON; clasa hidrometeorilor și grindina (TRT) sunt mutate odată cu celulele."""
    try:
        nwp = nwp_surface(t)
    except Exception as e:
        log.info("tendința ICON la sol nu e disponibilă (%s); tipul în prognoză folosește temperatura de acum", e)
        nwp = None
    lat = GLAT[PSL].ravel(); lon = GLON[PSL].ravel(); hz = relief_grid()[PSL].ravel().astype(np.float64)
    met = met_points(lat, lon, hz)
    mlb0 = C["mlb"][PSL].ravel().astype(np.float64)
    cls_now = C["cls"].astype(np.float32)
    out = {}
    for lead in range(10, 121, 10):
        R = nc["fc"][lead // NC_DT - 1][PSL].ravel()
        pm = np.nan_to_num(R) >= 0.1
        typ = np.full(R.shape, np.nan, np.float32)
        typ[np.isfinite(R)] = 0
        if pm.any():
            cl = advect_nearest(cls_now, nc["mot"], lead)[PSL].ravel()[pm]
            if Hz is not None and lead <= 60:
                cl = np.where(advect_nearest(Hz["hail"].astype(np.float32), nc["mot"], lead)[PSL].ravel()[pm] >= 1, 10, cl)
            mlb = mlb0[pm].copy(); mt = None
            if met is not None:
                T = met["T"][pm].copy(); Td = met["Td"][pm].copy()
                if nwp is not None:
                    dT, dTd, dH = nwp_trend(nwp, t, t + timedelta(minutes=lead), lat[pm], lon[pm])
                    T = T + dT; Td = np.minimum(Td + dTd, T); mlb = mlb + dH
                mt = {"T": T, "Td": Td, "Tw": wet_bulb(T, Td)}
            elif nwp is not None:
                mlb = mlb + nwp_trend(nwp, t, t + timedelta(minutes=lead), lat[pm], lon[pm])[2]
            typ[pm] = surface_type(cl, hz[pm], mlb, mt)
        out[lead] = typ.reshape(2 * HALF + 1, 2 * HALF + 1)
    return out


def iso_at(iso, lat, lon):
    P = np.array(iso["pts"], float)
    d = np.hypot((lat[:, None] - P[None, :, 0]) * KY, (lon[:, None] - P[None, :, 1]) * KX)
    w = 1.0 / np.maximum(d, 5.0) ** 2
    return (w * P[None, :, 2]).sum(1) / w.sum(1), (w * P[None, :, 3]).sum(1) / w.sum(1)


def vol_geometry(code, root, tilts, pix):
    """porțile pe toate elevațiile pentru punctele radarului (cache)"""
    w = root.get("where", {})
    lat0, lon0, h0 = float(w["lat"]), float(w["lon"]), float(w.get("height", 0.0))
    sig = json.dumps([code, round(lat0, 4), round(lon0, 4), round(h0), [[round(t["el"], 2), t["nrays"], t["nbins"], t["rscale"], t["rstart"]] for t in tilts], int(pix.size), GH, GW])
    key = hashlib.md5(sig.encode()).hexdigest()[:10]
    p = os.path.join(CACHE, "vgeom_%s_%s.npz" % (code, key))
    if os.path.exists(p):
        with np.load(p) as d:
            return {k: d[k] for k in d.files}
    az, s = az_range(lat0, lon0, GLAT.ravel()[pix], GLON.ravel()[pix])
    ne = len(tilts)
    bins = np.full((ne, pix.size), -1, np.int32); rays = np.zeros((ne, pix.size), np.int32); hb = np.full((ne, pix.size), np.nan, np.float32)
    for k, t in enumerate(tilts):
        r, h = slant_from_ground(s, t["el"], h0)
        ib = np.floor((r - t["rstart"]) / t["rscale"]).astype(np.int32)
        ok = (ib >= 0) & (ib < t["nbins"])
        bins[k, ok] = ib[ok]; hb[k] = h
        rays[k] = (np.floor(az / (360.0 / t["nrays"])).astype(np.int32)) % t["nrays"]
    g = {"bins": bins, "rays": rays, "h": hb}
    np.savez_compressed(p + ".tmp.npz", **g)
    os.replace(p + ".tmp.npz", p)
    return g


def column_products(res, iso):
    """VIL, ET18, H45, MESH, POH și rafala Stewart pentru punctele unui radar (volumul complet de reflectivitate)"""
    code, ts, pix = res["code"], res["ts"], res["pix"]
    names = ["dataset%d" % k for k in range(1, 21)]
    root, sz = read_volume(code, ts, "dBZ", names)
    tilts = sorted(sz.values(), key=lambda t: t["el"])
    tilts = [t for t in tilts if t["el"] <= 30]
    vg = vol_geometry(code, root, tilts, pix)
    ne = len(tilts)
    Z = np.full((ne, pix.size), np.nan, np.float32)
    for k, t in enumerate(tilts):
        v = decode(t)
        ok = vg["bins"][k] >= 0
        Z[k, ok] = v[vg["rays"][k][ok], vg["bins"][k][ok]]
    Z = np.where(np.isneginf(Z), np.nan, Z)
    # ecourile fixe și nemeteorologice de la elevația joasă nu trebuie să intre în coloană: punctele marcate ca
    # nemeteorologice la sol (clasele 1, 2) sunt excluse
    bad = np.isin(res["cls"], (1, 2))
    Z[:, bad] = np.nan
    H = vg["h"].astype(np.float64)
    lat, lon = GLAT.ravel()[pix], GLON.ravel()[pix]
    H0, H20 = iso_at(iso, lat, lon)
    Zc = np.minimum(np.nan_to_num(Z, nan=-99.0), 56.0)
    zl = np.where(Zc > -50, 10 ** (Zc / 10.0), 0.0)
    # VIL (kg/m²), trapez pe straturile dintre elevații
    q = 3.44e-6 * zl ** (4.0 / 7.0)
    dh = np.diff(H, axis=0)
    vil = np.nansum(0.5 * (q[1:] + q[:-1]) * np.where(dh > 0, dh, 0), 0)
    # vârfurile ecourilor
    def top(thr):
        m = np.nan_to_num(Z, nan=-99.0) >= thr
        hh = np.where(m, H, -np.inf).max(0)
        return np.where(np.isfinite(hh), hh, np.nan)
    et18 = top(18.0); h45 = top(45.0)
    # SHI / MESH (Witt et al. 1998)
    Zh = np.nan_to_num(Z, nan=-99.0)
    WZ = np.clip((Zh - 40.0) / 10.0, 0, 1)
    E = 5e-6 * 10 ** (0.084 * np.minimum(Zh, 80)) * WZ
    WT = np.clip((H - H0[None, :]) / np.maximum(H20 - H0, 100.0)[None, :], 0, 1)
    f = WT * E
    shi = 0.1 * np.sum(0.5 * (f[1:] + f[:-1]) * np.where(dh > 0, dh, 0), 0)
    mesh = 2.54 * np.sqrt(np.maximum(shi, 0))           # mm
    # POH
    dH = (h45 - H0) / 1000.0
    poh = np.where(np.isfinite(dH) & (dH > 0), np.clip(29 * np.log(np.maximum(dH, 1e-6)) + 50, 0, 100), 0.0)
    # rafala potențială (Stewart 1991) — doar în nucleele convective (VIL ≥ 10 kg/m² și ecou ≥ 40 dBZ)
    et_m = np.nan_to_num(et18, nan=0.0)
    wg2 = 20.628571 * vil - 3.125e-6 * et_m ** 2
    conv = (vil >= 10) & (np.nanmax(np.where(np.isnan(Z), -99, Z), 0) >= 40)
    wg = np.where(conv & (wg2 > 0), np.sqrt(np.maximum(wg2, 0)) * 3.6, np.nan)     # km/h
    seen = np.isfinite(Z).any(0)
    return {"vil": np.where(seen, vil, np.nan).astype(np.float32), "et18": et18.astype(np.float32), "h45": h45.astype(np.float32),
            "mesh": np.where(seen, mesh, np.nan).astype(np.float32), "poh": np.where(seen, poh, np.nan).astype(np.float32),
            "wg": wg.astype(np.float32), "ntilt": ne}


def hazards(per, iso_ok):
    """compozitul produselor de volum (în fiecare punct radarul cel mai apropiat) și zonele de risc"""
    n = GH * GW
    best = np.full(n, np.inf, np.float32)
    out = {k: np.full(n, np.nan, np.float32) for k in ("vil", "et18", "mesh", "poh", "wg")}
    for code, r in per.items():
        cp = r.get("col")
        if cp is None:
            continue
        take = r["s"] < best[r["pix"]]
        idx = r["pix"][take]
        best[idx] = r["s"][take]
        for k in out:
            out[k][idx] = cp[k][take]
    for k in out:
        out[k] = out[k].reshape(GH, GW)
    # nucleu convectiv: VIL ≥ 15 kg/m² (în ploaia stratiformă, banda strălucitoare lărgită de fascicul la distanță mare
    # poate ridica artificial ecoul de 45 dBZ peste izoterma 0 °C — limită cunoscută a POH/MESH, Witt et al. 1998)
    core = np.nan_to_num(out["vil"]) >= 15
    hail = np.zeros((GH, GW), np.uint8)
    hail[(np.nan_to_num(out["poh"]) >= 50) & core] = 1
    hail[(np.nan_to_num(out["mesh"]) >= 20) & core] = 2
    hail[(np.nan_to_num(out["mesh"]) >= 50) & core] = 3
    wind = np.zeros((GH, GW), np.uint8)
    wind[np.nan_to_num(out["wg"]) >= 60] = 1
    wind[np.nan_to_num(out["wg"]) >= 90] = 2
    risk = np.zeros((GH, GW), np.uint8)
    risk[hail == 1] = 1
    risk[(hail == 2) | (wind == 1)] = 2
    risk[(hail == 3) | (wind == 2)] = 3
    out.update({"hail": hail, "wind": wind, "risk": risk})
    return out


def advect_nearest(F, mot, minutes):
    """mută câmpul F înainte cu `minutes` după câmpul de deplasare (persistență lagrangiană)"""
    U = mot["u"] * minutes / 60.0; V = -mot["v"] * minutes / 60.0
    Y, X = np.meshgrid(np.arange(GH, dtype=np.float64), np.arange(GW, dtype=np.float64), indexing="ij")
    oy, ox = Y - V, X - U
    for _ in range(2):
        oy = Y - bilinear(V, (Y + oy) / 2, (X + ox) / 2, edge=True)
        ox = X - bilinear(U, (Y + oy) / 2, (X + ox) / 2, edge=True)
    iy = np.round(oy).astype(int); ix = np.round(ox).astype(int)
    ok = (iy >= 0) & (ix >= 0) & (iy < GH) & (ix < GW)
    out = np.zeros_like(F)
    out[ok] = F[iy[ok], ix[ok]]
    return out


# ---------------- GitHub ----------------
GH_API = os.environ.get("ALARO_GH_API", "https://api.github.com")


def gh_conf():
    p = os.path.join(HERE, "github.txt")
    if not os.path.exists(p):
        return None
    c = {}
    for line in open(p, encoding="utf-8-sig"):
        if "=" in line:
            k, v = line.split("=", 1); c[k.strip().lower()] = v.strip()
    return c if c.get("repo") and c.get("token") else None


def gh(conf, method, path, data=None, ok404=False):
    url = "%s/repos/%s%s" % (GH_API, conf["repo"], path)
    body = json.dumps(data).encode() if data is not None else None
    for i in range(5):
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
            raise RuntimeError("GitHub %s %s -> %s %s" % (method, path, e.code, msg))
        except (urllib.error.URLError, ConnectionError, TimeoutError, OSError) as e:
            if i == 4:
                raise
            time.sleep(5 * (i + 1))




# ---------------- publicare ----------------
def publish():
    conf = gh_conf()
    if not conf:
        return
    mine = [("radar.html", os.path.join(HERE, "radar.html"))] if os.path.exists(os.path.join(HERE, "radar.html")) else []
    for nm in sorted(os.listdir(OUT)):
        if nm.endswith((".dat", ".png", ".js")) and not nm.endswith(".key"):
            mine.append(("radar/" + nm, os.path.join(OUT, nm)))
    ref = gh(conf, "GET", "/git/refs/heads/gh-pages", ok404=True)
    if ref.get("_status") or "object" not in ref:
        log.warning("depozitul nu are încă pagina principală publicată; rulează întâi obs_harti.py")
        return
    com = gh(conf, "GET", "/git/commits/" + ref["object"]["sha"])
    t = gh(conf, "GET", "/git/trees/%s?recursive=1" % com["tree"]["sha"])
    existing = {e["path"]: e["sha"] for e in t.get("tree", []) if e.get("type") == "blob"}
    have = set(existing.values())
    tree = [{"path": p, "mode": "100644", "type": "blob", "sha": s} for p, s in existing.items() if not p.startswith("radar")]
    sent = 0
    for path, local in mine:
        data = open(local, "rb").read()
        sha = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
        if sha not in have:
            sha = gh(conf, "POST", "/git/blobs", {"content": base64.b64encode(data).decode(), "encoding": "base64"})["sha"]
            sent += 1
        tree.append({"path": path, "mode": "100644", "type": "blob", "sha": sha})
    tsha = gh(conf, "POST", "/git/trees", {"tree": tree})["sha"]
    csha = gh(conf, "POST", "/git/commits", {"message": "radar Galați", "tree": tsha, "parents": []})["sha"]
    gh(conf, "PATCH", "/git/refs/heads/gh-pages", {"sha": csha, "force": True})
    log.info("publicat radar (%d fișiere trimise)", sent)


# ---------------- cadre pentru momentele recuperate ----------------
def light_frame(m, C, per):
    """cadrul paginii pentru un moment recuperat după o întrerupere (doar observația: imaginile, buletinul,
       cumulele; fără prognoză, deplasare sau produse de volum complet, care au sens doar pentru momentul curent)"""
    t = ts_time(m + "0000")
    a1, a1h, _ = accum_1km(1, t)
    a24, a24h, _ = accum_1km(24, t)
    head, lines = bulletin(t, C, per, None, a1, a1h)
    lines = [l for l in lines if not l.startswith(("Deplasarea ecourilor", "Precipitațiile din amonte"))]
    write_frame(m, C, per, a1, a24, None)
    return {"key": m, "t": t.strftime("%Y-%m-%dT%H:%MZ"), "head": head, "lines": lines,
            "radars": {k: {"t": ts_time(v["ts"]).strftime("%H:%M"), "lat": v["lat"], "lon": v["lon"], "el": v["elev"],
                           "wl": v["wl"], "ml": v.get("ml"), "fixed": v.get("fixed_km2")} for k, v in per.items()},
            "motion": None, "met": C.get("met_key"), "arrows": [], "nowcast": False,
            "nc_why": "moment recuperat ulterior: prognoza se calculează doar pentru imaginea cea mai nouă",
            "verif": None, "hazard": False, "iso": None, "recovered": True,
            "a1": a1h.strftime("%Y-%m-%dT%H:%MZ") if a1 is not None else None,
            "a24": a24h.strftime("%Y-%m-%dT%H:%MZ") if a24 is not None else None}


# ---------------- principal ----------------
def main():
    t_start = time.time()
    for d in (OUT, CACHE, QPE):
        os.makedirs(d, exist_ok=True)
    now = datetime.now(timezone.utc)
    st_p = os.path.join(QPE, "stare.json")
    try:
        S = json.load(open(st_p, encoding="utf-8"))
    except Exception:
        S = {}
    S.setdefault("done", {}); S.setdefault("ml", {})
    state_p = os.path.join(OUT, "frames.json")
    try:
        state = json.load(open(state_p, encoding="utf-8"))
    except Exception:
        state = {"frames": []}
    if state.get("bounds") and [round(x, 4) for x in state["bounds"]] != [round(x, 4) for x in BOUNDS]:
        state = {"frames": []}
    if state.get("format") != 2:
        state = {"frames": []}
    # 1. ce volume există la ANM
    with ThreadPoolExecutor(len(RCODES)) as ex:
        lists = dict(zip(RCODES, ex.map(lambda c: _safe(listing, c, default={}), RCODES)))
    lim = (now - timedelta(hours=LOOKBACK_H)).strftime("%Y%m%d%H%M")
    avail = {}
    for code, found in lists.items():
        for ts, prods in found.items():
            if ts[:12] >= lim and all(p in prods for p in ("dBZ", "ZDR", "KDP", "RhoHV")):
                avail.setdefault(ts[:12], {})[code] = ts
    avail_minutes = set(avail)
    # un moment de timp se procesează când toate radarele au volumul, sau după 15 minute (radar lipsă)
    ready = [m for m in sorted(avail) if m not in S["done"] and
             (len(avail[m]) == len(RCODES) or now - ts_time(m + "0000") >= timedelta(minutes=15))]
    if not ready:
        log.info("niciun volum nou")
    newest = ready[-1] if ready else None
    order = ([newest] if newest else []) + [m for m in ready if m != newest]      # întâi cel mai nou (pentru pagină), apoi recuperarea
    hours = Hours()
    shown = None
    recovered = []
    nproc = 0
    for m in order:
        if time.time() - t_start > BUDGET_S:
            log.info("timp epuizat: %d momente rămân pentru rularea următoare", len(order) - nproc)
            break
        # volumul complet (strat de topire + profil vertical) se citește cel mult o dată la 30 de minute pe radar
        tried = S.setdefault("ml_try", {})
        want = {c: (now - datetime.fromisoformat(tried[c]) > timedelta(minutes=29)) if c in tried else True for c in avail[m]}
        want = {c: w and m == newest for c, w in want.items()}
        for c, w in want.items():
            if w:
                tried[c] = now.isoformat()

        def one(code):
            try:
                return code, process_radar(code, avail[m][code], want[code]), None
            except Exception as e:
                return code, None, e
        with ThreadPoolExecutor(len(avail[m])) as ex:
            got = list(ex.map(one, list(avail[m])))
        per = {}
        for code, r, err in got:
            if r is None:
                log.warning("%s %s: volumul nu poate fi citit (%s)", code, m, err)
                continue
            if r.get("ml"):
                S["ml"][code] = {"t": now.isoformat(), "ml": r["ml"]}
            if r.get("vobs") is not None:
                S.setdefault("vpr", {})[code] = vpr_update(S.get("vpr", {}).get(code), r["vobs"], now)
            per[code] = r
        if not per:
            S["done"][m] = []
            nproc += 1
            continue
        # strat de topire: al radarului (≤ 3 ore), altfel media celorlalte
        mlr = {c: v["ml"] for c, v in S["ml"].items() if now - datetime.fromisoformat(v["t"]) <= timedelta(hours=3)}
        for code, r in per.items():
            ml = mlr.get(code)
            if ml is None and mlr:
                ml = [float(np.mean([v[i] for v in mlr.values()])) for i in range(3)]
            st = S.get("vpr", {}).get(code)
            if st and now - datetime.fromisoformat(st["t"]) > timedelta(hours=3):
                st = None
            fl = ml[2] if ml else None
            prof = vpr_profile(st, fl, r["h0"])
            classify(r, ml, prof)
            if m == newest:
                d = r["dzv"][r["valid"] & (r["cls"] >= 3)]
                log.info("%s profil vertical: %s", code, "convectiv — fără corecție" if prof and prof.get("conv") else
                         ("corecție la sol medie %+.1f dB (de la %+.1f la %+.1f) pe %d puncte cu precipitații" % (float(d.mean()), float(d.min()), float(d.max()), d.size)
                          if prof and d.size else ("indisponibil" if not prof else "fără precipitații")))
        C = composite(per)
        if m == newest and C.get("vpr_px"):
            pmm = C["cls"] >= 3
            log.info("corecția VPR pe %d puncte: intensitate medie %.2f → %.2f mm/h, maximă %.1f → %.1f mm/h",
                     C["vpr_px"], float(np.nanmean(C["rate_nv"][pmm])), float(np.nanmean(C["rate"][pmm])),
                     float(np.nanmax(C["rate_nv"][pmm])), float(np.nanmax(C["rate"][pmm])))
        hours.add(m, C["rate"].ravel(), C["qvalid"].ravel())
        save_comp(m, C)
        S["done"][m] = sorted(per)
        nproc += 1
        if m == newest:
            shown = (m, C, per)
        elif newest and m[-1] == newest[-1] and ts_time(newest + "0000") - ts_time(m + "0000") <= timedelta(minutes=FRAME_SPAN_MIN):
            try:
                recovered.append(light_frame(m, C, per))
            except Exception as e:
                log.warning("cadrul recuperat %s nu a putut fi scris (%s)", m, e)
        if nproc % 12 == 0:
            hours.save()
    hours.save()
    fin = finalize_hours(hours, avail_minutes, now, set(S["done"]))
    S["done"] = {k: v for k, v in S["done"].items() if k >= lim}
    json.dump(S, open(st_p + ".tmp", "w", encoding="utf-8")); os.replace(st_p + ".tmp", st_p)
    log.info("procesate %d momente (%.0f s, %.1f MB descărcați în %d cereri); ore închise: %s",
             nproc, time.time() - t_start, STATS["bytes"] / 1e6, STATS["req"], ", ".join(fin) or "—")
    if shown is None:
        return bool(fin)
    m, C, per = shown
    t = ts_time(m + "0000")
    key = m
    a1, a1h, _ = accum_1km(1, now)
    a24, a24h, n24 = accum_1km(24, now)
    # --- grindină și rafale din volumul complet (doar dacă există nuclee ≥ 40 dBZ) ---
    Hz = None; iso = None; hz_note = None
    if any(np.nanmax(np.append(np.where(r["cls"] >= 3, r["Z"], np.nan), -99)) >= 40 for r in per.values()):
        try:
            iso = isotherms(now)
        except Exception as e:
            hz_note = "izotermele 0 °C / −20 °C din model nu sunt disponibile (%s); grindina nu se poate estima" % e
            log.warning(hz_note)
        if iso is not None:
            for code, r in per.items():
                if np.nanmax(np.append(np.where(r["cls"] >= 3, r["Z"], np.nan), -99)) >= 40:
                    try:
                        r["col"] = column_products(r, iso)
                    except Exception as e:
                        log.warning("%s: volumul complet nu poate fi citit (%s)", code, e)
            Hz = hazards(per, True)
    # --- deplasare și prognoză 2 h ---
    nc = None
    try:
        nc = nowcast(m)
    except Exception as e:
        log.exception("prognoza imediată a eșuat (%s)", e)
    mot = None; arrows = []; verif = None
    if nc and nc.get("mot"):
        M = nc["mot"]
        mot = {"vx": M["um"], "vy": M["vm"], "kmh": math.hypot(M["um"], M["vm"]),
               "spre": (math.degrees(math.atan2(M["um"], M["vm"])) + 360) % 360, "n": M["n"], "cc": round(M["ccm"], 2)}
        rain = np.nan_to_num(C["rate"]) >= 0.1
        # săgeți la 20 km, unde există precipitații în 15 km
        for i in range(PR0 + 15, PR0 + 2 * HALF, 30):
            for j in range(PC0 + 15, PC0 + 2 * HALF, 30):
                if PDIST[i - PR0, j - PC0] > RADIUS or not rain[max(0, i - 15):i + 16, max(0, j - 15):j + 16].any():
                    continue
                arrows.append([round(float(GLON[i, j]), 4), round(float(GLAT[i, j]), 4), round(float(M["u"][i, j]), 1), round(float(M["v"][i, j]), 1)])
    if nc and nc.get("fc"):
        save_forecasts(m, nc["fc"])
        try:
            save_zforecasts(m, nc)
        except Exception as e:
            log.warning("salvarea prognozelor de reflectivitate pentru verificare a eșuat (%s)", e)
    try:
        verif = verify_nowcast(m, C["rate"])
        try:
            Vz = verify_reflectivity(m)
            for ln in zverif_summary(Vz):
                log.info("verificare reflectivitate (%d cazuri din %s): %s", len(Vz["cases"]), Vz["since"], ln)
        except Exception as e:
            log.warning("verificarea reflectivității a eșuat (%s)", e)
    except Exception as e:
        log.warning("verificarea prognozei a eșuat (%s)", e)
    head, lines = bulletin(t, C, per, mot, a1, a1h)
    # completări: prognoza pentru Galați, riscuri, verificare
    drop = ("Surse:", "Deplasarea ecourilor") + (("Precipitațiile din amonte",) if nc and nc.get("fc") else ())
    lines = [l for l in lines if not l.startswith(drop)] + extra_lines(C, nc, Hz, mot, verif, hz_note, iso) + doppler_line(per, Hz) + [l for l in lines if l.startswith("Surse:")]
    files = write_frame(key, C, per, a1, a24, Hz)
    if nc and nc.get("fc"):
        ftyp = None
        try:
            ftyp = fc_surface_types(C, nc, t, Hz)
        except Exception as e:
            log.warning("tipul precipitației în prognoză a eșuat (%s)", e)
        write_nowcast(key, nc, Hz, ftyp)
    frame = {"key": key, "t": t.strftime("%Y-%m-%dT%H:%MZ"), "head": head, "lines": lines,
             "radars": {k: {"t": ts_time(v["ts"]).strftime("%H:%M"), "lat": v["lat"], "lon": v["lon"], "el": v["elev"],
                            "wl": v["wl"], "ml": v.get("ml"), "fixed": v.get("fixed_km2")} for k, v in per.items()},
             "motion": mot, "met": C.get("met_key"), "arrows": arrows,
             "nowcast": bool(nc and nc.get("fc")), "nc_why": (nc or {}).get("why"), "verif": verif,
             "hazard": Hz is not None, "iso": iso and {"h0": round(float(np.mean([p[2] for p in iso["pts"]]))), "h20": round(float(np.mean([p[3] for p in iso["pts"]])))},
             "a1": a1h.strftime("%Y-%m-%dT%H:%MZ") if a1 is not None else None,
             "a24": a24h.strftime("%Y-%m-%dT%H:%MZ") if a24 is not None else None}
    newkeys = {key} | {f["key"] for f in recovered}
    state["frames"] = [f for f in state["frames"] if f["key"] not in newkeys] + recovered + [frame]
    state["frames"].sort(key=lambda f: f["key"])
    # fereastra paginii: ultimele 3 ore față de imaginea cea mai nouă (nu ultimele N cadre: după o întrerupere
    # nu trebuie să apară imagini de acum câteva ore lângă cea de acum)
    lim_f = (t - timedelta(minutes=FRAME_SPAN_MIN)).strftime("%Y%m%d%H%M")
    state["frames"] = [f for f in state["frames"] if f["key"] >= lim_f][-KEEP_FRAMES:]
    if recovered:
        log.info("cadre recuperate: %s", ", ".join(f["key"] for f in recovered))
    keep = {f["key"] for f in state["frames"]}
    for nm in os.listdir(OUT):
        if re.match(r"\d{12}_", nm) and nm[:12] not in keep:
            os.remove(os.path.join(OUT, nm))
    state.pop("sat_mot", None)            # extrapolarea imaginii de satelit a fost scoasă (la cererea utilizatorului)
    vis = visibility(C) if len(per) == len(RCODES) or not state.get("vis") else state["vis"]
    state.update({"format": 2, "vis": vis, "bounds": BOUNDS, "center": CENTER, "radius_km": RADIUS, "half": HALF,
                  "kx": KX, "ky": KY, "classes": CLASSES, "cls_col": CLS_COL, "sfc": SFC, "sfc_col": SFC_COL,
                  "radar_names": RADARS, "rcodes": RCODES, "pal": PAL,
                  "updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")})
    with open(state_p + ".tmp", "w", encoding="utf-8") as fh:
        json.dump(state, fh, ensure_ascii=False)
    os.replace(state_p + ".tmp", state_p)
    with open(os.path.join(OUT, "frames.js"), "w", encoding="utf-8") as fh:
        fh.write("window.RADAR_STATE=" + json.dumps(state, ensure_ascii=False) + ";\n")
    for nm in os.listdir(CACHE):          # cache vechi (volume întregi din versiunea anterioară)
        if nm.endswith(".hdf"):
            try:
                os.remove(os.path.join(CACHE, nm))
            except OSError:
                pass
    log.info("%s | %s", head, " ".join(lines))
    return True


def _safe(f, *a, default=None):
    try:
        return f(*a)
    except Exception as e:
        log.warning("%s%s: %s", f.__name__, a, e)
        return default


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s",
                        handlers=[logging.FileHandler(os.path.join(HERE, "radar_galati.log"), encoding="utf-8")]
                        + ([logging.StreamHandler(sys.stdout)] if sys.stdout else []))
    # paznic: o rulare blocată (de ex. o conexiune care nu se mai termină) ar împiedica pornirea rulărilor următoare
    # din Task Scheduler; după 9,5 minute procesul se oprește singur, iar rularea următoare reia de unde a rămas
    def _watchdog():
        log.error("rularea a depășit 9,5 minute — oprită forțat ca să nu blocheze rulările următoare")
        logging.shutdown()
        os._exit(3)
    _wd = threading.Timer(570, _watchdog); _wd.daemon = True; _wd.start()
    log.info("pornit")
    try:
        changed = main()
        if changed or "--publica" in sys.argv:
            if "--fara-publicare" not in sys.argv:
                publish()
    except Exception:
        log.exception("radarul a eșuat")
        sys.exit(1)
