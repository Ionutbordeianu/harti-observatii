"""Rularea în cloud (GitHub Actions): radarul la fiecare rulare, observațiile ANM o dată pe oră.
   Starea (compozite, cumule orare, arhiva stațiilor, cadrele paginii) vine din memoria rulărilor anterioare;
   la prima rulare, din ramura „stare-initiala” (copia de pe calculator)."""
import os, subprocess, sys, tarfile, time
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
repo, token = os.environ["GITHUB_REPOSITORY"], os.environ["GH_TOKEN"]
with open("github.txt", "w", encoding="utf-8") as fh:
    fh.write("repo=%s\ntoken=%s\n" % (repo, token))


def log(msg):
    print(datetime.now(timezone.utc).strftime("%H:%M:%S"), msg, flush=True)


# 1. starea inițială, doar dacă memoria rulărilor lipsește (prima rulare sau memorie ștearsă)
if not os.path.exists("arhiva_orara.json"):
    url = "https://x-access-token:%s@github.com/%s.git" % (token, repo)
    if subprocess.call(["git", "clone", "-q", "--depth", "1", "-b", "stare-initiala", url, "_stare"]) == 0:
        with tarfile.open(os.path.join("_stare", "stare.tar.gz")) as tf:
            tf.extractall(HERE, filter="data")
        log("starea inițială refăcută din ramura stare-initiala")
    else:
        log("fără stare inițială: se pornește de la zero")

rc = 0
# 2. radarul (are propriul paznic de 9,5 minute)
log("radar")
r = subprocess.call([sys.executable, "radar_galati.py"])
if r != 0:
    log("radar: cod de ieșire %d" % r); rc = r
# 3. observațiile: o dată pe oră, după minutul 50 (ca pe calculator), sau dacă au trecut peste 70 de minute
mark = "_ultima_obs.txt"
last = float(open(mark).read()) if os.path.exists(mark) else 0.0
now = time.time()
minute = datetime.now(timezone.utc).minute
if (minute >= 50 and now - last >= 45 * 60) or now - last >= 70 * 60:
    log("observații ANM")
    r = subprocess.call([sys.executable, "obs_harti.py"])
    if r == 0:
        open(mark, "w").write(str(now))
    else:
        log("observații: cod de ieșire %d" % r); rc = rc or r
sys.exit(rc)
