"""Publicarea pe GitHub mai robustă în cloud: GitHub refuză uneori arborii mari creați dintr-o dată
   („input too large” / „timed out”) sau răspunde temporar cu 5xx. Se aplică peste urllib, fără a modifica
   scripturile: arborii mari se construiesc pe bucăți (base_tree, cum recomandă GitHub), cererile eșuate
   temporar se repetă."""
import io, json, time, urllib.error, urllib.request

_orig = urllib.request.urlopen
CHUNK = 100


class _Resp(io.BytesIO):
    status = 201

    def getcode(self):
        return 201

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


def _send(req, body, timeout):
    r2 = urllib.request.Request(req.full_url, data=json.dumps(body).encode(), method="POST", headers=dict(req.header_items()))
    with _retry(r2, timeout) as r:
        return json.loads(r.read().decode())


def _retry(req, timeout, tries=5):
    for i in range(tries):
        try:
            return _orig(req, timeout=timeout)
        except urllib.error.HTTPError as e:
            if e.code in (500, 502, 503, 504) and i < tries - 1:
                time.sleep(10 * (i + 1)); continue
            if e.code == 422 and i < tries - 1:
                body = e.read().decode("utf-8", "replace")
                if "timed out" in body:
                    time.sleep(10 * (i + 1)); continue
                raise urllib.error.HTTPError(e.url, e.code, e.msg, e.hdrs, io.BytesIO(body.encode()))
            raise


def urlopen(req, *a, timeout=300, **k):
    if isinstance(req, urllib.request.Request) and req.full_url.startswith("https://api.github.com/"):
        if req.get_method() == "POST" and req.full_url.endswith("/git/trees") and req.data:
            d = json.loads(req.data.decode())
            tree = d.get("tree", [])
            if len(tree) > CHUNK and "base_tree" not in d:
                base = None
                for i in range(0, len(tree), CHUNK):
                    body = {"tree": tree[i:i + CHUNK]}
                    if base:
                        body["base_tree"] = base
                    base = _send(req, body, timeout)["sha"]
                return _Resp(json.dumps({"sha": base}).encode())
        return _retry(req, timeout)
    return _orig(req, *a, timeout=timeout, **k)


urllib.request.urlopen = urlopen
