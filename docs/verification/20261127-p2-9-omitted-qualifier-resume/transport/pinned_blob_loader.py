"""Fetch two exact public blobs once, authenticate all bytes, then run v6.

Inputs: SERVICE_OBSERVATION_JSON and SERVICE_OBSERVATION_SHA256 globals.
No network or bootstrap execution occurs when this module is imported.
"""
import base64
import hashlib
import json
import time
import urllib.request
import zlib

API_ROOT = "https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/"
BOOTSTRAP_PIN = {'bytes': 93325, 'sha256': 'd28b70f9445ce1dbaa58c4d12780c0b871549d2ddb5e1136e4225b3498a174ae', 'git_blob': 'fff63220837540a83e69b18dfebc173921ef4123'}
CACHE_COMPRESSED_PIN = {'git_blob': '6a8e8c635154b81a7d8b84cb0473ef4d36b1c14d', 'bytes': 310174, 'sha256': 'a5162d9275c14b4c33442ba642ceb0f28970a0c8ec3474a5444b513b9876bbd6'}
CACHE_PLAIN_PIN = {'bytes': 1552271, 'sha256': '706588ac2fe74f209fe256307f9d9073beb894e93baf45dd090928989ca54632'}
HTTP_TIMEOUT_SECONDS = 20.0
READ_CHUNK_BYTES = 65536
API_OVERHEAD_BYTES = 65536
MAX_BLOB_BYTES = 1048576
MAX_PLAIN_BYTES = 8388608
MAX_OBSERVATION_BYTES = 65536


class LoaderError(RuntimeError):
    pass


def _require(condition, message):
    if not condition:
        raise LoaderError(message)


def _hex(value, length):
    return isinstance(value, str) and len(value) == length and all(c in "0123456789abcdef" for c in value)


def _check_pin(pin, maximum, with_git=False):
    _require(isinstance(pin, dict) and type(pin.get("bytes")) is int and 0 < pin["bytes"] <= maximum,
             "invalid bounded byte pin")
    _require(_hex(pin.get("sha256"), 64), "invalid SHA256 pin")
    if with_git:
        _require(_hex(pin.get("git_blob"), 40), "invalid Git blob pin")


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise LoaderError("HTTP redirect is forbidden")


def _api_limit(pin):
    return 4 * ((pin["bytes"] + 2) // 3) + API_OVERHEAD_BYTES


def _fetch_blob(pin, *, opener=None, clock=None):
    _check_pin(pin, MAX_BLOB_BYTES, with_git=True)
    clock = time.monotonic if clock is None else clock
    opener = urllib.request.build_opener(_NoRedirect()).open if opener is None else opener
    url = API_ROOT + pin["git_blob"]
    request = urllib.request.Request(url, headers={
        "Accept": "application/vnd.github+json", "Accept-Encoding": "identity",
        "User-Agent": "p29-v5-exact-blob-loader",
    })
    limit = _api_limit(pin)
    deadline = clock() + HTTP_TIMEOUT_SECONDS
    chunks = []
    received = 0
    # read1 performs at most one buffered raw read, unlike read(n), which may
    # keep collecting a slow-drip response. Each read also has the socket timeout.
    with opener(request, timeout=HTTP_TIMEOUT_SECONDS) as response:
        _require(response.status == 200 and response.geturl() == url, "unexpected HTTP status or endpoint")
        _require(response.headers.get("Content-Encoding", "identity").lower() == "identity", "unexpected HTTP content encoding")
        declared = response.headers.get("Content-Length")
        if declared is not None:
            _require(declared.isascii() and declared.isdigit() and int(declared) <= limit,
                     "HTTP response Content-Length exceeds bound or is malformed")
        while True:
            _require(clock() <= deadline, "HTTP deadline exceeded")
            requested = min(READ_CHUNK_BYTES, limit + 1 - received)
            part = response.read1(requested)
            _require(clock() <= deadline, "HTTP deadline exceeded")
            _require(isinstance(part, bytes) and len(part) <= requested, "invalid HTTP bounded read")
            if not part:
                break
            received += len(part)
            _require(received <= limit, "HTTP response exceeds byte bound")
            chunks.append(part)
    body = b"".join(chunks)
    if declared is not None:
        _require(len(body) == int(declared), "HTTP response Content-Length differs from bytes read")
    row = json.loads(body)
    _require(isinstance(row, dict) and row.get("sha") == pin["git_blob"], "API blob SHA differs")
    _require(type(row.get("size")) is int and row["size"] == pin["bytes"], "API blob size differs")
    _require(row.get("encoding") == "base64" and isinstance(row.get("content"), str), "API blob encoding differs")
    encoded = row["content"].replace("\n", "").replace("\r", "")
    _require(len(encoded) == 4 * ((pin["bytes"] + 2) // 3), "encoded blob size differs")
    data = base64.b64decode(encoded, validate=True)
    _require(len(data) == pin["bytes"], "decoded blob size differs")
    git_sha = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
    _require(git_sha == pin["git_blob"], "recomputed Git object SHA differs")
    _require(hashlib.sha256(data).hexdigest() == pin["sha256"], "blob SHA256 differs")
    return data


def _inflate_exact(compressed, plain_pin):
    _check_pin(plain_pin, MAX_PLAIN_BYTES)
    _require(isinstance(compressed, bytes) and len(compressed) <= MAX_BLOB_BYTES, "compressed input exceeds bound")
    decompressor = zlib.decompressobj()
    data = decompressor.decompress(compressed, plain_pin["bytes"] + 1)
    _require(len(data) == plain_pin["bytes"], "decompressed size differs")
    _require(decompressor.eof, "incomplete compressed stream")
    _require(not decompressor.unconsumed_tail and not decompressor.unused_data, "compressed stream has trailing data")
    # No flush(): decompression already ended and its output was bounded.
    _require(hashlib.sha256(data).hexdigest() == plain_pin["sha256"], "decompressed SHA256 differs")
    return data


def _execute_pinned(observation, observation_sha, bootstrap_pin, compressed_pin, plain_pin, *, opener=None):
    _require(isinstance(observation, str), "observation must be exact JSON text")
    observed = observation.encode("utf-8")
    _require(0 < len(observed) <= MAX_OBSERVATION_BYTES, "observation exceeds byte bound")
    _require(_hex(observation_sha, 64) and hashlib.sha256(observed).hexdigest() == observation_sha,
             "observation SHA256 differs")
    _require(isinstance(json.loads(observed), dict), "observation must be a JSON object")
    bootstrap = _fetch_blob(bootstrap_pin, opener=opener)
    cache = _inflate_exact(_fetch_blob(compressed_pin, opener=opener), plain_pin)
    namespace = {"__name__": "__main__", "V5_PROBE_TEXT": cache.decode("utf-8"),
                 "SERVICE_OBSERVATION_JSON": observation, "SERVICE_OBSERVATION_SHA256": observation_sha}
    exec(compile(bootstrap, "p29-v6-exact-pinned-bootstrap.py", "exec"), namespace)
    return namespace


def main(namespace):
    return _execute_pinned(namespace["SERVICE_OBSERVATION_JSON"], namespace["SERVICE_OBSERVATION_SHA256"],
                           BOOTSTRAP_PIN, CACHE_COMPRESSED_PIN, CACHE_PLAIN_PIN)


if __name__ == "__main__":
    main(globals())
