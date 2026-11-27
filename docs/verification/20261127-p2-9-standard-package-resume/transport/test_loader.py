"""Offline transport tests. The production bootstrap is never executed."""
import base64
import hashlib
import io
import json
from pathlib import Path
import unittest
import urllib.error
import zlib

import pinned_blob_loader as loader


def pin(data):
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
            "git_blob": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()}


def api_body(data, expected, **changes):
    row = {"sha": expected["git_blob"], "size": expected["bytes"], "encoding": "base64",
           "content": base64.encodebytes(data).decode()}
    row.update(changes)
    return json.dumps(row).encode()


class Response:
    def __init__(self, data, url, headers=None, status=200):
        self.data = io.BytesIO(data)
        self.url = url
        self.status = status
        self.headers = {"Content-Length": str(len(data))} if headers is None else headers
        self.read_sizes = []

    def __enter__(self):
        return self

    def __exit__(self, *args):
        return False

    def geturl(self):
        return self.url

    def read1(self, size):
        self.read_sizes.append(size)
        return self.data.read(size)


class LoaderTests(unittest.TestCase):
    def setUp(self):
        self.observation = '{"schema":"offline-test-only"}\n'
        self.observation_sha = hashlib.sha256(self.observation.encode()).hexdigest()
        self.cache = b'{"cache":"offline exact fixture"}\n'
        self.compressed = zlib.compress(self.cache, 9)
        self.bootstrap = ("assert __name__ == '__main__'\n"
                          "assert CACHE_PROBE_TEXT == " + repr(self.cache.decode()) + "\n"
                          "assert SERVICE_OBSERVATION_JSON == " + repr(self.observation) + "\n"
                          "assert SERVICE_OBSERVATION_SHA256 == " + repr(self.observation_sha) + "\n"
                          "STUB_EXECUTED = True\n").encode()
        self.bootstrap_pin, self.compressed_pin, self.plain_pin = map(pin, [self.bootstrap, self.compressed, self.cache])
        self.calls = []
        self.responses = {}
        for data, expected in [(self.bootstrap, self.bootstrap_pin), (self.compressed, self.compressed_pin)]:
            url = loader.API_ROOT + expected["git_blob"]
            self.responses[url] = Response(api_body(data, expected), url)

    def open(self, request, *, timeout):
        self.calls.append((request.full_url, timeout))
        response = self.responses[request.full_url]
        if isinstance(response, Exception):
            raise response
        return response

    def execute(self):
        return loader._execute_pinned(self.observation, self.observation_sha,
                                      self.bootstrap_pin, self.compressed_pin, self.plain_pin,
                                      opener=self.open)

    def test_success_executes_only_exact_stub_with_unchanged_globals(self):
        namespace = self.execute()
        self.assertIs(namespace["STUB_EXECUTED"], True)
        self.assertEqual(len(self.calls), 2)
        self.assertTrue(all(timeout == loader.HTTP_TIMEOUT_SECONDS for _, timeout in self.calls))

    def test_observation_hash_failure_precedes_all_http(self):
        self.observation_sha = "0" * 64
        with self.assertRaisesRegex(loader.LoaderError, "observation SHA256"):
            self.execute()
        self.assertEqual(self.calls, [])

    def test_transport_failure_is_not_retried(self):
        self.responses[loader.API_ROOT + self.bootstrap_pin["git_blob"]] = urllib.error.URLError("offline failure")
        with self.assertRaises(urllib.error.URLError):
            self.execute()
        self.assertEqual(len(self.calls), 1)

    def test_byte_corruption_fails_recomputed_git_identity(self):
        url = loader.API_ROOT + self.bootstrap_pin["git_blob"]
        damaged = b"X" + self.bootstrap[1:]
        self.responses[url] = Response(api_body(damaged, self.bootstrap_pin), url)
        with self.assertRaisesRegex(loader.LoaderError, "Git object SHA"):
            self.execute()
        self.assertEqual(len(self.calls), 1)

    def test_api_size_sha_and_encoding_must_match(self):
        url = loader.API_ROOT + self.bootstrap_pin["git_blob"]
        for change in [{"size": self.bootstrap_pin["bytes"] + 1}, {"sha": "0" * 40}, {"encoding": "utf-8"}]:
            with self.subTest(change=change):
                self.responses[url] = Response(api_body(self.bootstrap, self.bootstrap_pin, **change), url)
                with self.assertRaises(loader.LoaderError):
                    loader._fetch_blob(self.bootstrap_pin, opener=self.open)

    def test_decoded_size_and_sha256_are_independently_checked(self):
        url = loader.API_ROOT + self.bootstrap_pin["git_blob"]
        self.responses[url] = Response(api_body(self.bootstrap[:-1], self.bootstrap_pin), url)
        with self.assertRaisesRegex(loader.LoaderError, "decoded blob size"):
            loader._fetch_blob(self.bootstrap_pin, opener=self.open)
        wrong = {**self.bootstrap_pin, "sha256": "0" * 64}
        self.responses[url] = Response(api_body(self.bootstrap, wrong), url)
        with self.assertRaisesRegex(loader.LoaderError, "blob SHA256"):
            loader._fetch_blob(wrong, opener=self.open)

    def test_http_oversize_is_rejected_before_or_during_bounded_reads(self):
        url = loader.API_ROOT + self.bootstrap_pin["git_blob"]
        limit = loader._api_limit(self.bootstrap_pin)
        for headers in [{"Content-Length": str(limit + 1)}, {}]:
            with self.subTest(headers=headers):
                response = Response(b" " * (limit + 1), url, headers=headers)
                self.responses[url] = response
                with self.assertRaisesRegex(loader.LoaderError, "HTTP response"):
                    loader._fetch_blob(self.bootstrap_pin, opener=self.open)
                self.assertTrue(all(0 < count <= loader.READ_CHUNK_BYTES for count in response.read_sizes))
                self.assertLessEqual(response.data.tell(), limit + 1)

    def test_body_deadline_is_checked_after_each_read(self):
        readings = iter([0.0, 0.0, loader.HTTP_TIMEOUT_SECONDS + 1.0])
        with self.assertRaisesRegex(loader.LoaderError, "HTTP deadline"):
            loader._fetch_blob(self.bootstrap_pin, opener=self.open, clock=lambda: next(readings))

    def test_redirect_is_rejected_without_followup(self):
        with self.assertRaisesRegex(loader.LoaderError, "redirect"):
            loader._NoRedirect().redirect_request(None, None, 302, "Found", {}, "https://elsewhere.invalid/")
        self.assertEqual(self.calls, [])

    def test_compressed_trailing_data_or_concatenated_stream_is_rejected(self):
        for extra in [b"trailing", zlib.compress(b"second")]:
            with self.subTest(extra=extra):
                with self.assertRaisesRegex(loader.LoaderError, "trailing"):
                    loader._inflate_exact(self.compressed + extra, self.plain_pin)

    def test_truncated_or_oversized_decompression_is_rejected(self):
        with self.assertRaisesRegex(loader.LoaderError, "incomplete"):
            loader._inflate_exact(self.compressed[:-1], self.plain_pin)
        with self.assertRaisesRegex(loader.LoaderError, "decompressed size"):
            loader._inflate_exact(self.compressed, {**self.plain_pin, "bytes": len(self.cache) - 1})

    def test_decompressed_sha256_is_required(self):
        with self.assertRaisesRegex(loader.LoaderError, "decompressed SHA256"):
            loader._inflate_exact(self.compressed, {**self.plain_pin, "sha256": "0" * 64})

    def test_production_bootstrap_pin_matches_exact_final_file_without_execution(self):
        data = (Path(__file__).resolve().parent.parent / "generated-final/bootstrap.py").read_bytes()
        self.assertEqual(pin(data), loader.BOOTSTRAP_PIN)


if __name__ == "__main__":
    unittest.main()
