"""Focused offline v6 generation and namespace tests; no proof bootstrap runs."""
import ast
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

try:
    import build_loader
except ModuleNotFoundError:
    build_loader = None


HERE = Path(__file__).resolve().parent
REVIEWED = HERE.parent / "p29-v5-builder/transport/pinned_blob_loader.py"
FIXTURE_BOOTSTRAP = b"received = {key: globals()[key] for key in ['V5_PROBE_TEXT', 'SERVICE_OBSERVATION_JSON', 'SERVICE_OBSERVATION_SHA256']}\nold_cache_forwarded = 'CACHE_PROBE_TEXT' in globals()\n"


class V6TransportTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(build_loader, "v6 transport builder is not implemented")

    def fixture(self, directory):
        path = directory / "fixture_bootstrap.py"
        path.write_bytes(FIXTURE_BOOTSTRAP)
        return path

    def literal(self, source, name):
        tree = ast.parse(source)
        node = next(node for node in tree.body if isinstance(node, ast.Assign)
                    and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                    and node.targets[0].id == name)
        return ast.literal_eval(node.value)

    def test_generation_uses_actual_bootstrap_and_exact_new_probe_pins(self):
        with tempfile.TemporaryDirectory(dir=HERE) as temporary:
            directory = Path(temporary)
            bootstrap = self.fixture(directory)
            output = directory / "generated"
            binding = build_loader.build(bootstrap, output)
            source = (output / "pinned_blob_loader.py").read_text()
            expected_bootstrap = {
                "bytes": len(FIXTURE_BOOTSTRAP),
                "sha256": hashlib.sha256(FIXTURE_BOOTSTRAP).hexdigest(),
                "git_blob": hashlib.sha1(b"blob " + str(len(FIXTURE_BOOTSTRAP)).encode() + b"\0" + FIXTURE_BOOTSTRAP).hexdigest(),
            }
            self.assertEqual(self.literal(source, "BOOTSTRAP_PIN"), expected_bootstrap)
            self.assertEqual(self.literal(source, "CACHE_COMPRESSED_PIN"), {
                "git_blob": "6a8e8c635154b81a7d8b84cb0473ef4d36b1c14d", "bytes": 310174,
                "sha256": "a5162d9275c14b4c33442ba642ceb0f28970a0c8ec3474a5444b513b9876bbd6",
            })
            self.assertEqual(self.literal(source, "CACHE_PLAIN_PIN"), {
                "bytes": 1552271, "sha256": "706588ac2fe74f209fe256307f9d9073beb894e93baf45dd090928989ca54632",
            })
            self.assertEqual(binding["bootstrap"], expected_bootstrap)
            self.assertEqual(binding["forwarded_probe_global"], "V5_PROBE_TEXT")

    def test_identical_input_bytes_generate_identical_artifacts(self):
        with tempfile.TemporaryDirectory(dir=HERE) as temporary:
            directory = Path(temporary)
            bootstrap = self.fixture(directory)
            first, second = directory / "one", directory / "two"
            build_loader.build(bootstrap, first)
            build_loader.build(bootstrap, second)
            self.assertEqual({p.name: p.read_bytes() for p in first.iterdir()},
                             {p.name: p.read_bytes() for p in second.iterdir()})

    def test_reviewed_behavior_recovers_byte_for_byte_after_allowed_inverse(self):
        with tempfile.TemporaryDirectory(dir=HERE) as temporary:
            directory = Path(temporary)
            output = directory / "generated"
            binding = build_loader.build(self.fixture(directory), output)
            source = (output / "pinned_blob_loader.py").read_text()
            original = REVIEWED.read_text()
            def function(text, name):
                node = next(node for node in ast.parse(text).body
                            if isinstance(node, ast.FunctionDef) and node.name == name)
                return ast.get_source_segment(text, node)
            self.assertEqual(function(source, "_fetch_blob"), function(original, "_fetch_blob"))
            for name in ["BOOTSTRAP_PIN", "CACHE_COMPRESSED_PIN", "CACHE_PLAIN_PIN"]:
                def assignment(text):
                    tree = ast.parse(text)
                    node = next(node for node in tree.body if isinstance(node, ast.Assign)
                                and isinstance(node.targets[0], ast.Name) and node.targets[0].id == name)
                    return ast.get_source_segment(text, node)
                source = source.replace(assignment(source), assignment(original), 1)
            source = source.replace('"V5_PROBE_TEXT"', '"CACHE_PROBE_TEXT"', 1)
            source = source.replace("then run v6.", "then run v5.", 1)
            source = source.replace("p29-v6-exact-pinned-bootstrap.py", "p29-v5-exact-pinned-bootstrap.py", 1)
            self.assertEqual(source.encode(), REVIEWED.read_bytes())
            self.assertIs(binding["reviewed_source_inverse_exact"], True)

    def test_changed_interface_forwards_new_probe_and_observation_without_old_cache(self):
        with tempfile.TemporaryDirectory(dir=HERE) as temporary:
            directory = Path(temporary)
            output = directory / "generated"
            build_loader.build(self.fixture(directory), output)
            namespace = {"__name__": "offline_v6_loader_test"}
            exec(compile((output / "pinned_blob_loader.py").read_bytes(), "offline_v6_loader_test", "exec"), namespace)
            fetched = []
            inflated = []
            probe = b'{"schema":"offline_v5_probe_fixture"}'
            def fetch(pin, *, opener=None):
                fetched.append(pin)
                return FIXTURE_BOOTSTRAP if pin is namespace["BOOTSTRAP_PIN"] else b"compressed-fixture"
            def inflate(compressed, pin):
                inflated.append((compressed, pin))
                return probe
            namespace["_fetch_blob"] = fetch
            namespace["_inflate_exact"] = inflate
            observation = '{"schema":"offline_observation_fixture"}'
            observation_sha = hashlib.sha256(observation.encode()).hexdigest()
            result = namespace["main"]({"SERVICE_OBSERVATION_JSON": observation,
                                         "SERVICE_OBSERVATION_SHA256": observation_sha})
            self.assertEqual(result["received"], {"V5_PROBE_TEXT": probe.decode(),
                                                  "SERVICE_OBSERVATION_JSON": observation,
                                                  "SERVICE_OBSERVATION_SHA256": observation_sha})
            self.assertIs(result["old_cache_forwarded"], False)
            self.assertEqual(fetched, [namespace["BOOTSTRAP_PIN"], namespace["CACHE_COMPRESSED_PIN"]])
            self.assertEqual(inflated, [(b"compressed-fixture", namespace["CACHE_PLAIN_PIN"])])

    def test_missing_or_empty_bootstrap_cannot_create_output(self):
        with tempfile.TemporaryDirectory(dir=HERE) as temporary:
            directory = Path(temporary)
            output = directory / "no-output"
            with self.assertRaises(ValueError):
                build_loader.build(directory / "missing.py", output)
            self.assertFalse(output.exists())
            empty = directory / "empty.py"
            empty.write_bytes(b"")
            with self.assertRaises(ValueError):
                build_loader.build(empty, output)
            self.assertFalse(output.exists())

    def test_changed_reviewed_loader_is_rejected_before_output(self):
        with tempfile.TemporaryDirectory(dir=HERE) as temporary:
            directory = Path(temporary)
            changed = directory / "changed-reviewed.py"
            changed.write_bytes(REVIEWED.read_bytes() + b"\n")
            output = directory / "no-output"
            with self.assertRaisesRegex(ValueError, "reviewed loader"):
                build_loader.build(self.fixture(directory), output, reviewed_loader=changed)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
