"""Build a deterministic v6 loader from an actual bootstrap and reviewed v5 code.

This builder performs local reads, syntax checks, hashing, and artifact writes.
It does not fetch blobs or execute a bootstrap, proof controller, or loader.
"""
from __future__ import annotations

import argparse
import ast
import difflib
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REVIEWED_LOADER = HERE.parent / "p29-v5-builder/transport/pinned_blob_loader.py"
REVIEWED_LOADER_SHA256 = "cc964642fa17b012af67f3a12fa7176bf5d3aa07df5b44366ddcb29349977de2"
MAX_BOOTSTRAP_BYTES = 1048576
PROBE_COMPRESSED_PIN = {
    "git_blob": "6a8e8c635154b81a7d8b84cb0473ef4d36b1c14d",
    "bytes": 310174,
    "sha256": "a5162d9275c14b4c33442ba642ceb0f28970a0c8ec3474a5444b513b9876bbd6",
}
PROBE_PLAIN_PIN = {
    "bytes": 1552271,
    "sha256": "706588ac2fe74f209fe256307f9d9073beb894e93baf45dd090928989ca54632",
}


class BuildError(ValueError):
    pass


def _require(condition, message):
    if not condition:
        raise BuildError(message)


def _pin(data):
    return {
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
        "git_blob": hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest(),
    }


def _read_regular(path, maximum, label):
    path = Path(path)
    _require(path.is_file() and not path.is_symlink(), label + " must be an existing regular nonsymlink file")
    before = path.stat()
    stamp = lambda value: (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns)
    _require(0 < before.st_size <= maximum, label + " is empty or exceeds the reviewed byte bound")
    data = path.read_bytes()
    _require(stamp(path.stat()) == stamp(before) and len(data) == before.st_size, label + " changed during its read")
    return data


def _assignment(source, name):
    tree = ast.parse(source)
    found = [node for node in tree.body if isinstance(node, ast.Assign) and
             len(node.targets) == 1 and isinstance(node.targets[0], ast.Name) and node.targets[0].id == name]
    _require(len(found) == 1, "reviewed pin assignment is not unique: " + name)
    return ast.get_source_segment(source, found[0])


def build(bootstrap_path, output, *, reviewed_loader=REVIEWED_LOADER):
    """Emit loader, exact patch, and binding only after authenticating inputs."""
    output = Path(output)
    _require(output.resolve().is_relative_to(HERE), "output must remain within the authorized v6 transport directory")
    _require(not output.exists() and not output.is_symlink(), "output directory already exists; no overwrite")
    bootstrap = _read_regular(bootstrap_path, MAX_BOOTSTRAP_BYTES, "actual bootstrap")
    original = _read_regular(reviewed_loader, MAX_BOOTSTRAP_BYTES, "reviewed loader")
    _require(hashlib.sha256(original).hexdigest() == REVIEWED_LOADER_SHA256, "reviewed loader SHA256 differs")
    try:
        compile(bootstrap, "v6-bootstrap-syntax-only", "exec")
    except (SyntaxError, ValueError) as error:
        raise BuildError("actual bootstrap is not valid Python source") from error
    source = original.decode("utf-8")
    bootstrap_pin = _pin(bootstrap)
    changes = []
    for name, value in [
        ("BOOTSTRAP_PIN", bootstrap_pin),
        ("CACHE_COMPRESSED_PIN", PROBE_COMPRESSED_PIN),
        ("CACHE_PLAIN_PIN", PROBE_PLAIN_PIN),
    ]:
        changes.append((name, _assignment(source, name), name + " = " + repr(value)))
    changes.extend([
        ("version_description", "then run v5.", "then run v6."),
        ("forwarded_probe_global", '"CACHE_PROBE_TEXT"', '"V5_PROBE_TEXT"'),
        ("bootstrap_filename_label", "p29-v5-exact-pinned-bootstrap.py", "p29-v6-exact-pinned-bootstrap.py"),
    ])
    changed = source
    for label, before, after in changes:
        _require(changed.count(before) == 1, "reviewed replacement is not unique: " + label)
        changed = changed.replace(before, after, 1)
    inverse = changed
    for label, before, after in reversed(changes):
        _require(inverse.count(after) == 1, "reviewed inverse is not unique: " + label)
        inverse = inverse.replace(after, before, 1)
    _require(inverse.encode("utf-8") == original, "reviewed source inverse did not recover exact bytes")
    compile(changed, "v6-loader-syntax-only", "exec")
    loader = changed.encode("utf-8")
    patch = "".join(difflib.unified_diff(source.splitlines(keepends=True), changed.splitlines(keepends=True),
                                         fromfile="v5/pinned_blob_loader.py", tofile="v6/pinned_blob_loader.py")).encode("utf-8")
    binding = {
        "schema": "p29_v6_exact_pinned_transport_binding_v1",
        "status": "STATIC_ONLY_NOT_EXECUTED_OR_SUBMITTED",
        "reviewed_v5_loader": _pin(original),
        "bootstrap": bootstrap_pin,
        "compressed_probe": dict(PROBE_COMPRESSED_PIN),
        "plain_probe": dict(PROBE_PLAIN_PIN),
        "loader": _pin(loader),
        "patch": _pin(patch),
        "forwarded_probe_global": "V5_PROBE_TEXT",
        "service_observation_globals": ["SERVICE_OBSERVATION_JSON", "SERVICE_OBSERVATION_SHA256"],
        "allowed_changes": [label for label, _, _ in changes],
        "reviewed_source_inverse_exact": True,
        "http_hash_size_decompression_and_observation_behavior_unchanged": True,
        "old_cache_http_fetch": False,
        "deterministic_artifacts_without_paths_or_timestamps": True,
        "network_or_bootstrap_execution_by_builder": False,
    }
    artifacts = {
        "pinned_blob_loader.py": loader,
        "V5_TO_V6_LOADER.patch": patch,
        "TRANSPORT_BINDING.json": (json.dumps(binding, sort_keys=True, indent=2) + "\n").encode("utf-8"),
    }
    output.mkdir(parents=True, exist_ok=False)
    for name, data in artifacts.items():
        with (output / name).open("xb") as stream:
            stream.write(data)
    return binding


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bootstrap", type=Path, required=True, help="Actual final v6 bootstrap file")
    parser.add_argument("--out", type=Path, required=True, help="New output directory beneath this transport workspace")
    args = parser.parse_args()
    try:
        binding = build(args.bootstrap, args.out)
    except (OSError, ValueError, SyntaxError) as error:
        print("V6_TRANSPORT_BUILD_BLOCKED: " + str(error), file=sys.stderr)
        return 2
    print(json.dumps({"out": str(args.out), "loader": binding["loader"], "bootstrap": binding["bootstrap"]}, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
