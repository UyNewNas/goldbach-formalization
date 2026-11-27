"""Authenticate the actual Batteries cache probe without running a controller.

The accepted derived facet table supplies historical input authority.  The cache
producer receipt supplies auxiliary provenance, and the probe supplies current
metadata plus exact file hashes for the five Lemma facets only.
"""
from __future__ import annotations

import base64
import hashlib
import json
from pathlib import PurePosixPath


CACHE_PROBE_PIN = {
    "bytes": 2729017,
    "sha256": "58688582f77ce9fad0536e4e2077725e9d9b80c238b38d22b686ab377798ff74",
}
SNAPSHOT_SHA = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
TABLE_SHA = "e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636"
SOURCE_REVISION = "41bd267b3f6b7252f6676af46d4ffc6783b64de9"
CACHE_ROOT = PurePosixPath("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169")
CACHE_LIB = CACHE_ROOT / "active/lib"
DERIVED_ROOT = PurePosixPath("/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77/verification-import-order-resume-v3/original-external-derived")
SOURCE_ROOT = PurePosixPath("/workspace/goldbach-p2/.lake/packages/batteries")
DONOR_ROOT = PurePosixPath("/workspace/compile-deps/mathlib/.lake/packages/batteries")
HISTORICAL_SOURCE_ROOT = PurePosixPath("/home/runner/work/_temp/t01-project/.lake/packages/batteries")
FACETS = frozenset({".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"})
RECORD_PINS = {
    "CHECKPOINT.json": {
        "path": str(CACHE_ROOT / "CHECKPOINT.json"), "bytes": 67075207,
        "sha256": "aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a",
    },
    "REQUEST.json": {
        "path": str(CACHE_ROOT / "REQUEST.json"), "bytes": 447257,
        "sha256": "9b33d3b252c02b3ab1e5ca75532efddd0f95136ef9daecf185b1aba40457a965",
    },
    "SNAPSHOT_SHAPE.json": {
        "path": str(DERIVED_ROOT / "SNAPSHOT_SHAPE.json"), "bytes": 3445,
        "sha256": "b9892b552f36317dc29a9bb0b63cb0e7b5b1c664565483cbb908854bd723c221",
    },
    "batteries_receipt": {
        "path": str(CACHE_ROOT / "standard-input-overlays/batteries.json"), "bytes": 1048751,
        "sha256": "8b07545f47252a5a906310e8e1bb2c2259f3815cd0693c8b39b740c09456a8f8",
    },
    "producer_script": {
        "path": str(CACHE_ROOT / "tooling/qualifier-9358919122485744f044333334aeb4106902f5b959b87b46d2349d1cb4842745.py"),
        "bytes": 52729,
        "sha256": "9358919122485744f044333334aeb4106902f5b959b87b46d2349d1cb4842745",
    },
}
PAYLOAD_RECORDS = frozenset({"REQUEST.json", "SNAPSHOT_SHAPE.json", "batteries_receipt"})


class CacheInputError(ValueError):
    pass


def _check(condition, message):
    if not condition:
        raise CacheInputError(message)


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _valid_sha(value):
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def _valid_stat(value, size):
    return (isinstance(value, list) and len(value) == 5 and
            all(type(part) is int and part >= 0 for part in value) and value[2] == size)


def _file_metadata(row, path, size, label, require_path=True):
    # The actual probe's "exists" is Path.is_file(), not Path.exists().
    _check(isinstance(row, dict) and row.get("exists") is True and
           row.get("is_symlink") is False, label + " is not an observed regular nonsymlink file")
    _check(row.get("resolved_path") == path and
           (not require_path or row.get("path") == path), label + " path differs")
    _check(_valid_stat(row.get("stat"), size), label + " stat or size differs")


def _decode_record(row, expected):
    try:
        data = base64.b64decode(row["base64"], validate=True)
    except (ValueError, TypeError, KeyError) as error:
        raise CacheInputError("record payload is not valid base64") from error
    _check(len(data) == expected["bytes"] and _sha(data) == expected["sha256"],
           "record payload differs from its exact observed pin")
    return data


def _validate_records(report):
    records = report["records"]
    _check(isinstance(records, dict) and set(records) == set(RECORD_PINS), "cache record inventory differs")
    raw = {}
    for name, expected in RECORD_PINS.items():
        row = records[name]
        _check(all(row.get(key) == value for key, value in expected.items()), "cache record pin differs: " + name)
        _file_metadata(row, expected["path"], expected["bytes"], "cache record " + name)
        _check(("base64" in row) == (name in PAYLOAD_RECORDS), "cache record payload inventory differs: " + name)
        if name in PAYLOAD_RECORDS:
            raw[name] = _decode_record(row, expected)
    return raw


def _validate_report(report):
    """Validate semantics after the public entry point authenticates raw bytes."""
    _check(isinstance(report, dict) and report.get("schema") == "p29_frozen_batteries_original_cache_readonly_probe_v1",
           "cache probe schema differs")
    _check(all(type(report.get(key)) is int and report[key] == 0
               for key in ["Lean_invocations", "filesystem_writes", "new_formal_credit"]),
           "cache probe has unexpected effects or credit")
    table = report["original_derived_table"]
    table_path = str(DERIVED_ROOT / "P2_DECLARED_FACETS.jsonl")
    _check(table.get("bytes") == 23833463 and table.get("sha256") == TABLE_SHA,
           "accepted derived table pin differs")
    _file_metadata(table, table_path, 23833463, "accepted derived table")

    record_raw = _validate_records(report)
    receipt = json.loads(record_raw["batteries_receipt"])
    request = json.loads(record_raw["REQUEST.json"])
    shape = json.loads(record_raw["SNAPSHOT_SHAPE.json"])
    snapshot = report["raw_snapshot_descriptor"]
    _check(snapshot.get("bytes") == 20904189 and snapshot.get("sha256") == SNAPSHOT_SHA and
           shape.get("schema") == "p29_ad438_actual_snapshot_shape_v1" and shape.get("raw_source") == snapshot,
           "original snapshot descriptor differs from accepted shape")
    _check(isinstance(report["original_snapshot_file_entries"], dict), "raw snapshot file entries must be a mapping")
    # Missing raw snapshot file/receipt linkage is recorded, not promoted into a new gate.

    _check(receipt.get("schema") == "p2-winner9-batteries-overlay-v1" and
           receipt.get("status") == "EXACT_ORIGINAL_INPUT_BYTES_RESTORED_NOT_QUALIFICATION" and
           receipt.get("active_root") == str(CACHE_LIB) and receipt.get("module_count") == 192 and
           receipt.get("facet_count") == 960, "auxiliary Batteries receipt boundary differs")
    _check(all(receipt.get(key) is False for key in ["compile_credit", "kernel_credit", "baseline_modified", "donor_modified"]) and
           type(receipt.get("source_compiler_invocations")) is int and receipt["source_compiler_invocations"] == 0,
           "auxiliary receipt has unexpected compiler effects or credit")
    _check(request.get("schema") == "p2-winner9-owner-native-cache-request-v1" and
           request.get("status") == "READY_FOR_BYTE_TRANSPORT_ONLY" and
           all(request.get(key) is False for key in ["cache_acceptance", "compile_credit", "kernel_credit"]),
           "auxiliary cache request boundary differs")
    checkpoint = RECORD_PINS["CHECKPOINT.json"]
    _check(request["artifact"]["checkpoint_bytes"] == checkpoint["bytes"] and
           request["artifact"]["checkpoint_sha256"] == receipt.get("checkpoint_sha256") == checkpoint["sha256"] and
           receipt.get("request_sha256") == RECORD_PINS["REQUEST.json"]["sha256"] and
           receipt.get("producer_script") == RECORD_PINS["producer_script"]["path"] and
           receipt.get("producer_script_sha256") == RECORD_PINS["producer_script"]["sha256"],
           "auxiliary request/checkpoint/producer identity join differs")
    _check(request.get("locked_packages") == report["locked_packages"] and
           request["locked_packages"]["batteries"]["rev"] == receipt.get("source_pin") == SOURCE_REVISION,
           "Batteries source revision differs")

    rows = []
    seen = set()
    modules = {}
    hashed_modules = set()
    hashed_count = 0
    for wrapper in report["accepted_cached_standard_facets"]:
        original = wrapper["original"]
        module = original["module"]
        if module != "Batteries" and not module.startswith("Batteries."):
            continue
        facet = original["facet"]
        key = (module, facet)
        _check(key not in seen, "duplicate Batteries module/facet")
        seen.add(key)
        _check(facet in FACETS, "Batteries facet is outside the accepted five facets")
        modules.setdefault(module, set()).add(facet)
        identity = original["identity"]
        relative = module.replace(".", "/") + facet
        expected_path = str(CACHE_LIB / relative)
        _check(identity.get("path") == expected_path, "accepted Batteries module/facet path differs")
        _check(type(identity.get("bytes")) is int and identity["bytes"] >= 0 and _valid_sha(identity.get("sha256")),
               "accepted Batteries size/SHA identity is invalid")
        _check(original.get("original_snapshot_sha256") == SNAPSHOT_SHA, "Batteries original snapshot differs")
        association = "original_resolutions_entry" if facet == ".olean" else "existing_exact_companion_path_in_files"
        _check(original.get("association") == association, "accepted Batteries facet association differs")
        current = wrapper["current"]
        _file_metadata(current, expected_path, identity["bytes"], "current Batteries input", require_path=False)
        if module == "Batteries.Tactic.Lemma":
            exact = wrapper.get("current_exact_file")
            _check(isinstance(exact, dict) and exact.get("bytes") == identity["bytes"] and
                   exact.get("sha256") == identity["sha256"], "Lemma observed hash does not equal accepted identity")
            _file_metadata(exact, expected_path, identity["bytes"], "current exact Lemma input")
            _check(exact["stat"] == current["stat"], "Lemma exact-hash and metadata stat differ")
            hashed_count += 1
            hashed_modules.add(module)
        else:
            _check("current_exact_file" not in wrapper, "unexpected fresh hash claim beyond Lemma")
        rows.append(wrapper)
    _check(len(rows) == 960 and len(modules) == 192 and
           all(facets == FACETS for facets in modules.values()), "Batteries selection must contain 192 modules and 960 rows with five facets each")
    _check(hashed_count == 5, "Lemma must have five observed facet hashes")
    rows.sort(key=lambda row: (row["original"]["module"], row["original"]["facet"]))
    expected_relatives = {row["original"]["module"].replace(".", "/") + row["original"]["facet"] for row in rows}
    _check(isinstance(receipt.get("facets"), dict) and set(receipt["facets"]) == expected_relatives,
           "auxiliary receipt facet inventory differs from selected table rows")
    for wrapper in rows:
        original = wrapper["original"]
        relative = original["module"].replace(".", "/") + original["facet"]
        evidence = receipt["facets"][relative]
        identity = original["identity"]
        _check(evidence.get("module") == original["module"] and evidence.get("target") == identity["path"] and
               evidence.get("bytes") == identity["bytes"] and evidence.get("sha256") == identity["sha256"],
               "auxiliary receipt facet identity differs from selected table row: " + relative)
        _check(evidence.get("donor_path") == str(DONOR_ROOT / ".lake/build/lib/lean" / relative) and
               evidence.get("original_path") == str(HISTORICAL_SOURCE_ROOT / ".lake/build/lib/lean" / relative),
               "auxiliary receipt donor/historical path provenance differs: " + relative)
    _check(set(receipt.get("sources", {})) == set(modules), "auxiliary receipt source inventory differs")
    group = report["active_namespace_groups"]["Batteries"]
    _check(group == {"facets": 960, "missing": [], "modules": 192, "present": 960, "size_mismatches": []},
           "Batteries current namespace metadata count differs")

    for name, expected_root in [("source_root", SOURCE_ROOT), ("donor_root", DONOR_ROOT)]:
        root = report["source_roots"][name]
        path = str(expected_root)
        git = root["git"]
        _check(receipt.get(name) == root.get("path") == root.get("resolved") == path and root.get("is_dir") is True and
               git["toplevel"].get("exit_code") == git["HEAD"].get("exit_code") == git["tracked_diff"].get("exit_code") == 0 and
               git["toplevel"].get("stdout") == path and git["HEAD"].get("stdout") == SOURCE_REVISION and
               git["tracked_diff"].get("stdout") == "", "source/donor tracked-tree or pinned revision differs")
    lemma_source = report["lemma_source_row"]
    _check(lemma_source == receipt["sources"]["Batteries.Tactic.Lemma"], "Lemma source receipt join differs")
    _check(lemma_source.get("original_source") == str(HISTORICAL_SOURCE_ROOT / "Batteries/Tactic/Lemma.lean"),
           "Lemma historical source provenance differs")
    for name, root in [("source", SOURCE_ROOT), ("donor_source", DONOR_ROOT)]:
        path = str(root / "Batteries/Tactic/Lemma.lean")
        _check(lemma_source.get(name) == path, "Lemma source/donor path differs")
        source = report["lemma_source_files"][path]
        _file_metadata(source, path, lemma_source["bytes"], "current Lemma source/donor")
        _check(source.get("bytes") == lemma_source["bytes"] and source.get("sha256") == lemma_source["sha256"],
               "Lemma source/donor observed hash differs")

    provenance = {
        "selection_authority": "accepted_original_derived_facet_table",
        "accepted_table": {"path": table_path, "bytes": 23833463, "sha256": TABLE_SHA},
        "original_snapshot_sha256": SNAPSHOT_SHA,
        "selected_modules": 192,
        "selected_facets": 960,
        "excluded_standard_probe_rows": len(report["accepted_cached_standard_facets"]) - len(rows),
        "current_exact_hash_facets": hashed_count,
        "current_exact_hash_modules": sorted(hashed_modules),
        "metadata_only_facets": len(rows) - hashed_count,
        "all_current_facets_hashed": False,
        "runtime_actual_import_path_bytes_headers_and_facets_still_required": True,
        "receipt_is_historical_qualification_authority": False,
        "producer_records_role": "auxiliary_currently_observed_provenance_only",
        "record_pins": {name: dict(pin) for name, pin in RECORD_PINS.items()},
        "raw_snapshot_record_linkage_verified": False,
        "raw_snapshot_linkage_required_for_selection": False,
        "raw_snapshot_file_entry_count_observed": len(report["original_snapshot_file_entries"]),
        "raw_snapshot_file_currently_available": report["raw_snapshot_current_identity"]["exists"],
        "source_donor_revision": SOURCE_REVISION,
        "source_donor_tracked_tree_clean": True,
        "source_donor_untracked_file_status_claimed": False,
        "request_source_census_script_sha256": request["source_census"]["script_sha256"],
        "producer_script_sha256": RECORD_PINS["producer_script"]["sha256"],
        "new_formal_credit": 0,
    }
    return {
        "report": report,
        "rows": rows,
        "receipt": receipt,
        "receipt_raw": record_raw["batteries_receipt"],
        "request": request,
        "request_raw": record_raw["REQUEST.json"],
        "record_raw": record_raw,
        "provenance": provenance,
        "cache_lib": str(CACHE_LIB),
    }


def load_cache_context(raw: bytes) -> dict:
    """Load only the exact completed probe independently pinned by the parent."""
    _check(isinstance(raw, bytes) and len(raw) == CACHE_PROBE_PIN["bytes"] and
           _sha(raw) == CACHE_PROBE_PIN["sha256"], "actual cache probe byte pin differs")
    try:
        report = json.loads(raw)
        return _validate_report(report)
    except (KeyError, TypeError, IndexError) as error:
        raise CacheInputError("actual cache probe has malformed required fields") from error
