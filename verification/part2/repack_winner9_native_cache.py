#!/usr/bin/env python3
"""Copy a finite requested subset of an existing T01 cache into small archives.

This is byte transport, not cache qualification.  Original source, setup, trace,
guarded command, quarantine classification and payload bytes remain unchanged.
No compiler, kernel, object loader, network client or authentication API is run.
The caller downloads the fixed old artifact using ordinary authorized transport.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import zipfile

from inspect_winner9_owner_native import imports as source_imports


SCHEMA = "p2-winner9-owner-native-cache-request-v1"
READY = "READY_FOR_BYTE_TRANSPORT_ONLY"
ARTIFACT = {
    "repository": "UyNewNas/goldbach-formalization",
    "id": 13749339878, "run_id": 42753193835, "run_attempt": 1,
    "producer_commit": "cdc81d65ea82bd35ccc2ea19f916f65d84b7a3a1",
    "bytes": 3370363988,
    "sha256": "c506ac0c034e971c5554802a4e551762f122a42d25701b07a5a6c4c6471d4b7b",
    "checkpoint_bytes": 67075207,
    "checkpoint_sha256": "aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a",
}
PINS = {
    "goldbach": "09b97db5764ade1246bfb77206baa1b124760958",
    "mathlib": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",
    "LeanArchitect": "78dd66840d3efe8c824c699fc03381cec817c271",
}
ROOTS = [
    "ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows",
    "ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows",
    "ImbalancedChen.P2OriginalDescendingEighthLogSemantics",
    "ImbalancedChen.P2OriginalThirdMinorantLogDictionary",
    "ImbalancedChen.P2Winner9OriginalFull87Bridge",
]
ALLOWED_PREFIXES = {"MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd", "Architect", "ImbalancedChen"}
PORTABLE_SUFFIXES = {
    ".lean", ".olean", ".olean.private", ".olean.server", ".ilean",
    ".ir", ".ir.sig", ".c", ".bc", ".trace", ".setup.json", ".hash",
}
EXECUTABLE_SUFFIXES = (".so", ".a", ".o", ".o.export", ".o.noexport", ".exe")
# Leave one MiB for the upload action's outer single-file ZIP wrapper.
PART_LIMIT = 399 * 1024 * 1024
PART_RESERVE = 4 * 1024 * 1024
MAX_PARTS = 10
CENSUS_SCRIPT_SHA = "9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d"
CLASSIFIED = "PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND"
PROJECT_CLASSIFIED = "COMPILED_CHECKPOINT_ONLY_NOT_KERNEL_ACCEPTANCE"
ARCHITECT_QUARANTINE = "PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def encoded(value: dict) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def valid_module(name: str) -> bool:
    return (re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", name) is not None
            and name.split(".")[0] in ALLOWED_PREFIXES)


def package_for(name: str) -> str:
    prefix = name.split(".")[0]
    return "project" if prefix == "ImbalancedChen" else "LeanArchitect" if prefix == "Architect" else "goldbach"


def validate_request(request: dict) -> None:
    require(request.get("schema") == SCHEMA and request.get("status") == READY,
            "The actual complete source census has not finalized this request")
    require(request.get("artifact") == ARTIFACT, "Fixed original artifact identity changed")
    require(request.get("project_roots") == ROOTS, "The four-owner compatibility scope changed")
    require(all(request.get(k) is False for k in ("compile_credit", "kernel_credit", "cache_acceptance")),
            "A byte carrier cannot grant proof/cache credit")
    census = request["source_census"]
    require(census.get("script_sha256") == CENSUS_SCRIPT_SHA
            and file_sha(Path(__file__).with_name("inspect_winner9_owner_native.py")) == CENSUS_SCRIPT_SHA,
            "The selected source-census parser identity changed")
    require(re.fullmatch("[0-9a-f]{64}", census.get("sha256") or "") is not None,
            "The actual source census needs an immutable SHA256")
    require(census.get("status") == "SOURCE_GRAPH_COMPLETE_CACHE_ACCEPTANCE_PENDING",
            "Missing or incomplete selected source graph")
    require(census.get("project_source_count") == 247, "Unexpected original compatibility graph size")
    requested = request["requested"]
    require(isinstance(requested, dict) and requested
            and len(requested) == census["native_source_count"] + census["project_source_count"],
            "Requested full source count differs from the actual census")
    require(sum(r["package"] == "project" for r in requested.values()) == census["project_source_count"],
            "Requested project source count differs from the actual census")
    require(all(name in requested for name in ROOTS), "An actual owner/bridge root is missing")
    for package, pin in PINS.items():
        require(request["locked_packages"][package]["rev"] == pin, "Locked dependency pin changed")
    for name, row in requested.items():
        require(valid_module(name), "Unrelated/invalid requested module: " + name)
        require(row["package"] == package_for(name), "Wrong selected module package")
        require(row["source_path"] == name.replace(".", "/") + ".lean", "Source path/module mismatch")
        require(re.fullmatch("[0-9a-f]{64}", row["source_sha256"]) is not None
                and re.fullmatch("[0-9a-f]{40}", row["git_blob_sha1"]) is not None
                and isinstance(row["source_bytes"], int) and row["source_bytes"] > 0,
                "Missing exact selected source identity")
        for dep in row["direct_imports"]:
            if dep.split(".")[0] in ALLOWED_PREFIXES:
                require(dep in requested, "Requested source graph is not closed: " + dep)
    require(len(request["direct_native_roots"]) == 21
            and all(name in requested for name in request["direct_native_roots"]),
            "The actual 21 native entry points are not retained")
    actual_native_roots = sorted({dep for row in requested.values() if row["package"] == "project"
                                  for dep in row["direct_imports"]
                                  if dep.split(".")[0] in ALLOWED_PREFIXES - {"ImbalancedChen", "Architect"}})
    require(actual_native_roots == request["direct_native_roots"], "Native entry-point edges changed")
    reachable, visiting = set(), set()

    def visit(name: str) -> None:
        require(name not in visiting, "Cyclic requested import graph")
        if name in reachable:
            return
        visiting.add(name)
        for dep in requested[name]["direct_imports"]:
            if dep in requested:
                visit(dep)
        visiting.remove(name)
        reachable.add(name)

    for name in ROOTS:
        visit(name)
    require(reachable == set(requested), "The request contains modules outside the actual owner root closure")


def make_request(census_path: Path, template_path: Path, output: Path) -> None:
    census_bytes, template_bytes = census_path.read_bytes(), template_path.read_bytes()
    census, request = json.loads(census_bytes), json.loads(template_bytes)
    require(census["schema"] == "p2-owner-native-source-census-v1"
            and census["status"] == "SOURCE_GRAPH_COMPLETE_CACHE_ACCEPTANCE_PENDING"
            and not census["missing"] and census["roots"] == ROOTS,
            "Use the actual complete private-workspace owner census")
    require(census["source_compiler_or_object_loader_invocations"] == 0
            and census["source_or_baseline_modifications"] == 0
            and census["cache_acceptance"] is False, "Unexpected census provenance")
    for package, pin in PINS.items():
        require(census["packages"][package]["commit"] == pin
                and census["packages"][package].get("tracked_clean") is True,
                "The census does not bind the clean fixed source checkout")
    request["status"] = READY
    request["artifact"] = ARTIFACT
    request["project_roots"] = ROOTS
    request["direct_native_roots"] = census["direct_native_roots"]
    request["source_census"] = {
        "sha256": digest(census_bytes), "script_sha256": census["script_sha256"],
        "status": census["status"], "project_source_count": census["project_source_count"],
        "native_source_count": census["native_source_count"],
        "source_census_invoked_compiler": False,
    }
    request["requested"] = {
        name: {"package": row["package"], "source_path": row["relative"],
               "source_sha256": row["sha256"], "git_blob_sha1": row["git_blob_sha1"],
               "source_bytes": row["bytes"], "direct_imports": row["imports"]}
        for name, row in census["nodes"].items()
    }
    validate_request(request)
    require(not output.exists(), "Write a new request file, then review the exact replacement")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(encoded(request))
    print("REQUEST", output, file_sha(output), "modules", len(request["requested"]))


def validate_remote_metadata(metadata: dict) -> None:
    require(metadata["id"] == ARTIFACT["id"] and not metadata["expired"]
            and metadata["size_in_bytes"] == ARTIFACT["bytes"]
            and metadata["digest"] == "sha256:" + ARTIFACT["sha256"]
            and metadata["workflow_run"]["id"] == ARTIFACT["run_id"]
            and metadata["workflow_run"]["head_sha"] == ARTIFACT["producer_commit"],
            "GitHub metadata differs from the fixed old artifact")


def read_payload(archive: zipfile.ZipFile, row: dict) -> bytes:
    """Reuse the original checkpoint's exact member/length/SHA checks."""
    name = row.get("payload")
    require(isinstance(name, str) and re.fullmatch(r"objects/[0-9a-f]{64}", name) is not None,
            "Missing or unsafe original content-addressed payload")
    require(name == "objects/" + row["sha256"], "Payload filename does not bind its original SHA")
    info = archive.getinfo(name)
    require(info.file_size == row["bytes"] and info.file_size < PART_LIMIT - PART_RESERVE,
            "Original payload length changed or exceeds a bounded output packet")
    require(not info.flag_bits & 1 and info.compress_type == zipfile.ZIP_STORED
            and not stat.S_ISLNK(info.external_attr >> 16), "Unexpected original payload encoding")
    data = archive.read(info)  # zipfile also verifies the original ZIP CRC.
    require(len(data) == row["bytes"] and digest(data) == row["sha256"], "Original payload SHA changed")
    return data


def select_payloads(checkpoint: dict, request: dict) -> tuple[dict, dict, dict, list]:
    """Select only the requested source identities; preserve every old status."""
    selected, omitted, payloads, excluded_native = {}, {}, {}, []
    rows_by_name = {}
    for collection in ("all_guarded_package_compilations", "modules"):
        for index, row in enumerate(checkpoint[collection]):
            if row.get("module") in request["requested"]:
                package = "project" if collection == "modules" else row.get("package")
                rows_by_name.setdefault(row["module"], []).append((collection, index, package, row))
    for name, wanted in sorted(request["requested"].items()):
        matching = [(collection, index, row) for collection, index, package, row in rows_by_name.get(name, [])
                    if package == wanted["package"]
                    and row["source"]["sha256"] == wanted["source_sha256"]
                    and row["source"]["bytes"] == wanted["source_bytes"]]
        if not matching:
            omitted[name] = "NO_SOURCE_MATCHING_ORIGINAL_GUARDED_ROW"
            continue
        fingerprints = {digest(encoded({k: r.get(k) for k in
                         ("source", "setup", "facet_files", "classification", "command", "guarded_source_commands")}))
                        for _, _, r in matching}
        require(len(fingerprints) == 1, "Ambiguous original guarded providers: " + name)
        collection, index, row = matching[0]
        classification = row["classification"]
        leaf = name == "Architect.Command" and classification == ARCHITECT_QUARANTINE
        good_class = PROJECT_CLASSIFIED if wanted["package"] == "project" else CLASSIFIED
        if classification != good_class and not leaf:
            omitted[name] = "ORIGINAL_CLASSIFICATION_RETAINED_NOT_EXPORTED: " + classification
            continue
        if wanted["package"] == "project":
            require(row.get("completed_guarded_compile_candidate") and row.get("guarded_source_commands")
                    and not row.get("missing_expected_direct_imports")
                    and not row.get("observed_output_descriptor_contradiction")
                    and not row.get("missing_actual_import_artifacts"),
                    "Original project completed-output fields do not bind this selected row: " + name)
        else:
            require(row.get("lake_completed_trace") and row.get("output_bound_command")
                    and not row.get("missing_actual_import_artifacts"),
                    "Original native completed-output fields do not bind this selected row: " + name)
        original_sources = checkpoint["actual_import_sources"]
        origin = original_sources.get(name)
        if origin is not None:
            require(origin.get("package") == wanted["package"]
                    and origin.get("source", {}).get("sha256") == wanted["source_sha256"],
                    "Original imported source differs from its guarded source: " + name)
        source = row["source"]
        facets, excluded = [], []
        if wanted["package"] == "project":
            package_marker = checkpoint["runtime_state"]["root"] + "/"
            module_path = name.replace(".", "/")
            stems = [package_marker + ".lake/build/" + directory + "/" + module_path + "."
                     for directory in ("lib/lean", "ir")]
            original_facets = [value for path, value in checkpoint["files"].items()
                               if any(path.startswith(stem) for stem in stems)]
        else:
            package_marker = "/.lake/packages/" + wanted["package"] + "/"
            original_facets = row["facet_files"]
        relative_stems = [".lake/build/" + directory + "/" + name.replace(".", "/") + "."
                          for directory in ("lib/lean", "ir")]
        for facet in original_facets:
            original = facet["original_path"]
            require(package_marker in original, "Facet is not in its original selected package")
            relative = original.split(package_marker, 1)[1]
            require(relative.startswith(".lake/build/") and ".." not in PurePosixPath(relative).parts,
                    "Unexpected original facet location")
            require(any(relative.startswith(stem) for stem in relative_stems),
                    "Original facet belongs to another module: " + name)
            if relative.endswith(EXECUTABLE_SUFFIXES):
                excluded.append({"path": original, "sha256": facet["sha256"], "reason": "NATIVE_EXECUTABLE_NOT_CARRIED"})
                continue
            require(any(relative.endswith(suffix) for suffix in PORTABLE_SUFFIXES),
                    "Unreviewed output facet kind: " + original)
            facets.append(facet)
        facet_paths = {f["original_path"] for f in facets}
        require(set(row["required_output_parts"]) <= facet_paths,
                "An original required output part is absent from the byte selection: " + name)
        require(row["setup"]["original_path"] in facet_paths
                and any(f["original_path"].endswith(".trace") for f in facets),
                "Original setup/trace is missing: " + name)
        references = [source, row["setup"]]
        if "trace" in row:
            require(row["trace"]["original_path"] in facet_paths, "Original trace record is not a selected facet")
            references.append(row["trace"])
        for entry in [*references, *facets]:
            original = checkpoint["files"].get(entry["original_path"])
            require(original is not None and all(original.get(k) == entry.get(k)
                    for k in ("payload", "sha256", "bytes")), "Global/original payload records disagree")
            key = entry.get("payload")
            require(key is not None, "The selected original bytes were not archived")
            previous = payloads.get(key)
            require(previous is None or (previous["sha256"], previous["bytes"]) ==
                    (entry["sha256"], entry["bytes"]), "Conflicting content-addressed payload records")
            payloads[key] = entry
        selected[name] = {
            "package": wanted["package"], "original_record_collection": collection,
            "original_guarded_row_index": index,
            "original_classification": classification, "source": source,
            "setup": row["setup"], "facets": facets,
            "original_actual_import_map_sha256": row["actual_import_map_sha256"],
            "original_guarded_commands": row["guarded_source_commands"] if wanted["package"] == "project" else [row["command"]],
            "separate_architect_leaf_qualification_required": leaf,
            "source_bytes_verified_during_export": False,
            "source_object_import_runtime_qualification": "NOT_PERFORMED",
            "compile_credit": False, "kernel_credit": False, "cache_acceptance": False,
        }
        excluded_native.extend(excluded)
    return selected, omitted, payloads, excluded_native


def partition(payloads: dict, limit: int = PART_LIMIT) -> list[list[str]]:
    groups, current, size = [], [], 0
    for name, row in sorted(payloads.items()):
        cost = row["bytes"] + 2 * len(name.encode()) + 256
        require(cost < limit - PART_RESERVE, "One payload cannot fit the chosen packet budget")
        if current and size + cost > limit - PART_RESERVE:
            groups.append(current)
            current, size = [], 0
        current.append(name)
        size += cost
    if current:
        groups.append(current)
    require(len(groups) + 1 <= MAX_PARTS, "More packets than the fixed workflow can upload")
    return groups


def zip_write(archive: zipfile.ZipFile, name: str, data: bytes) -> None:
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and str(path) == name,
            "Unsafe byte-carrier member name")
    info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
    info.compress_type = zipfile.ZIP_STORED
    info.external_attr = 0o100644 << 16
    archive.writestr(info, data)


def repack(archive_path: Path, request_path: Path, metadata_path: Path, output: Path) -> None:
    request_bytes, metadata_bytes = request_path.read_bytes(), metadata_path.read_bytes()
    request, metadata = json.loads(request_bytes), json.loads(metadata_bytes)
    validate_request(request)
    validate_remote_metadata(metadata)
    require(not output.exists(), "Use a new output directory; never overwrite previous evidence")
    require(archive_path.is_file() and not archive_path.is_symlink()
            and archive_path.stat().st_size == ARTIFACT["bytes"], "Wrong original archive size/type")
    require(file_sha(archive_path) == ARTIFACT["sha256"], "Whole original artifact digest changed")
    with zipfile.ZipFile(archive_path) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)), "Duplicate names in original ZIP")
        info = archive.getinfo("CHECKPOINT.json")
        require(info.file_size == ARTIFACT["checkpoint_bytes"], "Wrong original checkpoint length")
        checkpoint_bytes = archive.read(info)
        require(digest(checkpoint_bytes) == ARTIFACT["checkpoint_sha256"], "Wrong original checkpoint SHA")
        cp = json.loads(checkpoint_bytes)
        require(cp["schema"] == "t01-coherent-build-checkpoint-v3"
                and cp["runtime_audit_valid"] and cp["all_dependency_source_pins_valid"],
                "Original checkpoint runtime/source audit did not pass")
        require(str(cp["run_id"]) == str(ARTIFACT["run_id"])
                and str(cp["run_attempt"]) == str(ARTIFACT["run_attempt"])
                and cp["source_commit"] == ARTIFACT["producer_commit"], "Original producer changed")
        locked = request["locked_packages"]
        require(len(cp["packages"]) == len(locked), "Original/requested dependency package census differs")
        for p in cp["packages"]:
            require(p["pin_matches"] and p["tracked_sources_clean"]
                    and locked.get(p["name"]) == {"rev": p["rev"], "url": p["url"]},
                    "Original/requested locked package identity differs")
        selected, omitted, payloads, excluded = select_payloads(cp, request)
        require(bool(selected), "No required original source identity is present; nothing to repack")
        for name, row in selected.items():
            source = read_payload(archive, row["source"])
            require(blob_sha(source) == request["requested"][name]["git_blob_sha1"],
                    "Original source bytes differ from the selected fixed Git blob: " + name)
            require(source_imports(source.decode()) == request["requested"][name]["direct_imports"],
                    "Original source imports differ from the requested source graph: " + name)
            row["source_bytes_verified_during_export"] = True
        groups = partition(payloads)
        output.mkdir(parents=True, exist_ok=False)
        part_rows = []
        for index, group in enumerate(groups, 1):
            path = output / f"part-{index:03}.zip"
            group_index = {
                "schema": "p2-original-native-byte-packet-v1", "part": index,
                "original_artifact": ARTIFACT, "request_sha256": digest(request_bytes),
                "payloads": {key: {"bytes": payloads[key]["bytes"], "sha256": payloads[key]["sha256"]}
                             for key in group}, "cache_acceptance": False,
            }
            with zipfile.ZipFile(path, "x", compression=zipfile.ZIP_STORED) as packet:
                zip_write(packet, "PACKET_INDEX.json", encoded(group_index))
                for key in group:
                    zip_write(packet, key, read_payload(archive, payloads[key]))
            require(path.stat().st_size <= PART_LIMIT, "Output packet exceeds 400 MiB")
            part_rows.append({"file": path.name, "bytes": path.stat().st_size,
                              "sha256": file_sha(path), "payload_count": len(group)})
            print("PACKET", path.name, path.stat().st_size, "bytes", flush=True)
        manifest = {
            "schema": "p2-original-native-byte-export-v1", "status": "BYTES_ONLY_NO_CACHE_OR_PROOF_ACCEPTANCE",
            "utc": datetime.now(timezone.utc).isoformat(), "script_sha256": file_sha(Path(__file__)),
            "github_caller": {k: os.environ.get(k) for k in
                              ("GITHUB_REPOSITORY", "GITHUB_SHA", "GITHUB_REF", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT")},
            "original_artifact": ARTIFACT, "whole_original_archive_sha256_verified": True,
            "original_checkpoint_sha256_verified": True, "request_sha256": digest(request_bytes),
            "selected_modules": selected, "not_exported": omitted,
            "excluded_native_executable_facets": excluded, "payload_packets": part_rows,
            "requested_count": len(request["requested"]), "exported_module_count": len(selected),
            "original_classification_counts": dict(Counter(r["original_classification"] for r in selected.values())),
            "original_bytes_or_classifications_modified": False,
            "compiler_or_kernel_or_object_loader_invocations": 0,
            "compile_credit": False, "kernel_credit": False, "cache_acceptance": False,
            "required_next_step": "Private-environment source/object/import/runtime qualification, then exact replay/audit",
        }
        path = output / "part-000.zip"
        with zipfile.ZipFile(path, "x", compression=zipfile.ZIP_STORED) as packet:
            for name, data in [("CHECKPOINT.json", checkpoint_bytes), ("REQUEST.json", request_bytes),
                               ("ORIGINAL_ARTIFACT_METADATA.json", metadata_bytes),
                               ("EXPORT_MANIFEST.json", encoded(manifest))]:
                zip_write(packet, name, data)
        require(path.stat().st_size <= PART_LIMIT, "Metadata packet exceeds 400 MiB")
        part_rows.insert(0, {"file": path.name, "bytes": path.stat().st_size,
                            "sha256": file_sha(path), "payload_count": 0})
    require(file_sha(archive_path) == ARTIFACT["sha256"], "Original archive changed during byte export")
    require(request_path.read_bytes() == request_bytes and metadata_path.read_bytes() == metadata_bytes,
            "Request/artifact metadata changed during export")
    summary = {
        "schema": "p2-original-native-byte-export-summary-v1",
        "status": "BYTES_ONLY_NO_CACHE_OR_PROOF_ACCEPTANCE", "parts": part_rows,
        "requested_count": len(request["requested"]), "exported_module_count": len(selected),
        "not_exported_count": len(omitted), "request_sha256": digest(request_bytes),
        "original_artifact_sha256": ARTIFACT["sha256"], "original_checkpoint_sha256": ARTIFACT["checkpoint_sha256"],
        "compiler_or_kernel_or_object_loader_invocations": 0,
        "compile_credit": False, "kernel_credit": False, "cache_acceptance": False,
    }
    (output / "SUMMARY.json").write_bytes(encoded(summary))
    print(json.dumps({k: summary[k] for k in ("status", "requested_count", "exported_module_count", "not_exported_count")}, indent=2))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="mode", required=True)
    prepare = commands.add_parser("request", help="Create a new final request from the actual complete source census")
    prepare.add_argument("--census", type=Path, required=True)
    prepare.add_argument("--template", type=Path, required=True)
    prepare.add_argument("--out", type=Path, required=True)
    validate = commands.add_parser("validate-request", help="Refuse pending or unrelated requests before downloading")
    validate.add_argument("--request", type=Path, required=True)
    remote = commands.add_parser("validate-metadata", help="Check the normal GitHub artifact response before download")
    remote.add_argument("--metadata", type=Path, required=True)
    export = commands.add_parser("repack", help="Copy verified original bytes into bounded independent packets")
    export.add_argument("--archive", type=Path, required=True)
    export.add_argument("--request", type=Path, required=True)
    export.add_argument("--metadata", type=Path, required=True)
    export.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.mode == "request":
        make_request(args.census, args.template, args.out)
    elif args.mode == "validate-request":
        validate_request(json.loads(args.request.read_bytes()))
        print("READY_FOR_BYTE_TRANSPORT_ONLY", file_sha(args.request))
    elif args.mode == "validate-metadata":
        validate_remote_metadata(json.loads(args.metadata.read_bytes()))
        print("FIXED_ORIGINAL_ARTIFACT_METADATA_MATCH")
    else:
        repack(args.archive, args.request, args.metadata, args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
