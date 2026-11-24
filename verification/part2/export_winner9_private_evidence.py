#!/usr/bin/env python3
"""Export current, accepted P2 evidence without recompilation or kernel replay.

Only receipts whose complete project inputs, compilation bindings and stored
artifacts still match are credited. Diagnostic/benchmark/migration files are
context only. Packages contain sources and evidence, never .olean objects.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
import math
from pathlib import Path
import re
import subprocess
import tarfile

from run_winner9_private_checks import LEAN, MATHLIB, PIN, digest, json_digest
from run_winner9_private_audit import (
    LEANCHECKER, TEMPLATE, TEMPLATE_TARGET, parse_audit, project_nodes, replay_context, require, verify_compilation,
)

DRIVER_V1 = "05f31ad7f78c69bf58a1f0daab4b597db9a90190f255a880abdab22767c864b5"
DRIVER_V2 = "b214fe826d40f96c9907cb9c42f0ac96dcc9bc48dc080a264c9c13de2b43cc08"
DRIVER_V3 = "36b2e1252b3b926a22505e7a7489485c78b33d1fb6904060840dfc9d613a9637"
DRIVER_FILES = {DRIVER_V1: "driver-v1.py", DRIVER_V2: "driver-v2.py", DRIVER_V3: "driver-v3.py"}
COMPILE_BEFORE_BUDGET = "dc6cbb64bbcf1e3db7080ddc4fc0ebff4742e9cced16f325f9817344bfc1c480"
COMPILE_BUDGET_V2 = "df9949270753bb36cace92d70099de4a7c30dcea8f761ade36ecd03f50c5684d"
GEOMETRY = {"ImbalancedChen." + name for name in (
    ["P2Winner9PullingArchiveCore", "P2Winner9PullingOrderChecks"]
    + [f"P2Winner9CompletePullingData{i:02}" for i in range(44)]
    + ["P2Winner9CompletePullingData", "P2Winner9CompletePullingFlags"]
    + [f"P2Winner9CompletePullingCheck{i:02}" for i in range(44)]
    + ["P2Winner9CompletePullingGeometry"])}
CORES = {"ImbalancedChen." + name for name in (
    "OriginalAscendingThirteenRowDefinitions", "OriginalDescendingFifteenRowDefinitions",
    "P2OriginalDescendingEighthCapDefinitions", "P2OriginalThirdMinorantCapDefinitions",
    "P4AOriginalAscendingFourteenSourceDefinitions", "P4AOriginalFull87IntegralDefinitions",
    "P4AOriginalFull87SourceDefinitions", "P4AOriginalH3SourceDefinitions",
    "P4AOriginalH5H7SourceDefinitions", "P4AOriginalRemainingEighthSourceDefinitions",
    "P4AOriginalSeed7Unequal15SourceDefinitions")}
TEXT_SUFFIXES = {".json", ".log", ".txt", ".md", ".lean", ".py", ".patch"}


def encoded(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def local_path(root: Path, value: str) -> Path:
    path = (root / value).resolve()
    require(path.is_relative_to(root), "Evidence path escapes the verification worktree: " + value)
    return path


class Evidence:
    def __init__(self) -> None:
        self.files: dict[str, dict] = {}
        self.frozen: dict[Path, str] = {}
        self.external_contexts: dict[str, tuple[dict, object]] = {}
        self.accepted_external_contexts: set[str] = set()

    def freeze(self, path: Path) -> str:
        if path not in self.frozen:
            self.frozen[path] = digest(path)
        return self.frozen[path]

    def add_bytes(self, name: str, raw: bytes, origin: str, role: str) -> str:
        require(not Path(name).is_absolute() and ".." not in Path(name).parts, "Unsafe archive name")
        require(".olean" not in Path(name).suffixes and Path(name).suffix in TEXT_SUFFIXES,
                "Only textual evidence is exported: " + name)
        record = {"data": raw, "sha256": sha_bytes(raw), "bytes": len(raw), "origin": origin, "role": role}
        if name in self.files:
            require(self.files[name]["sha256"] == record["sha256"], "Conflicting archive file: " + name)
        else:
            self.files[name] = record
        return name

    def add_path(self, path: Path, name: str, role: str, expected: str | None = None) -> str:
        raw = path.read_bytes()
        require(expected is None or sha_bytes(raw) == expected, "Evidence artifact changed: " + str(path))
        return self.add_bytes(name, raw, str(path), role)

    def file_index(self, names=None) -> dict:
        return {name: {key: value for key, value in self.files[name].items() if key != "data"}
                for name in sorted(self.files if names is None else names)}

    def verify_frozen(self) -> None:
        for path, expected in self.frozen.items():
            require(digest(path) == expected, "A verified input changed during export: " + str(path))
        for key in self.accepted_external_contexts:
            binding, external = self.external_contexts[key]
            require(external.verify() == binding, "Accepted native environment changed during export")

    def bind_external(self, root: Path, binding: dict) -> str:
        from winner9_external_snapshot import ExternalSnapshot
        key = json_digest(binding)
        if key not in self.external_contexts:
            external = ExternalSnapshot(Path(binding["snapshot"]), lean=LEAN, mathlib_pin=PIN,
                                        project_lib=root / ".lake/p2-private/lib")
            require(external.binding() == binding, "Accepted native snapshot differs from the actual environment")
            self.external_contexts[key] = (binding, external)
        return key


def page_binding(module: str, source: str, declarations: list[dict]) -> dict | None:
    match = re.fullmatch(r"ImbalancedChen\.P2Winner9NumericalPage(\d{4})", module)
    if not match:
        return None
    page = int(match[1])
    require(0 <= page < 690, "Numerical page ordinal is out of range")
    bound = re.search(r"theorem\s+checked\s*:\s*Checked\s*\(fun\s+_\s+r\s*=>\s*checkSelected\s+r\s*=\s*true\)"
                      r"\s+(\d+)\s+(\d+)\s*\(P2Winner9CompleteSeedBlock(\d{2})\.pages\[(\d+)\]!\)", source)
    require(bound is not None, "Missing the original numerical page Checked statement")
    first, count, block, local_page = map(int, bound.groups())
    require((first, count, block, local_page) == (page * 16, min(16, 11026 - page * 16), page // 16, page % 16),
            "Numerical page statement is not bound to its original row interval")
    checked = [record for record in declarations if record["name"] == module + ".checked"]
    require(len(checked) == 1 and all(term in checked[0]["type"] for term in (
        "ImbalancedChen.P2Winner9SeedArchiveChecks.Checked",
        "ImbalancedChen.P2Winner9SelectedArchiveChecker.checkSelected",
        f"ImbalancedChen.P2Winner9CompleteSeedBlock{block:02}.pages")),
        "Owned checked declaration does not expose the expected checker/archive type")
    return {"page": page, "first_ordinal": first, "row_count": count,
            "last_ordinal": first + count - 1, "block": block, "local_page": local_page}


def validate_receipt(root: Path, target: str, receipt: dict, records: dict,
                     evidence: Evidence, drivers: dict[str, Path]) -> dict:
    require(receipt.get("accepted") is True and receipt.get("module") == target, "Not an accepted target receipt")
    frozen = receipt["input_snapshot"]
    require(receipt.get("input_sha256") == json_digest(frozen), "Input snapshot digest mismatch")
    require(frozen["driver_sha256"] in drivers, "Missing the exact accepted audit driver version")
    external_key = None
    if "external_snapshot" in frozen:
        require(frozen["driver_sha256"] not in {DRIVER_V1, DRIVER_V2},
                "A historical audit driver cannot bind a retrofitted native snapshot")
        external_key = evidence.bind_external(root, frozen["external_snapshot"])
    require(frozen["template_sha256"] == evidence.freeze(TEMPLATE), "Audit template differs from accepted bytes")
    require(frozen["lean_binary_sha256"] == evidence.freeze(Path(LEAN))
            and frozen["leanchecker_sha256"] == evidence.freeze(Path(LEANCHECKER))
            and frozen["toolchain"]["mathlib_commit"] == PIN, "Accepted toolchain differs from the live pinned environment")
    nodes = project_nodes(root, target)
    require(set(nodes) == set(frozen["project"]), "Project dependency closure differs from the accepted source")
    project = {}
    for name, node in nodes.items():
        obj = root / ".lake/p2-private/lib" / (name.replace(".", "/") + ".olean")
        actual = {"source": str(node["source"].relative_to(root)), "source_sha256": evidence.freeze(node["source"]),
                  "object": str(obj), "object_sha256": evidence.freeze(obj)}
        require(all(actual[key] == frozen["project"][name][key]
                    for key in ("source", "source_sha256", "object_sha256")),
                "Accepted source/object changed: " + name)
        project[name] = actual
    current = dict(frozen, project=project)
    verify_compilation(records, nodes, current)
    require(receipt.get("source_sha256") == project[target]["source_sha256"]
            and receipt.get("object_sha256") == project[target]["object_sha256"],
            "Target source/object metadata differs from its frozen dependency graph")
    require(receipt["compile_closure_signature"] == records[target]["closure_signature"],
            "The accepted target no longer matches its compiled closure signature")
    require(receipt.get("replay_binding") == replay_context(frozen),
        "Independent replay is not bound to the accepted dependency graph")
    replay, audit = receipt["replay"], receipt["audit"]
    require(replay.get("exit_code") == 0 and replay.get("inputs_unchanged") is True
            and replay.get("command") == [LEANCHECKER, "--verbose", target], "Independent replay receipt is incomplete")
    require(audit.get("exit_code") == 0 and audit.get("inputs_unchanged") is True, "Owned-declaration audit is incomplete")
    audit_source = local_path(root, audit["source"])
    expected_command = [LEAN, "-t0", "-j1", "-M6144", "-DwarningAsError=true",
                        "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", audit["source"]]
    require(audit.get("command") == expected_command, "Unexpected audit command")
    require(audit_source.read_bytes() == TEMPLATE.read_text().replace(TEMPLATE_TARGET, target).encode()
            and digest(audit_source) == audit["source_sha256"], "The actual audit source is not the exact target template")
    audit_log = local_path(root, audit["log"])
    replay_log = local_path(root, replay["log"])
    declarations_path, types_path = audit_source.parent / "declarations.json", audit_source.parent / "types.txt"
    artifacts = receipt.get("artifacts", {})
    required = {str(path.relative_to(root)) for path in (audit_source, audit_log, replay_log, declarations_path, types_path)}
    require(required <= set(artifacts), "Missing accepted artifact bindings")
    for relative, expected in artifacts.items():
        require(evidence.freeze(local_path(root, relative)) == expected, "Accepted artifact changed: " + relative)
    require(digest(audit_log) == audit["log_sha256"] and digest(replay_log) == replay["log_sha256"], "Stage log digest mismatch")
    parsed = parse_audit(audit_log, target, set(nodes))
    require(json.loads(declarations_path.read_text()) == parsed, "Stored declaration inventory differs from the actual audit log")
    require(types_path.read_text() == "\n\n".join(record["name"] + "\n" + record["type"]
            for record in parsed["declarations"]) + "\n", "Stored declaration types differ from the actual audit log")
    require(audit["declaration_count"] == parsed["declaration_count"]
            and audit["axiom_counts"] == parsed["axiom_counts"], "Stored audit counts differ from the owned inventory")
    return {"project": project, "nodes": nodes, "parsed": parsed, "external_key": external_key}


def package(path: Path, names: set[str], modules: list[str], evidence: Evidence, page_bytes: int) -> dict:
    index = {"package": path.name, "modules": modules, "files": evidence.file_index(names),
             "no_olean_objects": True, "diagnostic_files_grant_no_proof_credit": True}
    package_manifest = encoded(index)
    with path.open("wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w") as archive:
                for name, data in [("PACKAGE_MANIFEST.json", package_manifest)] + [
                        (name, evidence.files[name]["data"]) for name in sorted(names)]:
                    item = tarfile.TarInfo(name)
                    item.size, item.mode, item.mtime = len(data), 0o644, 0
                    archive.addfile(item, io.BytesIO(data))
    size = path.stat().st_size
    return {"path": str(path), "bytes": size, "sha256": digest(path), "modules": modules,
            "uncompressed_payload_bytes": sum(evidence.files[name]["bytes"] for name in names) + len(package_manifest),
            "base64_bytes": 4 * math.ceil(size / 3), "suggested_raw_page_bytes": page_bytes,
            "suggested_page_count": math.ceil(size / page_bytes)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*", help="Default: all module audit directories")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--split", choices=("all", "group", "module"), default="group")
    parser.add_argument("--transfer-page-bytes", type=int, default=1000000)
    parser.add_argument("--driver-file", type=Path, action="append", default=[])
    parser.add_argument("--extra-evidence", type=Path, action="append", default=[])
    args = parser.parse_args()
    require(0 < args.transfer_page_bytes <= 1500000, "Raw transfer pages must fit under the 2 MiB base64 stdout cap")
    root = Path.cwd().resolve()
    private = root / ".lake/p2-private"
    audit_root = private / "audit"
    output = (args.output_dir or private / "exports" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")).resolve()
    require(not output.exists(), "Use a new export directory; previous evidence is not overwritten")
    pin = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip()
    require(pin == PIN, "Live Mathlib checkout differs from the fixed pin")
    source_root = Path(__file__).resolve().parents[2]
    driver_paths = [source_root / "docs/verification/20261124-p2-private/driver-v1.py",
                    source_root / "docs/verification/20261124-p2-private/audit-driver-v2.py",
                    Path(__file__).with_name("run_winner9_private_audit.py"), *args.driver_file]
    drivers = {digest(path): path for path in driver_paths if path.is_file() and digest(path) in DRIVER_FILES}
    require({DRIVER_V1, DRIVER_V2} <= set(drivers), "Both exact historical audit driver versions must be available")
    records_raw = (private / "records.json").read_bytes()
    records = json.loads(records_raw)
    evidence = Evidence()
    common: set[str] = set()
    module_files: dict[str, set[str]] = {}
    accepted, rejected, unselected, warnings = {}, [], [], []
    project_union = {}
    owned_names: dict[str, list[str]] = defaultdict(list)
    targets = sorted(set(args.modules or [path.name for path in audit_root.iterdir()
                                         if path.is_dir() and path.name.startswith("ImbalancedChen.")]))
    for target in targets:
        require(re.fullmatch(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9]*)+", target) is not None, "Invalid module name")
        directory = audit_root / target
        candidates = list(directory.glob("attempt-*/receipt.json"))
        if (directory / "latest.json").exists():
            candidates.append(directory / "latest.json")
        candidates.sort(key=lambda path: path.stat().st_mtime_ns, reverse=True)
        seen = set()
        for candidate in candidates:
            try:
                raw = candidate.read_bytes()
                if sha_bytes(raw) in seen:
                    continue
                seen.add(sha_bytes(raw))
                receipt = json.loads(raw)
                if receipt.get("accepted") is not True:
                    continue
                verified = validate_receipt(root, target, receipt, records, evidence, drivers)
                pending_artifacts = []
                for relative, expected in receipt["artifacts"].items():
                    path = local_path(root, relative)
                    require(path.suffix in TEXT_SUFFIXES and ".olean" not in path.suffixes,
                            "Accepted artifact is not textual evidence")
                    data = path.read_bytes()
                    require(sha_bytes(data) == expected, "Accepted artifact changed before capture: " + relative)
                    pending_artifacts.append((relative, path, data))
                files = {evidence.add_bytes("audits/" + target + "/selected-receipt.json", raw,
                                           str(candidate), "accepted audit receipt snapshot")}
                for relative, path, data in pending_artifacts:
                    files.add(evidence.add_bytes("worktree/" + relative, data, str(path),
                                                "accepted audit/replay artifact"))
                project_union.update(verified["project"])
                module_files[target] = files
                parsed = verified["parsed"]
                for declaration in parsed["declarations"]:
                    owned_names[declaration["name"]].append(target)
                metadata = {"receipt_source": str(candidate), "receipt_sha256": sha_bytes(raw),
                            "source_sha256": receipt["source_sha256"], "object_sha256": receipt["object_sha256"],
                            "compile_closure_signature": receipt["compile_closure_signature"],
                            "driver_sha256": receipt["input_snapshot"]["driver_sha256"],
                            "declaration_count": parsed["declaration_count"], "axiom_counts": parsed["axiom_counts"],
                            "project_modules": sorted(verified["project"]), "artifact_paths": sorted(files)}
                if verified["external_key"] is not None:
                    evidence.accepted_external_contexts.add(verified["external_key"])
                    metadata["external_snapshot"] = receipt["input_snapshot"]["external_snapshot"]
                try:
                    metadata["page_binding"] = page_binding(target, verified["nodes"][target]["source"].read_text(),
                                                            parsed["declarations"])
                except ValueError as error:
                    metadata["page_binding"] = None
                    warnings.append({"module": target, "page_coverage_not_credited": str(error)})
                accepted[target] = metadata
                break
            except (OSError, ValueError, KeyError, TypeError) as error:
                rejected.append({"module": target, "receipt": str(candidate), "reason": str(error)})
        if target not in accepted:
            unselected.append(target)

    common.add(evidence.add_bytes("context/records.json", records_raw, str(private / "records.json"),
                                 "complete compile registry snapshot; not an accepted-module list"))
    selected_records = {name: records[name] for name in sorted(project_union)}
    common.add(evidence.add_bytes("context/selected-compile-records.json", encoded(selected_records),
                                 "subset of context/records.json", "compiled dependency graph for accepted modules"))
    for name, item in project_union.items():
        common.add(evidence.add_path(root / item["source"], "sources/" + item["source"],
                                     "verified project source", item["source_sha256"]))
        record = records[name]
        log_names = {value for value in [record.get("log"), *(attempt.get("log") for attempt in record.get("attempts", []))]
                     if isinstance(value, str)}
        if record.get("new_strict_compile") is True and not log_names:
            warnings.append({"module": name, "compile_log_missing_from_record": True})
        for value in sorted(log_names):
            try:
                path = local_path(root, value)
                common.add(evidence.add_path(path, "worktree/" + str(path.relative_to(root)),
                                             "actual persisted compile attempt log; attempts may include failures"))
            except (OSError, ValueError) as error:
                warnings.append({"module": name, "compile_log": value, "unavailable": str(error)})
    for driver_sha, path in drivers.items():
        label = DRIVER_FILES[driver_sha]
        common.add(evidence.add_path(path, "tooling/" + label, "exact historical audit driver", driver_sha))
    tooling = [Path(__file__), TEMPLATE, Path(__file__).with_name("run_winner9_private_checks.py"),
               Path(__file__).with_name("migrate_winner9_private_snapshot.py"),
               source_root / "docs/verification/20261124-p2-private/compile-driver-before-budget.py",
               source_root / "docs/verification/20261124-p2-private/compile-driver-budget-v2.py",
               Path(__file__).with_name("winner9_external_snapshot.py"),
               Path(__file__).with_name("inspect_winner9_owner_native.py")]
    for path in tooling:
        if path.is_file():
            expected = {"compile-driver-before-budget.py": COMPILE_BEFORE_BUDGET,
                        "compile-driver-budget-v2.py": COMPILE_BUDGET_V2}.get(path.name)
            common.add(evidence.add_path(path, "tooling/" + path.name, "verification implementation snapshot", expected))
        else:
            warnings.append({"tooling_file_missing": str(path)})
    external_metadata = {}
    for key in sorted(evidence.accepted_external_contexts):
        binding, external = evidence.external_contexts[key]
        prefix = "context/native/" + key + "/"
        snapshot_name = evidence.add_path(external.path, prefix + "snapshot.json", "qualified native environment inventory; no proof credit",
                                          binding["snapshot_sha256"])
        common.add(snapshot_name)
        texts = {}
        for value, item in external.files.items():
            path = Path(value)
            original_trace = path.suffix == ".trace" and item.get("role") == "original-trace"
            if (path.suffix not in TEXT_SUFFIXES and not original_trace) or ".olean" in path.suffixes:
                continue
            name = prefix + "files/" + hashlib.sha256(value.encode()).hexdigest() + "-" + path.name
            role = "qualified native source/provenance text; no independent proof credit"
            if original_trace:
                raw = path.read_bytes()
                require(sha_bytes(raw) == item["sha256"], "Evidence artifact changed: " + str(path))
                try:
                    json.loads(raw.decode("utf-8"))
                except (UnicodeDecodeError, json.JSONDecodeError) as error:
                    raise ValueError("Original trace must be UTF-8 JSON: " + str(path)) from error
                name += ".json"
                common.add(evidence.add_bytes(name, raw, str(path), role))
            else:
                common.add(evidence.add_path(path, name, role, item["sha256"]))
            texts[value] = name
        external_metadata[key] = {"binding": binding, "snapshot_archive": snapshot_name, "text_artifact_map": texts}
    # Supplemental receipts are retained for provenance, never used to award
    # accepted module/declaration/page counts. Skip proof object and isolated
    # native-cache directories; bound native files above and explicit extras
    # below retain their separate inclusion rules.
    supplements = [path for path in private.rglob("*") if path.is_file()
                   and path != private / "records.json"
                   and not {"audit", "lib", "exports", "native-cache"}.intersection(path.relative_to(private).parts)
                   and (path.suffix == ".json" or (path.suffix == ".log" and any(
                       word in str(path.relative_to(private)).lower() for word in ("bench", "probe", "stable", "migration"))))]
    for path in [*supplements, *args.extra_evidence]:
        paths = path.rglob("*") if path.is_dir() else [path]
        for item in paths:
            if not item.is_file() or item.suffix not in TEXT_SUFFIXES or ".olean" in item.suffixes:
                continue
            absolute = item.resolve()
            name = "worktree/" + str(absolute.relative_to(root)) if absolute.is_relative_to(root) else (
                "context/external/" + hashlib.sha256(str(absolute).encode()).hexdigest()[:12] + "-" + absolute.name)
            common.add(evidence.add_path(absolute, name, "supplemental provenance/benchmark/diagnostic context; no acceptance credit"))
    pages = {name: item["page_binding"] for name, item in accepted.items() if item["page_binding"] is not None}
    rows = {ordinal for item in pages.values() for ordinal in range(item["first_ordinal"], item["first_ordinal"] + item["row_count"])}
    duplicates = {name: modules for name, modules in owned_names.items() if len(modules) > 1}
    metadata = {
        "export_schema": 1, "created_utc": datetime.now(timezone.utc).isoformat(), "worktree": str(root),
        "accepted_module_count": len(accepted), "owned_declaration_count": sum(x["declaration_count"] for x in accepted.values()),
        "unique_owned_declaration_count": len(owned_names), "duplicate_owned_declarations": duplicates,
        "transitive_axiom_counts": dict(sorted(sum((Counter(item["axiom_counts"])
                                                   for item in accepted.values()), Counter()).items())),
        "accepted_modules": accepted, "unselected_modules": unselected, "rejected_candidates": rejected,
        "warnings": warnings, "full_p2_complete": False, "full_winner9_family_claimed": False,
        "coverage": {
            "geometry": {"expected": 93, "accepted": len(GEOMETRY & set(accepted)),
                         "complete": GEOMETRY <= set(accepted), "missing": sorted(GEOMETRY - set(accepted))},
            "definition_cores": {"expected": 11, "accepted": len(CORES & set(accepted)),
                                 "complete": CORES <= set(accepted), "missing": sorted(CORES - set(accepted))},
            "numerical_pages": {"expected_pages": 690, "accepted_bound_pages": len(pages), "covered_rows": len(rows),
                                "expected_rows": 11026, "bindings": pages,
                                "full_row_coverage": rows == set(range(11026))}},
        "object_manifest": project_union, "records_snapshot_sha256": sha_bytes(records_raw),
        "driver_sources": {sha: str(path) for sha, path in drivers.items()}, "no_olean_objects": True,
        "external_snapshots": external_metadata,
        "source_boundary": "Project source/object closure verified onsite; fixed Mathlib remains the locked environment boundary. Native dependencies, when used, additionally require the exact qualified external snapshot and physical input checks.",
        "acceptance_boundary": "Only selected valid accepted audit receipts are counted. Compiler-only, diagnostic, benchmark and migration records grant no additional audit or P2 credit.",
        "split": args.split, "transfer_page_bytes": args.transfer_page_bytes,
    }
    common.add(evidence.add_bytes("EXPORT_METADATA.json", encoded(metadata), "generated by this read-only exporter", "verified selection metadata"))
    groups: dict[str, set[str]] = defaultdict(set)
    group_modules: dict[str, list[str]] = defaultdict(list)
    if args.split == "all":
        groups["all"] = set(evidence.files)
        group_modules["all"] = sorted(accepted)
    else:
        groups["common"] = common
        for name, files in module_files.items():
            group = "audit-" + name if args.split == "module" else (
                "geometry" if name in GEOMETRY else "original-definitions" if name in CORES else
                "numerical-pages" if re.fullmatch(r"ImbalancedChen\.P2Winner9NumericalPage\d{4}", name) else "other-audits")
            groups[group].update(files)
            group_modules[group].append(name)
    evidence.verify_frozen()
    output.mkdir(parents=True)
    packages = [package(output / (group + ".tar.gz"), files, sorted(group_modules[group]), evidence,
                        args.transfer_page_bytes) for group, files in sorted(groups.items())]
    evidence.verify_frozen()
    manifest = dict(metadata, packages=packages, files=evidence.file_index())
    manifest_path = output / "manifest.json"
    manifest_path.write_bytes(encoded(manifest))
    print(json.dumps({"manifest": str(manifest_path), "manifest_bytes": manifest_path.stat().st_size,
                      "manifest_sha256": digest(manifest_path), "accepted_module_count": len(accepted),
                      "owned_declaration_count": metadata["owned_declaration_count"],
                      "geometry_complete": metadata["coverage"]["geometry"]["complete"],
                      "definition_cores_complete": metadata["coverage"]["definition_cores"]["complete"],
                      "numeric_rows": len(rows), "full_p2_complete": False, "packages": packages}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
