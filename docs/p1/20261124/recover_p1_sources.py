#!/usr/bin/env python3
"""Recover exact published P1 source selections without compiling or editing Git.

The frozen R03 selection is overlaid only by registered Member postimages.
The modern Fine-density manifest then supplies absent modules additively.
Every byte source is checked against its published SHA256 (and Git blob ID
when present). Same-named alternatives are reported, never substituted.

By default this writes inventories only. --stage writes the minimal two-root
closure and refuses incomplete graphs, missing exact bytes, cycles, or an
existing destination with different bytes. --blob-dir accepts independently
retrieved exact sources such as the two historical Nineteen-count blobs.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess

DEFAULT_REF = "228ee511f27ad2d12450b431ba5a1acdc0b5ac9d"
REGISTERED_SUCCESSOR_REF = "10b89181754c78c0e77616677295ee2105de0bb6"
R03 = "docs/source-only/20261123-winner9-prices-member/R03_SOURCE_SELECTION.json"
MEMBER = "docs/verification/20261123-blue-compilation/MEMBER_SOURCE_OVERRIDES.json"
DENSITY = "docs/source-only/20261112-resume/t01/density-validation-v2/DENSITY_MANIFEST.json"
FULL87 = "docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json"
DEFAULT_ROOTS = [
    "ImbalancedChen.P4AOriginalFiniteAll22Nineteen",
    "ImbalancedChen.P4AOriginalEarlyFinitePayment",
]


def identity(data: bytes) -> dict:
    return {
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
        "git_blob_sha1": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
    }


def checked(data: bytes, record: dict, label: str) -> bytes:
    got = identity(data)
    for key in ("sha256", "bytes", "git_blob_sha1"):
        if key in record and got[key] != record[key]:
            raise ValueError(f"{label}: expected {key}={record[key]}, got {got[key]}")
    if "sha256" not in record:
        raise ValueError(f"{label}: unpinned source has no SHA256")
    return data


def imports(data: bytes) -> list[str]:
    # Remove nested Lean block comments and line comments before scanning actual
    # import lines. Strings outside imports are irrelevant to this operation.
    source = data.decode("utf-8-sig")
    out, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        else:
            if not depth or source[i] == "\n":
                out.append(source[i] if not depth else "\n")
            i += 1
    result = []
    for line in "".join(out).splitlines():
        match = re.match(r"\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$", line)
        if match:
            for name in match.group(1).split():
                if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", name):
                    result.append(name)
                else:
                    raise ValueError(f"Unrecognized import syntax: {line}")
    return list(dict.fromkeys(result))


class Repository:
    def __init__(self, path: Path, ref: str, blob_dirs: list[Path]):
        self.path = path
        self.ref = subprocess.check_output(["git", "-C", str(path), "rev-parse", ref + "^{commit}"], text=True).strip()
        self.process = subprocess.Popen(["git", "-C", str(path), "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.cache = {}
        self.local = {}
        self.tree = {}
        self.by_module = defaultdict(list)
        raw = subprocess.check_output(["git", "-C", str(path), "ls-tree", "-rz", self.ref])
        for row in raw.split(b"\0"):
            if not row:
                continue
            info, name = row.split(b"\t", 1)
            mode, kind, blob = info.decode().split()
            name = name.decode()
            if kind == "blob":
                self.tree[name] = blob
                if name.endswith(".lean"):
                    suffix = name.split("ImbalancedChen/", 1)[-1]
                    module = "ImbalancedChen." + suffix[:-5].replace("/", ".")
                    if "ImbalancedChen/" not in name:
                        module = "ImbalancedChen." + Path(name).stem
                    self.by_module[module].append({"path": name, "git_blob_sha1": blob})
        for directory in blob_dirs:
            if directory.exists():
                for path in sorted(directory.rglob("*.lean")):
                    data = path.read_bytes()
                    self.local[identity(data)["sha256"]] = (data, str(path.resolve()))

    def get(self, spec: str) -> bytes | None:
        if spec in self.cache:
            return self.cache[spec]
        self.process.stdin.write(spec.encode() + b"\n")
        self.process.stdin.flush()
        header = self.process.stdout.readline().decode().strip().split()
        if len(header) == 2 and header[1] == "missing":
            self.cache[spec] = None
            return None
        if len(header) != 3 or header[1] != "blob":
            raise ValueError(f"Unexpected git cat-file response for {spec}: {header}")
        data = self.process.stdout.read(int(header[2]))
        assert self.process.stdout.read(1) == b"\n"
        self.cache[spec] = data
        return data

    def published(self, path: str) -> tuple[dict, dict]:
        data = self.get(self.ref + ":" + path)
        if data is None:
            raise ValueError(f"Missing published metadata: {path}")
        return json.loads(data), {"repository_path": path, "commit": self.ref, **identity(data)}

    def resolve(self, record: dict) -> tuple[bytes | None, dict]:
        sha = record["sha256"]
        if sha in self.local:
            data, path = self.local[sha]
            return checked(data, record, path), {"kind": "exact_local_blob", "path": path}
        blob = record.get("git_blob_sha1")
        if blob:
            data = self.get(blob)
            if data is not None:
                return checked(data, record, blob), {"kind": "git_blob", "git_blob_sha1": blob}
        origin = record.get("origin", {})
        if origin.get("kind") == "git" and not record.get("transform"):
            spec = origin["commit"] + ":" + origin["path"]
            data = self.get(spec)
            if data is not None:
                return checked(data, record, spec), {"kind": "git_origin", **origin}
        if record.get("repository_path"):
            spec = self.ref + ":" + record["repository_path"]
            data = self.get(spec)
            if data is not None:
                return checked(data, record, spec), {"kind": "published_postimage", "commit": self.ref, "path": record["repository_path"]}
        if record.get("transform"):
            pre = record["pre_input"]
            data, provenance = self.resolve(pre)
            if data is not None:
                for edit in record["transform"]:
                    old, new = edit["old"].encode(), edit["new"].encode()
                    if data.count(old) != edit["count"]:
                        raise ValueError("Literal transform site count changed: " + record["module"])
                    data = data.replace(old, new)
                return checked(data, record, record["module"]), {"kind": "published_exact_transform", "preimage_resolution": provenance, "transform": record["transform"]}
        return None, {"kind": "missing_exact_bytes", "origin": origin, "git_blob_sha1": blob}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--ref", default=DEFAULT_REF)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--blob-dir", action="append", default=[], type=Path)
    parser.add_argument("--root", action="append")
    parser.add_argument("--stage", type=Path)
    parser.add_argument("--stage-available", action="store_true", help="Explicitly allow a partial source-only stage; missing exact sources remain listed and acceptance is never implied.")
    args = parser.parse_args()
    repo = Repository(args.repo, args.ref, args.blob_dir)
    args.out.mkdir(parents=True, exist_ok=True)
    metadata = []
    r03, r03_id = repo.published(R03)
    member, member_id = repo.published(MEMBER)
    density, density_id = repo.published(DENSITY)
    full87, full87_id = repo.published(FULL87)
    metadata.extend([r03_id, member_id, density_id, full87_id])
    if member["base_source_selection"]["sha256"] != r03_id["sha256"]:
        raise ValueError("Member base R03 identity mismatch")
    old_member_raw = repo.get(DEFAULT_REF + ":" + MEMBER)
    if old_member_raw is None:
        raise ValueError("Missing frozen original Member registration for prefix verification")
    old_member = json.loads(old_member_raw)
    original_overrides = old_member["source_overrides"]
    current_overrides = member["source_overrides"]
    if current_overrides[:len(original_overrides)] != original_overrides:
        raise ValueError("The frozen original Member override prefix changed")
    if len({r["module"] for r in current_overrides}) != len(current_overrides):
        raise ValueError("Duplicate current Member source override")
    if {k: v for k, v in old_member.items() if k != "source_overrides"} != {k: v for k, v in member.items() if k != "source_overrides"}:
        raise ValueError("A non-append Member registration field changed")
    for path, current_id in ((R03, r03_id), (DENSITY, density_id), (FULL87, full87_id)):
        prior = repo.get(DEFAULT_REF + ":" + path)
        if prior is None or identity(prior)["sha256"] != current_id["sha256"]:
            raise ValueError("An inherited source-selection manifest changed: " + path)
    extra_overrides = current_overrides[len(original_overrides):]
    if repo.ref == REGISTERED_SUCCESSOR_REF:
        commit = subprocess.check_output(["git", "-C", str(repo.path), "cat-file", "commit", repo.ref], text=True)
        parents = [line.split()[1] for line in commit.split("\n\n", 1)[0].splitlines() if line.startswith("parent ")]
        if parents != [DEFAULT_REF]:
            raise ValueError("Registered successor has an unexpected commit parent")
        expected = ["ImbalancedChen.P1Pair12RetainedActualFifthPolicyBound", "ImbalancedChen.OriginalAscendingThirteenExportOwnershipJoin"]
        if [r["module"] for r in extra_overrides] != expected:
            raise ValueError("Registered successor did not append exactly the two independently accepted suppliers")
    extension_evidence = []
    evidence_prefix = "docs/verification/20261123-blue-compilation/"
    for entry in extra_overrides:
        module = entry["module"]
        selection_path = evidence_prefix + entry["module_source_record"]
        review_path = evidence_prefix + entry["independent_review"]
        batch = str(Path(selection_path).parent)
        source_registration, source_id = repo.published(selection_path)
        review, review_id = repo.published(review_path)
        validation, validation_id = repo.published(batch + "/VALIDATION_RESULTS.json")
        release, release_id = repo.published(batch + "/FINAL_RELEASE.json")
        metadata.extend([source_id, review_id, validation_id, release_id])
        registered = source_registration[module]
        if registered["preimage_sha256"] != entry["preimage"]["sha256"] or registered["postimage_sha256"] != entry["postimage"]["sha256"]:
            raise ValueError("New Member source registration fingerprint differs: " + module)
        if not review.get("status", "").startswith("PASS_") or review.get("findings"):
            raise ValueError("New Member source lacks a passing independent review: " + module)
        if validation.get("status") != "PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS" or validation["modules"].get(module) != entry["postimage"]["sha256"]:
            raise ValueError("New Member source lacks its exact recorded validation: " + module)
        for field in ("full_owned_including_private_generated", "only_standard_axioms", "pp_all_true_no_elisions", "source_plus_five_outputs_unchanged_across_kernel_and_audit"):
            if validation.get(field) is not True:
                raise ValueError("New Member validation acceptance field is false: " + field)
        if release.get("normal_kernel_audit_all_exit0") is not True or release.get("validation_results_sha256") != validation_id["sha256"]:
            raise ValueError("New Member final release does not bind exact passing validation")
        commands = validation["normal_commands"] + validation["kernel_commands"] + [validation["audit_command"]]
        log_ids = []
        for command in commands:
            if command.get("exit_code") != 0:
                raise ValueError("New Member normal/kernel/audit command did not exit zero")
            log_path = batch + "/" + command["log"]
            payload = repo.get(repo.ref + ":" + log_path)
            if payload is None or identity(payload)["sha256"] != command["log_sha256"]:
                raise ValueError("New Member actual validation log identity differs: " + log_path)
            log_ids.append({"repository_path": log_path, **identity(payload)})
        preimage, pre_resolution = repo.resolve(entry["preimage"])
        postimage, post_resolution = repo.resolve(entry["postimage"])
        if preimage is None or postimage is None or imports(preimage) != imports(postimage):
            raise ValueError("New Member exact pre/post sources unavailable or import topology changed: " + module)
        extension_evidence.append({"module": module, "preimage": identity(preimage), "postimage": identity(postimage), "imports_unchanged": True, "source_registration": source_id, "independent_review": review_id, "validation": validation_id, "final_release": release_id, "actual_exit_zero_log_identities": log_ids, "old_acceptance_evidence_reused_no_tests_repeated": True, "current_objects_reused_or_qualified": False})
    member_extension = {"original_ref": DEFAULT_REF, "selected_ref": repo.ref, "original_override_count": len(original_overrides), "selected_override_count": len(current_overrides), "frozen_original_prefix_unchanged": True, "other_member_fields_unchanged": True, "R03_Density_Full87_manifests_unchanged": True, "new_supplier_evidence": extension_evidence}
    selected, conflicts = {}, []
    for shard in r03["project_source_shards"]:
        content = repo.get(repo.ref + ":" + shard["repository_path"])
        checked(content, shard, shard["repository_path"])
        values = json.loads(content)
        if len(values) != shard["module_count"]:
            raise ValueError("R03 shard count differs")
        metadata.append({"commit": repo.ref, **shard})
        for module, record in values.items():
            if module in selected:
                raise ValueError("Duplicate R03 module " + module)
            selected[module] = {"module": module, "install_path": module.replace(".", "/") + ".lean", **record, "selection_layer": "R03", "selection_evidence": shard["repository_path"]}
    base_count = len(selected)
    if base_count != r03["project_count"]:
        raise ValueError("Unexpected published R03 inventory size")
    override_counts = {}
    for key in ("source_overrides", "existing_verified_supplier_overrides", "shared_project_source_overrides"):
        override_counts[key] = len(member.get(key, []))
        for entry in member.get(key, []):
            module = entry["module"]
            previous = selected.get(module)
            record = {"module": module, "install_path": module.replace(".", "/") + ".lean", **entry["postimage"], "selection_layer": "MEMBER_" + key, "selection_evidence": MEMBER, "registration": entry}
            if previous and previous["sha256"] != record["sha256"]:
                record["selected_predecessor_sha256"] = previous["sha256"]
            selected[module] = record
    density_modules = {entry["module"]: entry for entry in density["files"]}
    for module, record in density_modules.items():
        if module in selected:
            if selected[module]["sha256"] != record["sha256"]:
                conflicts.append({"module": module, "selected_sha256": selected[module]["sha256"], "selected_layer": selected[module]["selection_layer"], "density_sha256": record["sha256"], "resolution": "PROTECT_REGISTERED_MEMBER_CONTEXT_NO_SAME_NAME_REPLACEMENT", "requires_current_context_elaboration": True})
        else:
            selected[module] = {**record, "selection_layer": "DENSITY_ADDITIVE", "selection_evidence": DENSITY}
    available, missing_bytes, import_differences, selected_payloads = {}, [], [], {}
    for module, record in selected.items():
        data, resolution = repo.resolve(record)
        record["resolution"] = resolution
        record["exact_bytes_available"] = data is not None
        if data is None:
            missing_bytes.append({"module": module, "sha256": record["sha256"], "git_blob_sha1": record.get("git_blob_sha1"), "origin": record.get("origin"), "same_named_published_candidates_not_selected": repo.by_module.get(module, [])})
            record["imports_basis"] = "PUBLISHED_METADATA_ONLY_SOURCE_BYTES_MISSING"
            record.setdefault("imports", [])
        else:
            actual_imports = imports(data)
            declared = record.get("imports")
            if declared is not None and actual_imports != declared:
                import_differences.append({"module": module, "published_imports": declared, "actual_imports": actual_imports})
            record["imports"] = actual_imports
            record["imports_basis"] = "PARSED_EXACT_SOURCE_BYTES"
            record.update(identity(data))
            selected_payloads[module] = data
    roots = args.root or DEFAULT_ROOTS

    def closure(roots):
        seen, visiting, order, cycles, missing, external = set(), [], [], [], set(), set()
        def visit(module):
            if module in visiting:
                cycles.append(visiting[visiting.index(module):] + [module])
                return
            if module in seen:
                return
            if module not in selected:
                if module.startswith("ImbalancedChen."):
                    missing.add(module)
                else:
                    external.add(module)
                return
            visiting.append(module)
            for dependency in selected[module]["imports"]:
                visit(dependency)
            visiting.pop()
            seen.add(module)
            order.append(module)
        for module in roots:
            visit(module)
        return {"roots": roots, "module_count": len(seen), "topological_order": order, "missing_project_modules": sorted(missing), "cycles": cycles, "external_imports": sorted(external), "missing_exact_source_bytes": [row for row in missing_bytes if row["module"] in seen]}

    graph = closure(roots)
    graph["per_root"] = {root: closure([root]) for root in roots}
    graph["source_identity_sha256"] = hashlib.sha256(json.dumps([[m, selected[m]["sha256"]] for m in sorted(graph["topological_order"])], separators=(",", ":")).encode()).hexdigest()
    active = set(graph["topological_order"])
    graph["active_context_differences_from_density_manifest"] = [row for row in conflicts if row["module"] in active]
    def consumers(record):
        names = list(record.get("consumed_by", []))
        if record.get("consuming_module"):
            names.append(record["consuming_module"])
        return names
    graph["active_data_inputs"] = [row for row in density["data_inputs"] if active.intersection(consumers(row))]
    graph["data_inputs_without_explicit_consumer"] = [row for row in density["data_inputs"] if not consumers(row)]
    summary = {
        "schema": "p1_exact_published_source_recovery_v1",
        "frozen_commit": repo.ref,
        "compiled": False,
        "kernel_verified": False,
        "proof_credit": 0,
        "r03_sources": base_count,
        "member_override_counts": override_counts,
        "member_extension_verification": member_extension,
        "density_manifest_sources": len(density_modules),
        "full87_manifest_sources": len(full87["files"]),
        "selected_inventory_sources": len(selected),
        "exact_source_bytes_available": len(selected_payloads),
        "selected_inventory_missing_bytes": len(missing_bytes),
        "selected_layer_counts": dict(Counter(row["selection_layer"] for row in selected.values())),
        "target_closure_sources": graph["module_count"],
        "target_closure_missing_bytes": len(graph["missing_exact_source_bytes"]),
        "target_closure_missing_modules": graph["missing_project_modules"],
        "target_closure_cycles": graph["cycles"],
        "target_context_differences_from_density_manifest": len(graph["active_context_differences_from_density_manifest"]),
        "import_metadata_differences": len(import_differences),
        "source_identity_sha256": graph["source_identity_sha256"],
        "target_source_bytes": sum(selected[module].get("bytes", 0) for module in active),
        "target_data_input_count": len(graph["active_data_inputs"]),
        "target_data_input_bytes": sum(row["bytes"] for row in graph["active_data_inputs"]),
        "metadata_identities": metadata,
        "native_overlay_registration": member["native_source_overrides"],
        "external_dependency_toolchain": {key: density[key] for key in ("toolchain", "mathlib_rev", "native_rev")},
        "stage_status": "NOT_REQUESTED",
        "scope": "Exact published source selection only. Member postimages are protected; additive source compatibility still requires compilation. No object reuse or endpoint acceptance is inferred.",
    }
    if args.stage:
        incomplete = graph["missing_project_modules"] or graph["cycles"] or graph["missing_exact_source_bytes"]
        if incomplete and not args.stage_available:
            summary["stage_status"] = "BLOCKED_INCOMPLETE_EXACT_TARGET_CLOSURE"
        else:
            destinations = [(args.stage / selected[module]["install_path"], selected_payloads[module]) for module in graph["topological_order"] if module in selected_payloads]
            for path, data in destinations:
                if path.exists() and path.read_bytes() != data:
                    raise ValueError("Refusing to replace existing different source: " + str(path))
            for path, data in destinations:
                path.parent.mkdir(parents=True, exist_ok=True)
                if not path.exists():
                    path.write_bytes(data)
            summary["stage_status"] = "PARTIAL_EXACT_TARGET_PROJECT_SOURCES_WRITTEN_NO_DATA_OR_OBJECTS" if incomplete else "EXACT_TARGET_PROJECT_SOURCES_WRITTEN_NO_DATA_OR_OBJECTS"
            summary["stage_destination"] = str(args.stage.resolve())
            summary["staged_source_count"] = len(destinations)
    outputs = {
        "RECOVERY_SUMMARY.json": summary,
        "SELECTED_PROJECT_SOURCES.json": selected,
        "MINIMAL_TARGET_GRAPH.json": graph,
        "MISSING_EXACT_SOURCE_BYTES.json": missing_bytes,
        "MISSING_TARGET_EXACT_SOURCE_BYTES.json": graph["missing_exact_source_bytes"],
        "MINIMAL_TARGET_SELECTION.json": {module: selected[module] for module in graph["topological_order"]},
        "PROTECTED_SOURCE_CONTEXT_DIFFERENCES.json": conflicts,
        "IMPORT_METADATA_DIFFERENCES.json": import_differences,
        "REQUIRED_DATA_INPUTS.json": density["data_inputs"],
        "NATIVE_SOURCE_REQUIREMENTS.json": {"source_manifest": DENSITY, "native_sources": density["native_sources"], "member_native_overrides": member["native_source_overrides"]},
        "MEMBER_PREFIX_AND_EXTENSION_VERIFICATION.json": member_extension,
    }
    for name, value in outputs.items():
        (args.out / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({key: value for key, value in summary.items() if key not in ("metadata_identities", "member_extension_verification")}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
