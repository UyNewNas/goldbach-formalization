#!/usr/bin/env python3
"""Pure-Python, local source/transition verification; no Lean or subprocesses."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True

TRIM = "docs/p1/20261125/p15-original-atlas-trim"
PHASE1 = "docs/p1/20261125/p15-singleton-proper-power/SOURCE_CLOSURE.json"
PHASE2 = "docs/p1/20261125/p15-original-atlas-proper-power/SOURCE_CLOSURE.json"
NINE = "docs/p1/20261125/p15-existing-atlas-dependencies/ADOPTION_MANIFEST.json"
LAYERING = "docs/p1/20261125/p15-finite-lambda-source-layering/ADOPTION_MANIFEST.json"
REPAIRS = "docs/p1/20261125/p15-singleton-proper-power/FIRST_COMPILE_REPAIRS.json"
PURE_REPAIRS = "docs/p1/20261125/p15-original-atlas-proper-power/FIRST_COMPILE_REPAIRS.json"
SECOND_REPAIR = "docs/p1/20261125/p15-original-atlas-proper-power/SECOND_COMPILE_REPAIRS.json"
INITIAL153 = TRIM + "/snapshots/source153-before-first-compile/SOURCE_CLOSURE.json"
MELLIN = "ImbalancedChen.PrimeProductsMellinExactMeanInsertion"
CORE = "ImbalancedChen.Part3FiniteLambdaOverLogCore"
FINITE = "ImbalancedChen.Part3FiniteLambdaOverLogDictionary"
ALLK = "ImbalancedChen.Part3AllKLambdaChartCorrection"
POINTWISE = "ImbalancedChen.P1OriginalSingletonPointwiseData"
PROVIDER = "ImbalancedChen.P5OriginalSingletonLowerTrimPaid"
CONSUMER = "ImbalancedChen.P1OriginalSingletonAtlasTrim"

EXPECTED_INPUTS = {
    TRIM + "/PROVIDER_ADOPTION.json": "bed468318515ba54beadde83a5556c02beb7cbed5c684fb762ad74735ca27e36",
    TRIM + "/SOURCE_REVIEW.json": "928645e0e4ebf62985c32002ea4ea2d328aad18dcaf4e308edd6424db94ef790",
    TRIM + "/SOURCE_CLOSURE.json": "dba02193625caa25c2b3c34c5ea01ff52fc372d0cd64f5d070de7c2e686818ac",
    TRIM + "/DEPENDENCY_TRANSITION.json": "46208e7d33ea6f082dd34d4a9fe562646052a98768dfbaf0941057473799eeb2",
    TRIM + "/snapshots/initial-source371.json": "5b7008e59d0d64f6c046c47bcb9c6780fda91038a67c46a81abacaa3fd6a2d71",
    PHASE1: "a8b22d483e1a67649ce96b319d23cda447b6a2e134df7ccaf5bc2780643f1178",
    PHASE2: "c1dfff16bd8a758d47f14f5dfbed1ca3c836f657b525ed2afbefbf2605e182ad",
    SECOND_REPAIR: "8607ba1bc2f7e3d65d9172647beeb4e9f4292a3247e29b6d26dd338d4fc4c43d",
    PURE_REPAIRS: "9b66ab9d6a8813612f77bdd109a0159c4e46836b5ce3aea980ad3a30d7f3b5bd",
    INITIAL153: "c8a01bfd5b7d79e782188d8d77da572fe3bb37f749dbebcb03926a6e541a1e85",
    NINE: "120f73bd8c57d663d971b7ab1ac2c12dd6fb98ae939c902f014811b8c8ec8531",
    LAYERING: "f99008df8c39e1e722a042d0659cd434717262d9662296fe8f95b030f51219e5",
    REPAIRS: "617250ec7dfb19bfd892bea012bc08639993897c447253363b718b9af08116ff",
}


def require(value: bool, message: str) -> None:
    if not value:
        raise ValueError(message)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fingerprint(data: bytes) -> dict:
    return {"bytes": len(data), "sha256": sha(data),
            "git_blob": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()}


def check_pin(data: bytes, pin: dict, label: str) -> None:
    actual = fingerprint(data)
    for key in ("bytes", "sha256", "git_blob"):
        if key in pin:
            require(actual[key] == pin[key], label + ": " + key + " mismatch")


def strip_comments_and_strings(text: str) -> str:
    """Keep line boundaries while excluding nested Lean comments and strings."""
    output = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        char = text[i]
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                output.extend("  ")
                i += 2
            else:
                output.append("\n" if char == "\n" else " ")
                i += 1
        elif string:
            if char == "\\" and i + 1 < len(text):
                output.extend("\n" if value == "\n" else " " for value in text[i:i + 2])
                i += 2
            else:
                if char == '"':
                    string = False
                output.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            output.extend("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                output.extend(" " * (len(text) - i))
                i = len(text)
            else:
                output.extend(" " * (end - i))
                i = end
        elif char == '"':
            string = True
            output.append(" ")
            i += 1
        else:
            output.append(char)
            i += 1
    require(depth == 0 and not string, "unterminated comment/string in source")
    return "".join(output)


def imports(data: bytes) -> list[str]:
    result = []
    for line in strip_comments_and_strings(data.decode("utf-8")).splitlines():
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$", line)
        if match:
            names = match.group(1).split()
            require(all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name) for name in names), "unsupported import header")
            result.extend(names)
        else:
            require(not re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\b", line), "unparsed import header")
    return result


def source_path(module: str) -> str:
    require(re.fullmatch(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z0-9_']*)+", module) is not None, "invalid project module")
    return module.replace(".", "/") + ".lean"


def source_map_digest(rows: dict) -> str:
    data = {module: {key: row[key] for key in ("path", "sha256", "all_imports", "project_imports")}
            for module, row in sorted(rows.items())}
    return sha(json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode())


def main() -> None:
    require(sys.argv[1:] in ([], ["--write-receipt"]), "only --write-receipt is supported")
    here = Path(__file__).resolve().parent
    repo = here.parents[3]
    read_files = {}
    metadata_pins = {}

    def read(name: str) -> bytes:
        path = repo / name
        require(not Path(name).is_absolute() and path.resolve().is_relative_to(repo), "path escaped repository")
        if name not in read_files:
            read_files[name] = path.read_bytes()
        return read_files[name]

    def metadata(name: str, pin: dict | None = None) -> dict:
        data = read(name)
        if name in EXPECTED_INPUTS:
            require(sha(data) == EXPECTED_INPUTS[name], "frozen input changed: " + name)
        if pin:
            check_pin(data, pin, name)
        metadata_pins[name] = {"path": name, **fingerprint(data)}
        return json.loads(data)

    documents = {name: metadata(name) for name in EXPECTED_INPUTS}
    actual_current = documents[TRIM + "/SOURCE_CLOSURE.json"]
    # This immutable stage documents the earlier 371 -> 153 source layering.
    # The actual current graph is separately checked after the two explicit repairs.
    current = documents[INITIAL153]
    pure_repairs = documents[PURE_REPAIRS]
    require(pure_repairs['schema'] == 'p15_atlas_first_compile_source_repairs_v1' and
            pure_repairs['failed_source_commit'] == 'e1a80f6c306b58eadf2a8c6f58f4cbc7385e32d5' and
            [row['module'] for row in pure_repairs['files']] == [CORE, MELLIN],
            'first-compile two-owner repair scope differs')
    check_pin(read(PURE_REPAIRS), actual_current['first_compile_source_repairs'],
              'current first-compile repair binding')
    second_repair = documents[SECOND_REPAIR]
    require(second_repair['schema'] == 'p15_atlas_mellin_second_compile_source_repair_v1' and
            second_repair['failed_source_commit'] == 'ef450be0a89b6a3f88b3bca19d06e04e7967fa18' and
            [row['module'] for row in second_repair['files']] == [MELLIN] and
            second_repair['expected_project_source_count'] == 168 and
            second_repair['expected_other_identical_source_count'] == 167 and
            second_repair['accepted_owner_preserved'] == {
                'module': CORE, 'source_commit': 'ef450be0a89b6a3f88b3bca19d06e04e7967fa18',
                'no_recompile_requested': True}, 'second Mellin repair scope differs')
    check_pin(read(SECOND_REPAIR), actual_current['second_compile_source_repair'],
              'current second-compile repair binding')

    def undo_repair(actual, row, label):
        check_pin(actual, row['after'], label + ' source postimage')
        output, cursor, delta = bytearray(), 0, 0
        for splice in row['exact_byte_splices']:
            old, new = splice['old_utf8'].encode(), splice['new_utf8'].encode()
            lo, hi = splice['pre_start_byte'], splice['pre_end_byte']
            require(type(lo) is int and type(hi) is int and 0 <= lo < hi and
                    hi - lo == len(old), label + ' splice length differs')
            start = lo + delta
            require(start >= cursor and actual[start:start + len(new)] == new,
                    label + ' inverse splice differs')
            output.extend(actual[cursor:start]); output.extend(old)
            cursor = start + len(new); delta += len(new) - len(old)
        output.extend(actual[cursor:])
        preimage = bytes(output)
        check_pin(preimage, row['before'], label + ' reconstructed preimage')
        require(imports(preimage) == imports(actual), label + ' changed imports')
        return preimage

    second_row = second_repair['files'][0]
    after_first_mellin = undo_repair(read(second_row['path']), second_row, 'second Mellin repair')
    pure_preimages = {}
    expected_current = json.loads(json.dumps(current))
    for row in pure_repairs['files']:
        actual = after_first_mellin if row['module'] == MELLIN else read(row['path'])
        preimage = undo_repair(actual, row, 'first-compile repair')
        check_pin(preimage, current['project_sources'][row['module']], 'original153 repair preimage')
        pure_preimages[row['module']] = preimage
        expected_current['project_sources'][row['module']].update(row['after'])
    expected_current['first_compile_source_repairs'] = actual_current['first_compile_source_repairs']
    expected_current['project_sources'][MELLIN].update(second_row['after'])
    expected_current['second_compile_source_repair'] = actual_current['second_compile_source_repair']
    require(expected_current == actual_current,
            'current153 changed beyond first two repairs and second Mellin repair')
    original = documents[TRIM + "/snapshots/initial-source371.json"]
    transition = documents[TRIM + "/DEPENDENCY_TRANSITION.json"]
    provider = documents[TRIM + "/PROVIDER_ADOPTION.json"]
    review = documents[TRIM + "/SOURCE_REVIEW.json"]
    phase1, phase2 = documents[PHASE1], documents[PHASE2]
    nine, layering, repairs = documents[NINE], documents[LAYERING], documents[REPAIRS]
    check_pin(read(transition["original_closure"]["path"]), transition["original_closure"], "original371 transition pin")
    check_pin(read(current["source_layering_transition"]["path"]), current["source_layering_transition"], "current transition pin")
    require({pin["path"] for pin in transition["related_source_manifests"]} == {NINE, LAYERING, REPAIRS}, "transition owner manifests differ")
    for pin in transition["related_source_manifests"]:
        check_pin(read(pin["path"]), pin, "transition owner manifest")
    require(current["targets"] == original["targets"] == [PROVIDER, CONSUMER], "trim targets changed")
    for value in (actual_current, current, original, transition, provider, review):
        require(value["new_Lean_acceptance"] is False and value["whole_P1_5_complete"] is False, "acceptance boundary changed")
    require(provider["module"] == PROVIDER and provider["all_bytes_unchanged"] is True, "provider adoption scope changed")
    require(provider["new_arithmetic_proof"] is False and not review["static_findings"] and review["new_axioms"] is False, "original review boundary changed")
    archive = read(provider["source_path"])
    check_pin(archive, provider, "original provider archive")
    require(read(provider["destination_path"]) == archive, "provider is not original bytes")
    check_pin(read(review["source"]["path"]), review["source"], "reviewed trim consumer")
    require(review["source"]["path"] == source_path(CONSUMER), "reviewed consumer path differs")
    consumer_text = strip_comments_and_strings(read(review["source"]["path"]).decode())
    for name in review["public_terminals"]:
        require(re.search(r"^theorem\s+" + re.escape(name) + r"\b", consumer_text, re.M) is not None, "reviewed public terminal absent")

    old_rows, new_rows = original["project_sources"], current["project_sources"]
    old_set, new_set = set(old_rows), set(new_rows)
    retained = old_set & new_set
    changed = {module for module in retained if old_rows[module]["sha256"] != new_rows[module]["sha256"]}
    added, removed = new_set - old_set, old_set - new_set
    require(len(old_set) == original["project_module_count"] == transition["original_count"] == 371, "old371 count mismatch")
    require(len(new_set) == current["project_module_count"] == transition["current_count"] == 153, "current153 count mismatch")
    require(added == set(transition["added_to_active_closure"]) == {CORE}, "added source set mismatch")
    require(removed == set(transition["removed_from_active_closure"]) and len(removed) == 219, "removed source set mismatch")
    declared_changes = {row["module"]: row for row in transition["changed_retained_sources"]}
    require(changed == set(declared_changes) and len(changed) == 11, "changed retained source set mismatch")
    for module, row in declared_changes.items():
        require(row["before_sha256"] == old_rows[module]["sha256"] and row["after_sha256"] == new_rows[module]["sha256"], "transition source endpoint mismatch")

    historical_bytes = {MELLIN: pure_preimages[MELLIN]}
    ownership = {}
    for row in nine["modules"]:
        module = row["module"]
        require(module in changed and module not in ownership, "nine-source transition scope mismatch")
        before = read(row["before"]["snapshot_path"])
        check_pin(before, row["before"], "accepted-reuse preimage")
        after = read(row["after"]["source_repository_path"])
        check_pin(after, row["after"], "accepted-reuse postimage")
        require(read(row["canonical_path"]) == after, "accepted canonical postimage mismatch")
        historical_bytes[module] = before
        ownership[module] = {"kind": "existing_accepted_reindex_source_reuse", "manifest": NINE}
    require(len(ownership) == 9, "nine-source owner count mismatch")
    for module in (ALLK, FINITE):
        before_pin = layering["preimages"][module]
        after_pin = layering["postimages"][module]
        before = read(before_pin["snapshot_path"])
        check_pin(before, before_pin, "layering preimage")
        check_pin(read(after_pin["canonical_path"]), after_pin, "layering postimage")
        require(read(after_pin["canonical_path"]) == read(after_pin["snapshot_path"]), "layering snapshot mismatch")
        historical_bytes[module] = before
    ownership[ALLK] = {"kind": "original_AllK_import_only_source_layering", "manifest": LAYERING}
    pointwise_repair = next(row for row in repairs["files"] if row["module"] == POINTWISE)
    current_pointwise = read(pointwise_repair["path"])
    check_pin(current_pointwise, pointwise_repair["after"], "pointwise repair postimage")
    restored = bytearray()
    cursor = 0
    delta = 0
    for splice in sorted(pointwise_repair["exact_byte_splices"], key=lambda row: row["pre_start_byte"]):
        old, new = splice["old_utf8"].encode(), splice["new_utf8"].encode()
        require(len(old) == splice["pre_end_byte"] - splice["pre_start_byte"], "pointwise splice range mismatch")
        start = splice["pre_start_byte"] + delta
        require(start >= cursor and current_pointwise[start:start + len(new)] == new, "pointwise inverse splice mismatch")
        restored.extend(current_pointwise[cursor:start])
        restored.extend(old)
        cursor = start + len(new)
        delta += len(new) - len(old)
    restored.extend(current_pointwise[cursor:])
    historical_bytes[POINTWISE] = bytes(restored)
    check_pin(historical_bytes[POINTWISE], pointwise_repair["before"], "restored pointwise preimage")
    ownership[POINTWISE] = {"kind": "first_compile_exact_source_syntax_repair", "manifest": REPAIRS,
                            "preimage_method": "in-memory inverse of the recorded exact byte splices"}
    require(set(ownership) == changed, "not all11 retained changes have one explicit owner")
    core_pin = layering["postimages"][CORE]
    check_pin(pure_preimages[CORE], core_pin, "original added Core before first compilation")
    require(imports(read(core_pin["canonical_path"])) == ["Mathlib"], "Core import boundary changed")

    def validate_rows(rows: dict, historic: bool = False) -> dict:
        result = {}
        for module, row in rows.items():
            require(row["path"] == source_path(module), "module/path mismatch")
            data = historical_bytes[module] if historic and module in historical_bytes else read(row["path"])
            check_pin(data, row, ("historical " if historic else "current ") + module)
            all_imports = imports(data)
            project_imports = [name for name in all_imports if name.startswith("ImbalancedChen.")]
            require(row["imports"] == project_imports, "recorded project imports mismatch: " + module)
            if "project_imports" in row:
                require(row["project_imports"] == project_imports, "project_imports mismatch: " + module)
            if "all_imports" in row:
                require(row["all_imports"] == all_imports, "all_imports mismatch: " + module)
            result[module] = {"path": row["path"], **fingerprint(data),
                              "all_imports": all_imports, "project_imports": project_imports}
        return result

    def closure(roots: list[str], rows: dict) -> set[str]:
        visited, visiting = set(), set()
        def visit(module: str) -> None:
            require(module in rows, "missing project dependency: " + module)
            require(module not in visiting, "project import cycle: " + module)
            if module in visited:
                return
            visiting.add(module)
            for dependency in rows[module]["project_imports"]:
                visit(dependency)
            visiting.remove(module)
            visited.add(module)
        for root in roots:
            visit(root)
        return visited

    old_verified = validate_rows(old_rows, historic=True)
    trim_verified = validate_rows(actual_current["project_sources"])
    require(closure(original["targets"], old_verified) == old_set, "original371 contains unreachable/missing sources")
    require(closure(current["targets"], trim_verified) == new_set, "current153 contains unreachable/missing sources")
    require(not current["missing"] and not current["cycles"] and not original["missing"] and not original["cycles"], "recorded graph failure")
    for row in transition["retained_owner_sources_unchanged"]:
        module = row["path"][:-5].replace("/", ".")
        require(module in {PROVIDER, CONSUMER}, "unexpected retained trim owner")
        check_pin(read(row["path"]), row, "unchanged trim owner")
        require(old_rows[module]["sha256"] == new_rows[module]["sha256"] == row["sha256"], "trim owner changed")
    require(len(transition["retained_owner_sources_unchanged"]) == 2, "trim owner count mismatch")
    changed_imports = {module for module in retained if old_verified[module]["all_imports"] != trim_verified[module]["all_imports"]}
    require(changed_imports == {ALLK}, "unexpected retained import change")
    replacement = layering["allk_import_replacement"]
    require(read(source_path(ALLK)) == historical_bytes[ALLK].replace(replacement["before"].encode(), replacement["after"].encode(), 1), "AllK change exceeds its recorded import replacement")

    graph_pin = layering["static_graph_review"]
    layering_graph = metadata(graph_pin["repository_path"], graph_pin)
    require(removed == set(layering_graph["removed_from_active_closure"]), "219 removals not exactly explained by source layering")
    removed_rows = []
    changed_removed = []
    for module in sorted(removed):
        data = read(source_path(module))
        before_sha = old_rows[module]["sha256"]
        after_sha = sha(data)
        if before_sha != after_sha:
            require(module == FINITE, "unattributed off-closure canonical change")
            check_pin(data, layering["postimages"][FINITE], "off-closure Finite complement")
            changed_removed.append(module)
        removed_rows.append({"module": module, "before_sha256": before_sha,
                             "current_canonical_sha256": after_sha, "file_still_exists": True,
                             "transition_owner_manifest": LAYERING,
                             "classification": "preserved_full_provider_complement" if module == FINITE else "source_unchanged_outside_active_closure"})
    require(changed_removed == [FINITE], "off-closure change set mismatch")

    phase1_verified = validate_rows(phase1["project_sources"])
    phase2_verified = validate_rows(phase2["project_sources"])
    require(len(phase1_verified) == 316 and len(phase1["targets"]) == 6, "phase1 scope mismatch")
    require(len(phase2_verified) == 168 and phase2["targets"] == layering["next_stage_handoff"]["targets"] and len(phase2["targets"]) == 6, "current six-owner phase2 scope mismatch")
    require(closure(phase1["targets"], phase1_verified) == set(phase1_verified), "phase1 closure mismatch")
    require(closure(phase2["targets"], phase2_verified) == set(phase2_verified), "phase2 closure mismatch")
    combined = {}
    for rows in (phase1_verified, phase2_verified, trim_verified):
        for module, row in rows.items():
            if module in combined:
                require(combined[module] == row, "cross-stage source/import mismatch")
            combined[module] = row
    base_union = set(phase1_verified) | set(phase2_verified)
    additional = sorted(new_set - base_union)
    require(len(base_union) == 349 and len(combined) == current["phase1_phase2_trim_union_count"] == 356, "union356 count mismatch")
    require(additional == current["additional_to_phase1_phase2_union"] and len(additional) == 7, "additional7 mismatch")
    all_roots = list(dict.fromkeys(phase1["targets"] + phase2["targets"] + current["targets"]))
    require(closure(all_roots, combined) == set(combined), "combined union is not an exact closure")

    for name, data in read_files.items():
        require((repo / name).read_bytes() == data, "input changed during read-only verification: " + name)
    actual_changed = {m for m in retained if old_rows[m]["sha256"] != trim_verified[m]["sha256"]}
    require(actual_changed == changed | {MELLIN}, "unexpected current retained repair set")
    receipt = {
        "schema": "p15_original_atlas_trim_current_sources_static_receipt_v3",
        "status": "PASS_SOURCE_IDENTITY_IMPORT_GRAPHS_AND_EXPLICIT_TRANSITION_NOT_LEAN_ACCEPTANCE",
        "verified_utc": datetime.now(timezone.utc).isoformat(),
        "verifier": {"path": TRIM + "/verify_current_sources.py", **fingerprint(Path(__file__).read_bytes())},
        "input_metadata": [metadata_pins[name] for name in sorted(metadata_pins)],
        "provider_adoption": {"module": PROVIDER, "canonical_equals_original_archive": True,
                              "source_context_commit_from_pinned_adoption": provider["source_context_commit"],
                              "source_pin": fingerprint(archive)},
        "independent_source_review_binding": {"reviewer": review["reviewer"], "source": review["source"],
                                              "public_terminals": review["public_terminals"],
                                              "manuscript_pin_retained_from_review": review["manuscript"],
                                              "manuscript_reread_or_proof_review_repeated": False},
        "counts": {"original_trim": 371, "current_trim": 153, "retained": len(retained),
                   "unchanged_retained": len(retained) - len(actual_changed), "changed_retained": len(actual_changed),
                   "source_layering_changed_retained": len(changed), "first_compile_repairs": 2, "second_compile_repairs": 1,
                   "added": len(added), "removed_from_active_closure": len(removed),
                   "removed_files_still_present": len(removed_rows), "phase1": 316, "phase2": 168,
                   "phase2_selected_owners": 6, "phase1_phase2_union": 349, "phase1_phase2_trim_union": 356,
                   "trim_additional_to_union": 7},
        "source_map_digest_encoding": "SHA256 of UTF-8 compact sorted-key JSON mapping each module to path, SHA256, all_imports and project_imports.",
        "source_map_sha256": {"original_trim": source_map_digest(old_verified),
                              "current_trim": source_map_digest(trim_verified),
                              "phase1": source_map_digest(phase1_verified),
                              "phase2": source_map_digest(phase2_verified),
                              "combined_union": source_map_digest(combined)},
        "source_layering_changed_retained_sources": [{**declared_changes[module], **ownership[module]} for module in sorted(changed)],
        "first_compile_source_repairs": {"manifest": metadata_pins[PURE_REPAIRS],
            "failed_source_commit": pure_repairs["failed_source_commit"],
            "exact_inverse_splices_verified": True, "modules": [CORE, MELLIN],
            "initial153_snapshot": metadata_pins[INITIAL153]},
        "second_compile_source_repair": {"manifest": metadata_pins[SECOND_REPAIR],
            "failed_source_commit": second_repair["failed_source_commit"],
            "exact_inverse_splice_verified": True, "modules": [MELLIN],
            "accepted_Core_source_unchanged": True, "accepted_Core_recompiled": False},
        "added_sources": [{"module": CORE, "owner_manifest": LAYERING, "subsequent_repairs_manifest": PURE_REPAIRS, "source": trim_verified[CORE]}],
        "removed_sources": removed_rows,
        "only_changed_removed_canonical_source": FINITE,
        "only_changed_retained_import_owner": ALLK,
        "additional7": [{"module": module, **combined[module]} for module in additional],
        "current_targets": {"phase1": phase1["targets"], "phase2": phase2["targets"], "trim": current["targets"]},
        "missing_project_sources": [], "cycles": [], "source_or_input_mutation_during_check": False,
        "original371_before_bytes_reconstructed_and_imports_checked": True,
        "new_Lean_acceptance": False, "Lean_Lake_kernel_invocations": 0, "cloud_queries": 0,
        "subprocesses": 0, "cache_reads_or_writes": 0, "whole_P1_5_complete": False,
        "limits": ["Source bytes, recorded provenance and import reachability only; no elaboration, kernel, all-owned audit or runtime readiness claim.",
                   "Leaving this active source closure does not remove canonical files or imply absence of independent accepted work.",
                   "The original manuscript and mathematical proof review are bound through the unchanged SOURCE_REVIEW metadata, not repeated here."],
    }
    receipt_bytes = (json.dumps(receipt, ensure_ascii=False, indent=2) + "\n").encode()
    if sys.argv[1:] == ["--write-receipt"]:
        with (here / "CURRENT_STATIC_RECEIPT.json").open("xb") as stream:
            stream.write(receipt_bytes)
    print(json.dumps({"status": receipt["status"], "counts": receipt["counts"],
                      "source_map_sha256": receipt["source_map_sha256"], "new_Lean_acceptance": False,
                      "receipt_written": bool(sys.argv[1:]),
                      "receipt_sha256": sha(receipt_bytes) if sys.argv[1:] else None},
                     ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (KeyError, ValueError, OSError, UnicodeError, StopIteration) as error:
        print(json.dumps({"status": "HOLD", "reason": str(error)}, ensure_ascii=False), file=sys.stderr)
        raise SystemExit(1)
