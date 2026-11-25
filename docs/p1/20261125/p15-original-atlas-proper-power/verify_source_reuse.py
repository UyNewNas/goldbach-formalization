#!/usr/bin/env python3
"""Verify the six-owner source revision; never run Lean or mutate source/cache.

Without arguments, print the check result. --write-receipt also writes only
CURRENT_STATIC_VERIFICATION.json beside this script. Historical receipts,
reviewed hashes, source originals, migration postimages and caches are read only.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
PHASE1 = ROOT / "docs/p1/20261125/p15-singleton-proper-power"
LEGACY_ROOTS = [
    "ImbalancedChen.PrimeProductsMellinExactMeanInsertion",
    "ImbalancedChen.P5IndependentPrimeSourceWordDictionary",
    "ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy",
    "ImbalancedChen.P1OriginalSingletonSmoothLicence",
    "ImbalancedChen.P1OriginalSingletonAtlasProperPower",
]
CORE = "ImbalancedChen.Part3FiniteLambdaOverLogCore"
EXPECTED_ROOTS = [CORE] + LEGACY_ROOTS
FINGERPRINT_KEYS = ("path", "bytes", "sha256", "git_blob")
INSTALLER = "docs/p1/20261125/p15-singleton-proper-power/install_sources.py"
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe)\b")


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def fingerprint(raw, path):
    return {"path": path, "bytes": len(raw), "sha256": sha(raw),
            "git_blob": hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()}


def file_fingerprint(path):
    return fingerprint((ROOT / path).read_bytes(), path)


def load(name):
    return json.loads((HERE / name).read_bytes())


def check_fingerprint(row, raw=None):
    if raw is None:
        raw = (ROOT / row["path"]).read_bytes()
    actual = fingerprint(raw, row["path"])
    for key in FINGERPRINT_KEYS:
        if key in row:
            need(actual[key] == row[key], f"fingerprint differs: {row['path']} {key}")
    return raw


def git_bytes(ref):
    return subprocess.check_output(["git", "cat-file", "blob", ref], cwd=ROOT)


def check_original(row):
    raw = check_fingerprint(row)
    need(git_bytes(row["git_blob"]) == raw, "origin Git blob differs: " + row["path"])
    commit = row.get("available_at_commit", row.get("source_commit"))
    if commit:
        need(git_bytes(commit + ":" + row["path"]) == raw,
             "origin commit/path differs: " + row["path"])
    return raw


def remove_intervals(raw, intervals):
    ordered = sorted(intervals)
    last = 0
    for lo, hi in ordered:
        need(last <= lo < hi <= len(raw), "overlapping or invalid declaration intervals")
        last = hi
    for lo, hi in reversed(ordered):
        raw = raw[:lo] + raw[hi:]
    return raw


def declaration_bytes(raw, row):
    lo, hi = row["source_start_byte"], row["source_end_byte"]
    need(0 <= lo < hi <= len(raw), "invalid declaration interval: " + row["name"])
    body = raw[lo:hi]
    need(len(body) == row["bytes"] and sha(body) == row["sha256"],
         "declaration bytes differ: " + row["name"])
    return body


def lean_code(text):
    """Erase nested comments and string literals, preserving line boundaries."""
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0:
                i = len(text)
        elif text.startswith("/-", i):
            i += 2
            depth = 1
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            need(depth == 0, "unclosed Lean comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("unclosed Lean string")
        else:
            i += 1
            continue
        for j in range(start, i):
            if out[j] not in "\r\n":
                out[j] = " "
    return "".join(out)


def import_list(raw):
    code = lean_code(raw.decode("utf-8"))
    return [word for line in re.findall(r"^import[ \t]+([^\n\r]+)", code, re.M)
            for word in line.split()]


def reachable(graph, roots):
    done, active = set(), set()
    def visit(module):
        need(module in graph, "missing import in manifest: " + module)
        need(module not in active, "project import cycle at " + module)
        if module in done:
            return
        active.add(module)
        for child in graph[module]:
            visit(child)
        active.remove(module)
        done.add(module)
    for module in roots:
        visit(module)
    return done


def second_compile_owner_repair(closure):
    """Reconstruct the first correction epoch from the one later Mellin splice."""
    binding = closure["second_compile_repairs"]
    repair = json.loads(check_fingerprint(binding))
    failed = "ef450be0a89b6a3f88b3bca19d06e04e7967fa18"
    module = LEGACY_ROOTS[0]
    path = module.replace(".", "/") + ".lean"
    need(repair["schema"] == "p15_atlas_mellin_second_compile_source_repair_v1" and
         repair["failed_source_commit"] == failed and
         repair["expected_project_source_count"] == 168 and
         repair["expected_other_identical_source_count"] == 167 and
         not repair["new_acceptance_claimed"] and not repair["whole_P1_5_complete"] and
         [r["module"] for r in repair["files"]] == [module], "second correction epoch scope differs")
    preserved = repair["accepted_owner_preserved"]
    need(preserved == {"module": CORE, "source_commit": failed, "no_recompile_requested": True},
         "preserved Core source identity or no-recompile scope differs")
    expected_history = {(HERE / name).relative_to(ROOT).as_posix() for name in [
        "FIRST_COMPILE_REPAIRS.json", "ADOPTION_MANIFEST.json", "SOURCE_REVIEW.json",
        "SMOOTH_EXTRACTION.json", "SOURCE_LAYERING_REVISION.json"]} | {
        CORE.replace(".", "/") + ".lean"}
    need({r["path"] for r in repair["unchanged_historical_bindings"]} == expected_history and
         len(repair["unchanged_historical_bindings"]) == 6, "second-epoch historical pin selection differs")
    for pin in repair["unchanged_historical_bindings"] + [repair["unchanged_driver"],
                                                        repair["unchanged_additive_installer"]]:
        need(check_fingerprint(pin) == git_bytes(failed + ":" + pin["path"]),
             "second repair changed an earlier binding or accepted Core source")
    old_raw = git_bytes(failed + ":" + repair["failed_source_closure"]["path"])
    check_fingerprint(repair["failed_source_closure"], old_raw)
    old = json.loads(old_raw)
    row = repair["files"][0]
    need(row["path"] == path and len(row["exact_byte_splices"]) == len(row["replacements"]) == 1,
         "second repair file or splice selection differs")
    before = git_bytes(failed + ":" + path)
    check_fingerprint({"path": path, **row["before"]}, before)
    after = check_fingerprint({"path": path, **row["after"]})
    splice = row["exact_byte_splices"][0]
    lo, hi = splice["pre_start_byte"], splice["pre_end_byte"]
    need(0 <= lo < hi <= len(before) and before[lo:hi] == splice["old_utf8"].encode() and
         before.count(splice["old_utf8"].encode()) == 1 and
         row["replacements"] == [{"old_utf8": splice["old_utf8"],
                                   "new_utf8": splice["new_utf8"], "count": 1}] and
         after == before[:lo] + splice["new_utf8"].encode() + before[hi:],
         "second Mellin expression repair differs outside its exact splice")
    def headers(raw):
        return [raw[m.start():raw.index(b":=", m.start())]
                for m in re.finditer(rb"^(?:def|theorem|lemma|abbrev)\s+", raw, re.M)]
    need(len(headers(before)) == 11 and headers(before) == headers(after) and
         import_list(before) == import_list(after) == ["Mathlib"],
         "second repair changes a Mellin declaration header or import")
    diagnosis = row["diagnosis"]
    need(diagnosis["classification"] == "PINNED_MATHLIB_TYPECLASS_INSTANCE_EXPRESSION_REPAIR" and
         not diagnosis["public_statements_or_imports_changed"] and not diagnosis["new_mathematical_assumption"] and
         diagnosis["normal_exit_code"] == 1 and diagnosis["actual_built_modules"] == [] and
         diagnosis["actual_failed_modules"] == [module], "second repair diagnosis scope differs")
    expected_row = copy.deepcopy(old["project_sources"][module])
    check_fingerprint(expected_row, before)
    expected_row.update(fingerprint(after, path))
    need(closure["project_sources"][module] == expected_row and
         len(closure["project_sources"]) == 168, "second-epoch changed closure row differs")
    restored = copy.deepcopy(closure)
    restored.pop("second_compile_repairs")
    restored["project_sources"][module] = old["project_sources"][module]
    need((json.dumps(restored, ensure_ascii=False, indent=2) + "\n").encode() == old_raw,
         "published first-epoch whole closure cannot be exactly reconstructed")
    receipt_path = (HERE / "CURRENT_STATIC_VERIFICATION.json").relative_to(ROOT).as_posix()
    first_receipt_raw = git_bytes(failed + ":" + receipt_path)
    first_receipt = json.loads(first_receipt_raw)
    need(first_receipt["status"] == "PASS_CURRENT_SIX_OWNER_EXACT_FIRST_COMPILE_REPAIRS_AND_SOURCE_GRAPH_ONLY" and
         first_receipt["current_active_source_modules"] == 168 and
         repair["failed_source_closure"] in first_receipt["inputs"],
         "published first-epoch static receipt differs")
    return old, {path: before}, {
        "manifest": binding, "failed_source_commit": failed,
        "published_first_epoch_closure": repair["failed_source_closure"],
        "published_first_epoch_static_receipt": {"source_commit": failed,
                                                  **fingerprint(first_receipt_raw, receipt_path)},
        "repaired_owner": module, "exact_splice_count": 1,
        "other_source_rows_identical": 167, "declaration_headers_byte_identical": 11,
        "literal_imports_unchanged": True, "first_epoch_source_closure_exactly_reconstructed": True,
        "preserved_Core_source_and_no_recompile_binding": preserved,
        "Core_acceptance_reverified_here": False,
        "old_new_elaborated_type_equivalence_proved": False, "Lean_acceptance_claimed": False,
    }


def first_compile_owner_repairs(closure, current_source_overrides=None):
    """Bind current owners to exact repairs of the published, preserved source stage."""
    failed = "e1a80f6c306b58eadf2a8c6f58f4cbc7385e32d5"
    binding = closure["first_compile_repairs"]
    repair = json.loads(check_fingerprint(binding))
    expected = {CORE: 2, LEGACY_ROOTS[0]: 3}
    need(repair["schema"] == "p15_atlas_first_compile_source_repairs_v1" and
         repair["failed_source_commit"] == failed and
         repair["expected_project_source_count"] == 168 and
         repair["expected_other_identical_source_count"] == 166 and
         not repair["Lean_acceptance_claimed"] and not repair["whole_P1_5_complete"],
         "current two-owner repair scope differs")
    need([r["module"] for r in repair["files"]] == list(expected),
         "current repaired-owner selection differs")
    old_raw = git_bytes(failed + ":" + repair["failed_source_closure"]["path"])
    check_fingerprint(repair["failed_source_closure"], old_raw)
    old = json.loads(old_raw)
    need(set(old["project_sources"]) == set(closure["project_sources"]) and
         len(old["project_sources"]) == 168, "first-compile import closure selection changed")
    historical_paths = {
        (HERE / name).relative_to(ROOT).as_posix()
        for name in ["ADOPTION_MANIFEST.json", "SOURCE_REVIEW.json", "SMOOTH_EXTRACTION.json",
                     "SOURCE_LAYERING_REVISION.json"]
    } | {"docs/p1/20261125/p15-finite-lambda-source-layering/" + name
         for name in ["ADOPTION_MANIFEST.json", "STATIC_GRAPH_REVIEW.json"]}
    need({r["path"] for r in repair["unchanged_historical_bindings"]} == historical_paths and
         len(repair["unchanged_historical_bindings"]) == 6,
         "historical repair binding selection differs")
    for row in repair["unchanged_historical_bindings"] + [repair["unchanged_driver"],
                                                        repair["unchanged_additive_installer"]]:
        need(check_fingerprint(row) == git_bytes(failed + ":" + row["path"]),
             "published historical record or entrypoint changed")
    for name in ["adopt_current_sources.py", "SOURCE_DEPLOYMENT.json"]:
        path = (HERE / name).relative_to(ROOT).as_posix()
        need((ROOT / path).read_bytes() == git_bytes(failed + ":" + path),
             "initial source deployment entrypoint or binding changed")

    baseline_path = HERE / "snapshots/source168-before-first-compile/SNAPSHOT.json"
    baseline = json.loads(baseline_path.read_bytes())
    expected_snapshot_paths = {
        (HERE / name).relative_to(ROOT).as_posix()
        for name in ["SOURCE_CLOSURE.json", "CURRENT_STATIC_VERIFICATION.json",
                     "verify_source_reuse.py", "README.md"]
    } | {module.replace(".", "/") + ".lean" for module in expected}
    need(baseline["schema"] == "p15_atlas_initial_six_owner_first_compile_baseline_v1" and
         baseline["source_commit"] == failed and not baseline["Lean_acceptance_claimed"] and
         {r["source"]["path"] for r in baseline["files"]} == expected_snapshot_paths and
         len(baseline["files"]) == 6, "initial168 snapshot scope differs")
    for row in baseline["files"]:
        raw = check_fingerprint(row["snapshot"])
        check_fingerprint(row["source"], raw)
        need(raw == git_bytes(failed + ":" + row["source"]["path"]),
             "initial168 snapshot differs from its published source")

    originals = {}
    header_counts = {}
    reconstructed = copy.deepcopy(closure)
    reconstructed.pop("first_compile_repairs")
    for row in repair["files"]:
        module, path = row["module"], row["path"]
        need(path == module.replace(".", "/") + ".lean" and
             len(row["exact_byte_splices"]) == expected[module], "repair path/splice count differs")
        original = git_bytes(failed + ":" + path)
        check_fingerprint({"path": path, **row["before"]}, original)
        current = check_fingerprint({"path": path, **row["after"]},
                                    (current_source_overrides or {}).get(path))
        parts, previous = [], 0
        for splice, replacement in zip(row["exact_byte_splices"], row["replacements"]):
            lo, hi = splice["pre_start_byte"], splice["pre_end_byte"]
            old_part, new_part = splice["old_utf8"].encode(), splice["new_utf8"].encode()
            need(previous <= lo < hi <= len(original) and original[lo:hi] == old_part,
                 "current owner exact splice interval differs")
            need(replacement == {"old_utf8": splice["old_utf8"],
                                 "new_utf8": splice["new_utf8"], "count": 1} and
                 original.count(old_part) == 1, "current owner replacement multiplicity differs")
            parts.extend([original[previous:lo], new_part])
            previous = hi
        need(len(row["replacements"]) == expected[module], "repair replacement count differs")
        parts.append(original[previous:])
        need(current == b"".join(parts), "current owner differs outside the explicit proof repairs")
        need(import_list(original) == import_list(current) == ["Mathlib"],
             "current pure-owner import list changed")
        # These two owners have only ordinary def/theorem headers. This is a
        # lexical statement check, never an elaborated-type-equivalence claim.
        def headers(raw):
            starts = list(re.finditer(rb"^(?:def|theorem|lemma|abbrev)\s+", raw, re.M))
            result = []
            for index, start in enumerate(starts):
                end = starts[index + 1].start() if index + 1 < len(starts) else len(raw)
                assignment = raw.find(b":=", start.start(), end)
                need(assignment >= 0, "unrecognized repaired-owner declaration header")
                result.append(raw[start.start():assignment])
            return result
        before_headers, after_headers = headers(original), headers(current)
        need(before_headers == after_headers and
             len(before_headers) == (9 if module == CORE else 11),
             "current repair changed a declaration header")
        header_counts[module] = len(before_headers)
        diagnosis = row["diagnosis"]
        need(diagnosis["classification"] == "FORMAL_EXPRESSION_REPAIR" and
             diagnosis["normal_exit_code"] == 1 and diagnosis["actual_built_modules"] == [] and
             diagnosis["actual_failed_modules"] == [module] and
             not diagnosis["new_mathematical_assumptions"] and
             not diagnosis["theorem_statements_changed"] and not diagnosis["imports_changed"],
             "first-compile failure/repair scope differs")
        expected_row = copy.deepcopy(old["project_sources"][module])
        check_fingerprint(expected_row, original)
        expected_row.update(fingerprint(current, path))
        need(closure["project_sources"][module] == expected_row,
             "current repaired-owner closure row differs outside its fingerprint")
        reconstructed["project_sources"][module] = old["project_sources"][module]
        originals[path] = original
    restored = (json.dumps(reconstructed, ensure_ascii=False, indent=2) + "\n").encode()
    need(restored == old_raw, "initial168 source closure not exactly reconstructed")
    report = {
        "manifest": binding, "failed_source_commit": failed,
        "initial_source_closure": repair["failed_source_closure"],
        "preserved_initial168_snapshot": file_fingerprint(baseline_path.relative_to(ROOT).as_posix()),
        "repaired_owners": list(expected), "exact_splice_count": sum(expected.values()),
        "other_source_rows_identical": 166, "declaration_headers_byte_identical": header_counts,
        "literal_imports_unchanged": True, "old_new_elaborated_type_equivalence_proved": False,
        "initial168_source_closure_exactly_reconstructed": True,
        "historical_bindings_and_entrypoints_unchanged": True,
        "source_values_from_verified_second_epoch_preimage": sorted(current_source_overrides or {}),
        "Lean_acceptance_claimed": False,
    }
    return originals, old_raw, report


def dependency_updates(adoption, closure, exceptions, historical_execution=None, owner_originals=None):
    """Check exact external source changes without claiming type equivalence."""
    binding = adoption["external_dependency_updates"]
    need(binding == closure["external_dependency_updates"] ==
         exceptions["dependency_source_updates"], "dependency-update binding differs")
    updates = json.loads(check_fingerprint(binding))
    baseline = json.loads(check_fingerprint(updates["prior_binding_snapshot"]))
    protected_hash = sha(json.dumps(adoption["protected_inputs"], sort_keys=True,
                                    separators=(",", ":")).encode())
    need(protected_hash == baseline["protected_input_bindings_sha256"],
         "original29 protected bindings were changed")
    for name in ["SOURCE_REVIEW.json", "SMOOTH_EXTRACTION.json", "FORMAT_ONLY_DELTA.json",
                 "STATIC_VERIFICATION.json", "run_selected.py", "install_sources.py"]:
        if historical_execution is not None and name in historical_execution:
            check_fingerprint(baseline["files"][name], historical_execution[name])
        else:
            check_fingerprint(baseline["files"][name])
    history = adoption["historical_five_owner_before_dependency_updates"]
    need(history["binding_snapshot"] == updates["prior_binding_snapshot"],
         "pre-update snapshot binding differs")
    old_receipt = check_fingerprint(history["static_receipt"])
    check_fingerprint(baseline["files"]["CURRENT_STATIC_VERIFICATION.json"], old_receipt)
    old_exceptions_raw = check_fingerprint(history["protected_exception_record"])
    check_fingerprint(baseline["files"]["PROTECTED_INPUT_EXCEPTIONS.json"], old_exceptions_raw)
    old_exceptions = json.loads(old_exceptions_raw)
    need(exceptions["exceptions"][0] == old_exceptions["exceptions"][0],
         "historical installer exception changed")

    published = "d20acdf13882e17d97833064f5e7c54f3192b03c"
    failed = "1a259e113c0977c8cb2814492ff3bd6ab7cdc475"
    first = updates["first_compile_repairs"]
    need(updates["published_phase1_update_commit"] == first["published_commit"] == published
         and first["failed_source_commit"] == failed, "first-compile source anchors differ")
    repair_raw = check_fingerprint(first["manifest"])
    need(git_bytes(published + ":" + first["manifest"]["path"]) == repair_raw,
         "published first-compile repair manifest differs")
    repair = json.loads(repair_raw)
    need(repair["failed_source_commit"] == failed, "repair preimage commit differs")
    expected_paths = {"ImbalancedChen/P1OriginalSingletonPointwiseData.lean",
                      "ImbalancedChen/P1Full87TrueDPolicyDelta.lean"}
    need({r["path"] for r in repair["files"]} == expected_paths and len(repair["files"]) == 2,
         "first-compile repair selection differs")
    summarized = {r["path"]: r for r in first["files"]}
    need(set(summarized) == expected_paths and len(first["files"]) == 2,
         "repair summary selection differs")
    preimages, changed_modules = {}, set()
    for row in repair["files"]:
        path = row["path"]
        normalized = {"module": row["module"], "path": path,
                      "before": {"path": path, **row["before"]},
                      "after": {"path": path, **row["after"]},
                      "splice_count": len(row["exact_byte_splices"])}
        need(summarized[path] == normalized, "repair summary differs")
        original = git_bytes(failed + ":" + path)
        check_fingerprint(normalized["before"], original)
        parts, previous = [], 0
        for splice in row["exact_byte_splices"]:
            lo, hi = splice["pre_start_byte"], splice["pre_end_byte"]
            need(previous <= lo < hi <= len(original) and
                 original[lo:hi] == splice["old_utf8"].encode(), "first-compile splice differs")
            parts.extend([original[previous:lo], splice["new_utf8"].encode()])
            previous = hi
        parts.append(original[previous:])
        current = check_fingerprint(normalized["after"])
        need(current == b"".join(parts) == git_bytes(published + ":" + path),
             "first-compile complete postimage differs")
        need(import_list(original) == import_list(current), "first-compile imports changed")
        preimages[path] = original
        changed_modules.add(row["module"])

    adopted = updates["existing_dependency_adoption"]
    accepted_raw = check_fingerprint(adopted["manifest"])
    accepted = json.loads(accepted_raw)
    need(accepted["schema"] == "p15_existing_atlas_dependency_source_reuse_v1" and
         accepted["base_commit"] == adopted["base_commit"] == published and
         accepted["accepted_publication_commit"] == adopted["accepted_publication_commit"] ==
         "a392cd8efcf4f0b4adf3d12f2d8db41370309ed3", "existing-postimage source anchors differ")
    need(accepted["module_count"] == adopted["module_count"] ==
         len(accepted["modules"]) == len(adopted["modules"]) == 9,
         "existing-postimage adoption count differs")
    need(not accepted["new_Lean_acceptance_claimed"] and
         not adopted["old_new_elaborated_type_equivalence_proved"] and
         not adopted["object_or_kernel_readiness_checked_here"], "unsupported source reuse claim")
    nine_modules = set()
    nine_preimages = {}
    for supplier, row in zip(accepted["modules"], adopted["modules"]):
        path, module = supplier["canonical_path"], supplier["module"]
        before, after = supplier["before"], supplier["after"]
        need(before["git_commit"] == published and
             after["source_git_commit"] == accepted["accepted_publication_commit"],
             "existing dependency source pin differs")
        original = git_bytes(before["git_commit"] + ":" + path)
        source = git_bytes(after["source_git_commit"] + ":" + after["source_repository_path"])
        need(before["sha256"] == sha(original) and before["bytes"] == len(original) and
             before["git_blob"] == fingerprint(original, path)["git_blob"],
             "existing dependency original bytes differ")
        need(after["sha256"] == sha(source) and after["bytes"] == len(source) and
             after["git_blob"] == fingerprint(source, path)["git_blob"],
             "existing accepted postimage bytes differ")
        need((ROOT / before["snapshot_path"]).read_bytes() == original and
             (ROOT / path).read_bytes() == source and
             (ROOT / after["source_repository_path"]).read_bytes() == source,
             "preserved preimage or current adopted source differs")
        need(import_list(original) == import_list(source) == supplier["direct_imports"],
             "existing-postimage imports differ")
        normalized = {
            "module": module, "path": path, "before": fingerprint(original, path),
            "before_commit": before["git_commit"],
            "preserved_preimage": fingerprint(original, before["snapshot_path"]),
            "after": fingerprint(source, path), "source_commit": after["source_git_commit"],
            "source": fingerprint(source, after["source_repository_path"]),
            "all_imports": supplier["direct_imports"],
            "reviewed_exception_classifications": supplier["repair_review"]["exception_classifications"],
            "old_new_elaborated_type_equivalence_proved": False,
        }
        need(row == normalized and
             supplier["repair_review"]["old_new_elaborated_type_equivalence_proved"] is False,
             "existing-postimage normalized binding or type-equivalence scope differs")
        need(module not in nine_modules, "duplicate adopted existing module")
        nine_modules.add(module)
        nine_preimages[path] = original
    need(not set(nine_preimages).intersection(adoption["protected_inputs"]),
         "nine-source adoption unexpectedly intersects original protected inputs")

    # Reconstruct the entire prior closure to preserve all unaffected row/field pins.
    reconstruction = updates["closure_reconstruction"]
    old_closure = copy.deepcopy(closure)
    for key in reconstruction["current_only_top_level_fields"]:
        need(key == "external_dependency_updates", "unexpected closure-only field")
        old_closure.pop(key)
    old_closure["stage1_comparison"] = reconstruction["before_stage1_comparison"]
    old_rows = reconstruction["before_changed_project_rows"]
    active_changes = (changed_modules | nine_modules).intersection(closure["project_sources"])
    need(set(old_rows) == active_changes and len(old_rows) == 10,
         "prior closure changed-row selection differs")
    originals = {**preimages, **nine_preimages}
    for module, row in old_rows.items():
        check_fingerprint(row, originals[row["path"]])
        old_closure["project_sources"][module] = row
    old_raw = (json.dumps(old_closure, ensure_ascii=False, indent=2) + "\n").encode()
    check_fingerprint(reconstruction["before_binding"], old_raw)
    need(reconstruction["before_binding"] == baseline["files"]["SOURCE_CLOSURE.json"],
         "prior closure fingerprint differs")
    phase1 = json.loads((PHASE1 / "SOURCE_CLOSURE.json").read_bytes())
    union = set(closure["project_sources"]) | set(phase1["project_sources"])
    membership = updates["membership"]
    need(sorted(active_changes) == membership["active_source_changes"] and
         sorted((changed_modules | nine_modules).intersection(union)) == membership["union_source_changes"] and
         membership["active_source_change_count"] == 10 and
         membership["union_source_change_count"] == 11 and
         not nine_modules.intersection(phase1["project_sources"]) and
         membership["nine_adoption_phase1_intersection"] ==
         membership["nine_adoption_original_protected_input_intersection"] == [],
         "source-change membership differs")
    need(updates["unchanged_owner_bindings"] == [r["destination"] for r in adoption["owners"]],
         "five original owner fingerprints changed")
    for row in updates["unchanged_owner_bindings"]:
        check_fingerprint(row, (owner_originals or {}).get(row["path"]))
    need(not updates["compiled"] and not updates["kernel_replayed"] and
         not updates["proof_credit_added"] and updates["new_arithmetic_proof_bodies"] == 0,
         "dependency metadata grants unsupported acceptance")
    return updates, preimages


def reconstruct_original_layering(layer, graph, preimages, owner_originals):
    """Recheck the pinned original extraction against verified e1 owner preimages.

    The historical verifier intentionally expects the initial Core/Mellin bytes.
    Keep it unchanged; reconstruct those exact source relations here instead of
    pretending that its original current-file check passes after explicit repairs.
    """
    finite_module = "ImbalancedChen.Part3FiniteLambdaOverLogDictionary"
    allk_module = "ImbalancedChen.Part3AllKLambdaChartCorrection"
    family_module = "ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound"
    declarations = ["lambdaOverLog", "lambdaOverLog_zero", "lambdaOverLog_one",
                    "lambdaOverLog_prime", "lambdaOverLog_prime_pow",
                    "lambdaOverLog_off_prime_powers", "lambdaOverLog_pointwise_split",
                    "finite_lambdaOverLog_split", "proper_term_has_prime_exponent"]
    need(set(layer["preimages"]) == {finite_module, allk_module, family_module} and
         [r["name"] for r in layer["declaration_ranges"]] == declarations,
         "original layered declaration/preimage selection differs")
    before = {module: preimages[pin["canonical_path"]]
              for module, pin in layer["preimages"].items()}
    ranges = layer["declaration_ranges"]
    core = b"".join(part["literal"].encode() if "literal" in part else
                    before[finite_module][part["start_byte"]:part["end_byte_exclusive"]]
                    for part in layer["core_construction"])
    finite = remove_intervals(before[finite_module],
                              [(r["old_start_byte"], r["old_end_byte_exclusive"]) for r in ranges])
    finite = layer["finite_added_import"].encode() + finite
    replacement = layer["allk_import_replacement"]
    old_import, new_import = replacement["before"].encode(), replacement["after"].encode()
    need(before[allk_module].startswith(old_import) and before[allk_module].count(old_import) == 1,
         "original AllK import position/multiplicity differs")
    allk = before[allk_module].replace(old_import, new_import, 1)
    need(allk[len(new_import):] == before[allk_module][len(old_import):],
         "AllK non-import bytes changed")
    expected = {CORE: core, finite_module: finite, allk_module: allk}
    need(set(layer["postimages"]) == set(expected), "layering postimage selection differs")
    for module, raw in expected.items():
        pin = layer["postimages"][module]
        check_fingerprint({"path": pin["canonical_path"], **pin}, raw)
        actual = owner_originals.get(pin["canonical_path"])
        if actual is None:
            actual = (ROOT / pin["canonical_path"]).read_bytes()
        need(raw == actual == (ROOT / pin["snapshot_path"]).read_bytes(),
             "original layering reconstruction differs")
    need(import_list(core) == ["Mathlib"] and
         (ROOT / layer["preimages"][family_module]["canonical_path"]).read_bytes() == before[family_module],
         "original Core imports or complete Family source differs")
    unchanged_current_core = 0
    current_core = (ROOT / (CORE.replace(".", "/") + ".lean")).read_bytes()
    for row in ranges:
        original = before[finite_module][row["old_start_byte"]:row["old_end_byte_exclusive"]]
        relocated = core[row["new_start_byte"]:row["new_end_byte_exclusive"]]
        check_fingerprint({"path": row["full_name"], **row}, original)
        need(original == relocated and row["full_name"] ==
             "ImbalancedChen.Part3.FiniteLambdaOverLogDictionary." + row["name"],
             "original Core declaration bytes or names differ")
        unchanged_current_core += int(current_core.count(original) == 1)
    need(unchanged_current_core == 7, "current Core differs from its two explicit repaired blocks")
    sorted_pin = layer["sorted_theorem_preservation"]
    sorted_body = before[finite_module][sorted_pin["old_start_byte"]:sorted_pin["old_end_byte_exclusive"]]
    check_fingerprint({"path": sorted_pin["name"], **sorted_pin}, sorted_body)
    need(finite.count(sorted_body) == 1, "complementary sorted theorem not preserved exactly once")
    pattern = r"^(?:def|theorem|lemma|abbrev|axiom|opaque) (?:" + "|".join(declarations) + r")\b"
    census = subprocess.run(["rg", "-n", pattern, "ImbalancedChen"], cwd=ROOT,
                            capture_output=True, text=True, check=False)
    lines = census.stdout.splitlines()
    need(census.returncode == 0 and len(lines) == 9 and
         all(line.startswith(CORE.replace(".", "/") + ".lean:") for line in lines),
         "original Core public declaration owner is duplicated")
    observation_pin = layer["source_only_observation"]
    observation = json.loads(check_fingerprint({"path": observation_pin["repository_path"],
                                               **observation_pin}))
    observed = {r["module"]: r for r in observation["rows"]}
    need(set(observed) == {finite_module, allk_module}, "historical source-only observation selection differs")
    for module, row in observed.items():
        need(row["source_matches"] and row["source"]["sha256"] == sha(before[module]) and
             all(value is None for value in row["outputs"].values()),
             "saved source-only observation differs")
    old_pin = graph["before386_source_manifest"]
    old = json.loads(check_fingerprint({"path": old_pin["repository_path"], **old_pin}))
    need(len(old["project_sources"]) == 386 and graph["extra45_retained_count"] == 3 and
         graph["extra45_outside_new_closure_count"] == 42,
         "historical layering source-graph scope differs")
    dependencies = {module: row["project_imports"]
                    for module, row in graph["after_project_sources"].items()}
    active = reachable(dependencies, EXPECTED_ROOTS)
    need(active == set(dependencies) and len(active) == 168 and finite_module not in active and
         {allk_module, family_module}.issubset(active), "original layering graph boundary differs")
    return {
        "status": "PASS_ORIGINAL_LAYERING_RECONSTRUCTION_WITH_EXPLICIT_CURRENT_OWNER_REPAIRS",
        "original_declarations_verified_on_published_preimage": 9,
        "current_Core_blocks_unchanged": unchanged_current_core,
        "current_Core_blocks_expression_repaired": 2,
        "unique_canonical_owner": CORE, "Core_literal_imports": ["Mathlib"],
        "AllK_only_import_changed": True, "Family_full_source_unchanged": True,
        "sorted_theorem_preserved": True, "old_source_closure": 386,
        "initial_six_owner_source_closure": 168,
        "historical_layering_verifier_preserved_not_invoked_on_repaired_sources": True,
        "Lean_invocations": 0, "new_Lean_acceptance": False,
    }


def layering_state(adoption, closure, exceptions, owner_originals, initial_closure):
    binding = adoption["source_layering_revision"]
    need(binding == closure["source_layering_revision"] == exceptions["source_layering_revision"],
         "layering revision binding differs")
    revision = json.loads(check_fingerprint(binding))
    need(revision["targets"] == EXPECTED_ROOTS and revision["project_module_count"] == 168 and
         revision["phase1_phase2_union_module_count"] == 349, "six-owner revision differs")
    snapshot = json.loads(check_fingerprint(revision["historical386_snapshot"]))
    for row in snapshot["files"]:
        raw = check_fingerprint(row["snapshot"])
        check_fingerprint(row["source"], raw)
    previous_adoption = json.loads(check_fingerprint(revision["historical386_adoption"]))
    previous_closure = json.loads(check_fingerprint(revision["historical386_closure"]))
    need(previous_closure["targets"] == LEGACY_ROOTS and previous_closure["project_module_count"] == 386,
         "historical386 stage was relabelled")
    need(adoption["protected_inputs"] == previous_adoption["protected_inputs"] and
         adoption["existing_canonical_reuse"] == previous_adoption["existing_canonical_reuse"],
         "original protected/reuse bindings changed")
    need(revision["unchanged_previous_five_owner_bindings"] ==
         [r["destination"] for r in adoption["owners"][1:]] ==
         [r["destination"] for r in previous_adoption["owners"]], "previous five owners changed")
    historical_execution = {
        "run_selected.py": check_fingerprint(revision["historical386_runner"]),
        "install_sources.py": check_fingerprint(revision["historical386_installer"]),
    }
    layer = json.loads(check_fingerprint(revision["source_layering_manifest"]))
    need(layer["schema"] == "p15_finite_lambda_original_source_layering_v1" and
         layer["Core_literal_imports"] == ["Mathlib"] and layer["Core_project_imports"] == [] and
         layer["declaration_count"] == 9 and not layer["new_Lean_acceptance_claimed"],
         "original Core source scope differs")
    preimages = {}
    for row in layer["preimages"].values():
        raw = (ROOT / row["snapshot_path"]).read_bytes()
        pin = {"path": row["canonical_path"], **{k: row[k] for k in ["bytes", "sha256", "git_blob"]}}
        check_fingerprint(pin, raw)
        need(raw == git_bytes(row["git_commit"] + ":" + row["canonical_path"]), "layering preimage differs")
        preimages[row["canonical_path"]] = raw
    for row in layer["postimages"].values():
        pin = {"path": row["canonical_path"], **{k: row[k] for k in ["bytes", "sha256", "git_blob"]}}
        raw = check_fingerprint(pin, owner_originals.get(pin["path"]))
        need(raw == (ROOT / row["snapshot_path"]).read_bytes() and import_list(raw) == row["literal_imports"],
             "layered canonical postimage/import differs")
    graph = json.loads(check_fingerprint(revision["source_layering_graph"]))
    need(graph["next_stage_six_targets"] == EXPECTED_ROOTS and
         set(graph["after_project_sources"]) == set(closure["project_sources"]), "layered graph differs")
    for module, row in graph["after_project_sources"].items():
        initial = initial_closure["project_sources"][module]
        need(all(initial[k] == row[k] for k in ["path", "bytes", "sha256", "git_blob", "all_imports", "project_imports"]),
             "initial168 graph differs from original layered source inventory")
        raw = check_fingerprint(row, owner_originals.get(row["path"]))
        need(import_list(raw) == row["all_imports"], "original layered source imports differ")
    verifier = layer["verifier"]
    check_fingerprint({"path": verifier["repository_path"],
                       **{k: verifier[k] for k in ["bytes", "sha256", "git_blob"]}})
    layered_receipt = reconstruct_original_layering(layer, graph, preimages, owner_originals)
    execution = json.loads(check_fingerprint(adoption["execution_revision"]))
    check_fingerprint(execution["runner"])
    check_fingerprint(execution["installer"])
    check_fingerprint(execution["fixture_verifier"])
    expected_fixture = json.loads(check_fingerprint(execution["fixture_report"]))
    fixtures = subprocess.run([sys.executable, str(ROOT / execution["fixture_verifier"]["path"])],
                              cwd=ROOT, capture_output=True, text=True, check=False)
    need(fixtures.returncode == 0, "readiness Python fixtures failed: " + fixtures.stderr)
    actual_fixture = json.loads(fixtures.stdout)
    need(actual_fixture == expected_fixture and actual_fixture["case_count"] == 18 and
         len(actual_fixture["unchanged_normal_audit_function_ASTs"]) == 13 and
         actual_fixture["real_command_calls"] == 0, "readiness fixture report differs")
    return revision, layer, preimages, previous_adoption, previous_closure, historical_execution, layered_receipt, actual_fixture


def verify():
    adoption = load("ADOPTION_MANIFEST.json")
    extraction = load("SMOOTH_EXTRACTION.json")
    review = load("SOURCE_REVIEW.json")
    delta = load("FORMAT_ONLY_DELTA.json")
    exceptions = load("PROTECTED_INPUT_EXCEPTIONS.json")
    closure = load("SOURCE_CLOSURE.json")
    historical = load("STATIC_VERIFICATION.json")
    need([r["module"] for r in adoption["owners"]] == EXPECTED_ROOTS,
         "six-owner adoption selection differs")
    need(closure["targets"] == EXPECTED_ROOTS and
         closure["schema"] == "p15_original_atlas_proper_power_source_closure_v2",
         "six-root closure revision differs")
    first_epoch_closure, first_epoch_sources, second_repair_receipt = second_compile_owner_repair(closure)
    owner_originals, initial_closure_raw, owner_repair_receipt = first_compile_owner_repairs(
        first_epoch_closure, first_epoch_sources)
    (revision, layer, layered_preimages, previous_adoption, previous_closure,
     historical_execution, layering_receipt, fixture_receipt) = layering_state(
         adoption, closure, exceptions, owner_originals, json.loads(initial_closure_raw))
    for row in adoption["toolchain_inputs"] + adoption["existing_canonical_reuse"]:
        check_fingerprint(row, layered_preimages.get(row["path"]))
    updates, repaired_originals = dependency_updates(previous_adoption, previous_closure, exceptions,
                                                     historical_execution, owner_originals)

    # Keep every original protected binding; five published changes plus exact layering.
    check_fingerprint(adoption["protected_input_exceptions"])
    need(len(adoption["protected_inputs"]) == 29 and len(exceptions["exceptions"]) == 7,
         "protected-input selection differs")
    exception = exceptions["exceptions"][0]
    need(exception["path"] == INSTALLER, "unexpected protected-input exception")
    need(exception["original_binding"] == adoption["protected_inputs"][INSTALLER],
         "protected installer baseline changed")
    exceptional = {r["path"]: r for r in exceptions["exceptions"]}
    need(len(exceptional) == 7 and set(exceptional) ==
         set(updates["membership"]["protected_changed_paths"]) |
         set(revision["additional_protected_layering_paths"]) and
         exceptions["original_protected_input_count"] == 29 and
         exceptions["unchanged_input_count"] == 22 and
         exceptions["exception_count"] == 7, "protected exception set differs")
    for path, row in adoption["protected_inputs"].items():
        if path not in exceptional:
            check_fingerprint(row)
        elif path in revision["additional_protected_layering_paths"]:
            change = exceptional[path]
            need(change["kind"] == "original_finite_source_layering" and change["original_binding"] == row and
                 change["source_layering_manifest"] == revision["source_layering_manifest"] and
                 change["source_layering_revision"] == adoption["source_layering_revision"] and
                 not change["normal_kernel_audit_api_changed"], "layering protected exception differs")
            check_fingerprint(row, layered_preimages[path])
            check_fingerprint(change["reviewed_current_binding"])
        elif path != INSTALLER:
            change = exceptional[path]
            need(change["kind"] == "published_phase1_first_compile_update" and
                 change["original_binding"] == row and
                 change["before_source_commit"] == updates["first_compile_repairs"]["failed_source_commit"] and
                 change["published_update_commit"] == updates["published_phase1_update_commit"] and
                 change["repair_manifest"] == updates["first_compile_repairs"]["manifest"] and
                 not change["phase2_modified_this_input"] and
                 not change["normal_kernel_audit_api_changed"], "published protected exception differs")
            check_fingerprint(row, git_bytes(change["before_source_commit"] + ":" + path))
            after = check_fingerprint(change["reviewed_current_binding"])
            need(after == git_bytes(change["published_update_commit"] + ":" + path),
                 "published protected postimage differs")
    after_installer = check_fingerprint(exception["reviewed_current_binding"])
    repair_raw = check_fingerprint(exception["repair_manifest"])
    repair = json.loads(repair_raw)
    need(repair["installer_before_sha256"] == exception["original_binding"]["sha256"]
         and repair["installer_after_sha256"] == sha(after_installer)
         and repair["normal_kernel_audit_api_changed"] is False,
         "installer exception repair binding differs")
    need(exception["normal_kernel_audit_api_changed"] is False
         and exception["phase2_modified_this_input"] is False,
         "exception scope differs")
    commit = exception["published_repair_commit"]
    need(git_bytes(commit + ":" + INSTALLER) == after_installer,
         "published installer differs")
    need(git_bytes(commit + ":" + exception["repair_manifest"]["path"]) == repair_raw,
         "published repair record differs")

    # Reconstruct the reviewed file exactly; the original review pins stay unchanged.
    check_fingerprint(adoption["format_only_delta"])
    check_fingerprint(extraction["format_only_delta"])
    check_fingerprint(review["post_review_format_only_delta"])
    smooth = check_fingerprint(delta["current_after"])
    check_fingerprint(delta["reviewed_before"], smooth + b"\n")
    need(delta["deleted_before_byte_interval"] == [len(smooth), len(smooth) + 1]
         and delta["deleted_hex"] == "0a", "format operation differs")
    need(smooth.endswith(b"\n") and not smooth.endswith(b"\n\n"),
         "format-only final-line condition differs")
    need(extraction["destination"] == delta["path"]
         and extraction["destination_sha256"] == sha(smooth)
         and extraction["destination_bytes"] == len(smooth)
         and extraction["destination_git_blob"] == delta["current_after"]["git_blob"],
         "smooth extraction destination differs")
    need({r["module"] for r in review["reviewed_owners"]} == set(LEGACY_ROOTS),
         "review owner selection differs")
    for row in review["reviewed_owners"]:
        if row["path"] == delta["path"]:
            check_fingerprint(row, smooth + b"\n")
        else:
            check_fingerprint(row, owner_originals.get(row["path"]))
    before_review = {k: v for k, v in review.items()
                     if k not in {"post_review_format_only_delta", "current_source_binding_note"}}
    before_review_raw = (json.dumps(before_review, ensure_ascii=False, indent=2) + "\n").encode()
    check_fingerprint(delta["source_review_before_delta"], before_review_raw)

    # Whole-source adoptions and the single explicit AllGroup import substitution.
    for row in adoption["owners"]:
        current = check_fingerprint(row["destination"], owner_originals.get(row["destination"]["path"]))
        kind = row["adoption"]
        if kind in {"complete_existing_t05_selected_source_byte_identical",
                    "complete_original_byte_identical"}:
            need(current == check_original(row["source"]), "complete source differs")
            if "selection_registry" in row:
                registry = check_original(row["selection_registry"])
                need(row["destination"]["sha256"].encode() in registry,
                     "selected source absent from recorded t05 registry")
        elif kind == "one_import_replacement_all_other_bytes_identical":
            original = check_original(row["source"])
            replace = row["replacement"]
            old, new = replace["old"].encode(), replace["new"].encode()
            need(original.count(old) == replace["occurrences"] == 1,
                 "AllGroup import replacement count differs")
            need(current == original.replace(old, new), "AllGroup non-import bytes changed")
        elif kind == "nine_exact_historical_declaration_blocks_in_original_namespaces":
            need(current == smooth, "smooth owner differs")
        elif kind == "nine_exact_original_finite_dictionary_declarations":
            need(row["module"] == CORE and row["declaration_count"] == 9 and
                 row["source_layering_manifest"] == revision["source_layering_manifest"] and
                 import_list(current) == ["Mathlib"], "original finite Core adoption differs")
        else:
            need(row["module"] == EXPECTED_ROOTS[-1]
                 and kind == "new_finite_dictionary_and_existing_P3_supplier_instantiation",
                 "unknown adoption kind")

    # The exact original18 + unchanged9 reconstruct both historical postimages.
    # Current PointwiseData is separately bound to its one published expression repair.
    check_fingerprint(extraction["stage1_manifest"])
    pointwise_binding = extraction["stage1_pointwise_owner"]
    pointwise = check_fingerprint(pointwise_binding, repaired_originals[pointwise_binding["path"]])
    pointwise_current = (ROOT / pointwise_binding["path"]).read_bytes()
    p1_extraction = json.loads((ROOT / extraction["stage1_manifest"]["path"]).read_bytes())
    p1_sources = {r["path"]: r for r in p1_extraction["sources"]}
    need(sha(pointwise) == p1_extraction["destination_sha256"], "pointwise owner differs")
    point_import = b"import ImbalancedChen.P1OriginalSingletonPointwiseData\n"
    smooth_import = b"import ImbalancedChen.P1OriginalSingletonSmoothLicence\n"
    names, point_names, post_count = set(), set(), 0
    unchanged_current_pointwise = 0
    max_destination_end = 0
    for source in extraction["sources"]:
        original = check_original(source)
        old = p1_sources[source["path"]]
        need(check_original(old) == original, "phase1/phase2 origin differs")
        stage1 = check_fingerprint(source["stage1_preimage"])
        check_fingerprint(old["provider_postimage"], stage1)
        point_intervals, smooth_intervals, stage1_intervals = [], [], []
        bodies = []
        for d in old["declarations"]:
            body = declaration_bytes(original, d)
            need(pointwise.count(body) == 1 and smooth.count(body) == 0,
                 "pointwise declaration ownership differs: " + d["name"])
            need(pointwise_current.count(body) <= 1, "duplicate current pointwise block")
            unchanged_current_pointwise += int(pointwise_current.count(body) == 1)
            point_names.add(d["name"])
            bodies.append(body)
            point_intervals.append((d["source_start_byte"], d["source_end_byte"]))
        need(stage1 == point_import + remove_intervals(original, point_intervals),
             "stage1 provider postimage differs")
        for d in source["declarations"]:
            body = declaration_bytes(original, d)
            lo, hi = d["destination_start_byte"], d["destination_end_byte"]
            need(0 <= lo < hi <= len(smooth) and smooth[lo:hi] == body
                 and smooth.count(body) == 1 and pointwise.count(body) == 0,
                 "smooth declaration ownership/interval differs: " + d["name"])
            a, b = d["stage1_preimage_start_byte"], d["stage1_preimage_end_byte"]
            need(stage1[a:b] == body and stage1.count(body) == 1,
                 "smooth stage1 interval differs: " + d["name"])
            need(d["name"] not in names, "duplicate extracted declaration")
            names.add(d["name"])
            bodies.append(body)
            smooth_intervals.append((d["source_start_byte"], d["source_end_byte"]))
            stage1_intervals.append((a, b))
            max_destination_end = max(max_destination_end, hi)
        post = check_fingerprint(source["provider_postimage"])
        need(post == smooth_import + remove_intervals(stage1, stage1_intervals),
             "phase2 provider postimage differs")
        need(post == smooth_import + point_import +
             remove_intervals(original, point_intervals + smooth_intervals),
             "combined27 provider postimage differs")
        need(all(post.count(body) == 0 for body in bodies),
             "postimage retains a migrated declaration")
        need(not FORBIDDEN.search(lean_code(post.decode())), "forbidden token in postimage")
        post_count += 1
    need(len(names) == extraction["declaration_count"] == 9
         and len(point_names) == extraction["stage1_pointwise_declaration_count"] == 18
         and len(names | point_names) == 27 and post_count == 4,
         "declaration/postimage counts differ")
    need(unchanged_current_pointwise == 17, "current pointwise expression-repair scope differs")
    need(max_destination_end == delta["maximum_protected_declaration_end_byte"] <= len(smooth),
         "deleted byte intersects protected declarations")
    for row in adoption["provider_postimages"]:
        check_fingerprint(row)

    # Verify all imports and fingerprints of the active168 and complete union349.
    # The immutable adoption manifest describes the published initial168 stage.
    # The current closure is checked independently against its exact repair record.
    check_fingerprint(adoption["current_source_closure"], initial_closure_raw)
    comparison = closure["stage1_comparison"]
    phase1_raw = (ROOT / comparison["manifest"]).read_bytes()
    need(sha(phase1_raw) == comparison["manifest_sha256"], "phase1 closure binding differs")
    phase1 = json.loads(phase1_raw)
    graph = {}
    forbidden_modules = []
    for manifest, full in [(phase1, False), (closure, True)]:
        for module, row in manifest["project_sources"].items():
            need(row["path"] == module.replace(".", "/") + ".lean", "module path differs")
            raw = check_fingerprint(row)
            imports = import_list(raw)
            project = [m for m in imports if m.startswith("ImbalancedChen.")]
            need(project == row["imports"], "project imports differ: " + module)
            if full:
                need(project == row["project_imports"] and imports == row["all_imports"],
                     "full import inventory differs: " + module)
                need(row["role"] == ("new_owner" if module in EXPECTED_ROOTS else
                                     "existing_canonical_cache_check_only"), "module role differs")
            if module in graph:
                need(graph[module] == project and row["sha256"] ==
                     phase1["project_sources"][module]["sha256"], "overlap differs")
            graph[module] = project
            if FORBIDDEN.search(lean_code(raw.decode())):
                forbidden_modules.append(module)
    need(not forbidden_modules, "forbidden proof token in project closure: " +
         ", ".join(sorted(set(forbidden_modules))))
    active = reachable(graph, EXPECTED_ROOTS)
    union = reachable(graph, phase1["targets"] + EXPECTED_ROOTS)
    need(active == set(closure["project_sources"]) and union == set(graph),
         "closure contains unrelated or missing project sources")
    need(len(active) == closure["project_module_count"] == 168
         and len(phase1["project_sources"]) == 316
         and len(union) == comparison["combined_project_module_count"] == 349,
         "closure count differs")
    new = active - phase1["project_sources"].keys()
    need(len(new - set(EXPECTED_ROOTS)) == 27
         and closure["existing_canonical_cache_check_count"] == 162
         and closure["target_count"] == closure["new_owner_count"] == 6,
         "new-owner/dependency count differs")
    need(not closure["missing"] and not closure["cycles"], "closure contains known failure")

    # The original four-provider receipt is never rewritten or relabelled as current.
    for item in [adoption["historical_four_provider_snapshot"],
                 closure["historical_four_provider_snapshot"]]:
        check_fingerprint(item["static_receipt"])
    need(historical["new_owner_count"] == 4 and historical["project_module_count"] == 358,
         "historical receipt scope differs")
    for record in [adoption, closure, extraction, historical]:
        need(record["compiled"] is False and record["kernel_replayed"] is False
             and record["proof_credit_added"] is False, "unsupported acceptance claim")
    input_names = ["ADOPTION_MANIFEST.json", "SMOOTH_EXTRACTION.json", "SOURCE_CLOSURE.json",
                   "SOURCE_REVIEW.json", "FORMAT_ONLY_DELTA.json", "PROTECTED_INPUT_EXCEPTIONS.json",
                   "STATIC_VERIFICATION.json", "README.md", "verify_source_reuse.py",
                   "BEFORE_DEPENDENCY_UPDATE_BINDINGS.json", "DEPENDENCY_SOURCE_UPDATES.json",
                   "STATIC_VERIFICATION_BEFORE_DEPENDENCY_UPDATES.json",
                   "PROTECTED_INPUT_EXCEPTIONS_BEFORE_DEPENDENCY_UPDATES.json",
                   "SOURCE_LAYERING_REVISION.json", "EXECUTION_REVISION.json",
                   "verify_pure_readiness.py", "PURE_READINESS_FIXTURES.json",
                   "run_selected.py", "install_sources.py", "FIRST_COMPILE_REPAIRS.json", "SECOND_COMPILE_REPAIRS.json",
                   "snapshots/source168-before-first-compile/SNAPSHOT.json"]
    return {
        "schema": "p15_original_atlas_proper_power_current_static_verification_v4",
        "status": "PASS_CURRENT_SIX_OWNER_SECOND_MELLIN_REPAIR_AND_SOURCE_GRAPH_ONLY",
        "source_context_commit": adoption["source_context_commit"],
        "selected_owners": EXPECTED_ROOTS,
        "selected_source_fingerprints": [file_fingerprint(r["destination"]["path"])
                                         for r in adoption["owners"]],
        "original_adoption_source_fingerprints": [r["destination"] for r in adoption["owners"]],
        "first_epoch_owner_repairs": owner_repair_receipt,
        "current_second_compile_repair": second_repair_receipt,
        "inputs": [file_fingerprint((HERE / n).relative_to(ROOT).as_posix()) for n in input_names],
        "current_smooth_bytes": len(smooth),
        "format_only_delta_reconstructs_reviewed_bytes": True,
        "original_review_record_preserved_except_explicit_delta_binding": True,
        "exact_smooth_declarations": len(names),
        "original_pointwise_declaration_blocks_verified": len(point_names),
        "current_pointwise_blocks_unchanged": unchanged_current_pointwise,
        "current_pointwise_expression_repaired_blocks": 1,
        "published_first_compile_source_repairs_exactly_reconstructed": 2,
        "published_first_compile_splice_count": 3,
        "adopted_existing_dependency_postimages": 9,
        "previous_external_dependency_source_changes_in_active_closure": 10,
        "previous_external_dependency_source_changes_in_phase1_phase2_union": 11,
        "historical_five_owner386_pre_external_update_closure_exactly_reconstructed": True,
        "original_finite_core_declarations_verified_on_published_preimage": 9,
        "current_Core_declaration_blocks_unchanged": 7,
        "current_Core_declaration_blocks_expression_repaired": 2,
        "AllK_only_import_layering_changed": True,
        "Family_full_source_unchanged": True,
        "inactive_original_Finite_sorted_theorem_preserved": True,
        "layering_original_source_reconstruction_result": layering_receipt,
        "pure_readiness_fixture_case_count": fixture_receipt["case_count"],
        "external_dependency_manifests": [updates["first_compile_repairs"]["manifest"],
                                          updates["existing_dependency_adoption"]["manifest"]],
        "reviewed_existing_dependency_exception_owners": [
            r["module"] for r in updates["existing_dependency_adoption"]["modules"]
            if r["reviewed_exception_classifications"]],
        "old_new_elaborated_type_equivalence_proved": False,
        "combined_declarations_removed_from_postimages": 27,
        "combined_provider_postimages": post_count,
        "original_Mellin_preimage_and_current_dictionary_bytes_equal_origins": True,
        "first_epoch_Mellin_exact_proof_expression_splices": 3,
        "second_epoch_Mellin_exact_proof_expression_splices": 1,
        "allgroup_exact_single_import_substitution": True,
        "original_protected_input_count": 29,
        "unchanged_protected_inputs": 22,
        "separately_reviewed_published_protected_exceptions": sorted(exceptional),
        "thirteen_normal_audit_function_ASTs_unchanged": True,
        "runtime_API_guard_global_bindings_unchanged": True,
        "installer_only_additive_scope_count_changed_5_to_6": True,
        "phase1_source_modules": 316,
        "current_active_source_modules": len(active),
        "phase1_phase2_union_source_modules": len(union),
        "new_owner_count": 6,
        "existing_active_dependencies_cache_check_only": 162,
        "newly_reached_existing_canonical_modules": 27,
        "all_source_hashes_and_imports_checked": True,
        "forbidden_proof_tokens_checked_on_union_and_postimages": True,
        "forbidden_proof_tokens_found": [],
        "missing_project_sources": [], "project_import_cycles": [],
        "historical_four_provider_receipt_unchanged": True,
        "historical_five_owner386_snapshot_unchanged": True,
        "historical_initial_six_owner168_snapshot_unchanged": True,
        "verification_method": "Python raw-byte/Git-blob/import-graph checks, original layering on published preimages, exact first-epoch five splices plus second-epoch Mellin splice, and fake-only readiness cases",
        "object_inventory_or_readiness_checked": False,
        "source_or_cache_mutations_by_verifier": 0,
        "Lean_or_Lake_invocations": 0, "cloud_tasks_started": 0,
        "compiled": False, "kernel_replayed": False, "full_owned_accepted": False,
        "proof_credit_added": False, "P1_5_closed": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    result = verify()
    text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.write_receipt:
        output = HERE / "CURRENT_STATIC_VERIFICATION.json"
        output.write_text(text)
        print(json.dumps({"status": result["status"], "receipt": output.relative_to(ROOT).as_posix(),
                          "sha256": sha(output.read_bytes()), "owners": 6,
                          "active_sources": 168, "union_sources": 349}, ensure_ascii=False))
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
