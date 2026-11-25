#!/usr/bin/env python3
"""Reconstruct the six assigned source edits and record lexical identity only.

This script does not run Lean, change production, or claim kernel acceptance.
"""
from pathlib import Path
import difflib
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

EDITS = {
    "P4AOriginalRemainingEighthSources.lean": [
        ("      norm_num [evaluate, K, X, add_assoc]\n",
         "      norm_num [evaluate, K, X, add_assoc]\n      rfl\n"),
    ],
    "P4AOriginalFirstFailureH3SourceSemantics.lean": [
        ("      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, add_assoc]\n",
         "      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, add_assoc] <;> rfl\n"),
        ("      not_true_eq_false, not_false_eq_true, ite_true, ite_false, add_assoc]\n",
         "      not_true_eq_false, not_false_eq_true, ite_true, ite_false, add_assoc] <;> rfl\n"),
        ("    norm_num [evaluate, K, X, mu, W]\n  ring\n",
         "    norm_num [evaluate, K, X, mu, W]\n  first | rfl | ring\n"),
    ],
    "P1OriginalCoarseContinuationCells.lean": [
        ("theorem active_ancestor3_of_wholeActive_cell (e : ℚ) (chi : ℝ) (m : ℕ)\n",
         "theorem active_ancestor3_of_wholeActive_cell (_e : ℚ) (_chi : ℝ) (m : ℕ)\n"),
        ("  clear e chi\n", "  clear _e _chi\n"),
    ],
    "P4AActualSixthFrozenEighthAdmission.lean": [
        ("      simpa only [hanc] using htail\n",
         "      rw [← hpre, hanc]\n      exact htail\n"),
    ],
    "P1HistoricalFourthFullCellLimit.lean": [
        ("    change (∑ i, t i) + t (Fin.last 3) ≤ lambda at hh\n",
         "    change (∑ i, t i) + t 3 ≤ lambda at hh\n"),
        ("    dsimp [P1FourthNearOneKernel.residual]\n    linarith\n",
         "    dsimp [P1FourthNearOneKernel.residual]\n"
         "    change (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p 3 ≤ lambda at hlegal\n"
         "    linarith\n"),
        ("    intro t ht\n    rw [extendedProfile_eq_raw_on_joint D ha hab j hlevel ht]\n",
         "    intro t ht\n    dsimp only\n    rw [extendedProfile_eq_raw_on_joint D ha hab j hlevel ht]\n"),
    ],
    "P2OriginalSaving19SimplexMoments.lean": [
        ("  simp [Fin.sum_univ_succ] <;> ring\n", "  simp [Fin.sum_univ_succ]\n  ring\n"),
        ("    simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]\n",
         "    simp only [factors]\n"),
    ],
}

DECL = re.compile(
    r"(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable) )*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|structure|inductive|class|instance) "
    r"(?P<name>[^\s({:]+)"
)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def records(raw):
    text = raw.decode()
    starts = list(DECL.finditer(text))
    out = []
    for i, match in enumerate(starts):
        end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
        span = text[match.start():end]
        header = span.split(":=", 1)[0]
        out.append({"kind": match["kind"], "name": match["name"],
                    "line": text[:match.start()].count("\n") + 1,
                    "header": header, "span": span})
    return out


files = []
identity = []
patch = []
for filename, edits in EDITS.items():
    relative = Path("ImbalancedChen") / filename
    before = (HERE / "before" / relative).read_bytes()
    after = (ROOT / relative).read_bytes()
    reconstructed = before
    for old, new in edits:
        assert reconstructed.count(old.encode()) == 1, (filename, old)
        reconstructed = reconstructed.replace(old.encode(), new.encode(), 1)
    assert reconstructed == after, (filename, "unrecorded source change")
    pre, post = records(before), records(after)
    assert [(d["kind"], d["name"]) for d in pre] == [(d["kind"], d["name"]) for d in post]
    decls = []
    for a, b in zip(pre, post):
        exact_header = a["header"] == b["header"]
        alpha_header = b["header"]
        if filename == "P1OriginalCoarseContinuationCells.lean" and a["name"] == "active_ancestor3_of_wholeActive_cell":
            alpha_header = alpha_header.replace("(_e : ℚ)", "(e : ℚ)").replace("(_chi : ℝ)", "(chi : ℝ)")
        assert a["header"] == alpha_header, (filename, a["name"], "statement change")
        if a["kind"] not in {"theorem", "lemma"}:
            assert a["span"] == b["span"], (filename, a["name"], "definition change")
        decls.append({"name": a["name"], "kind": a["kind"], "before_line": a["line"],
                      "after_line": b["line"], "header_exact": exact_header,
                      "header_exact_after_recorded_alpha_rename": a["header"] == alpha_header,
                      "before_header_sha256": sha(a["header"].encode()),
                      "after_header_sha256": sha(b["header"].encode()),
                      "before_span_sha256": sha(a["span"].encode()),
                      "after_span_sha256": sha(b["span"].encode()),
                      "span_exact": a["span"] == b["span"]})
    pre_lines, post_lines = before.decode().splitlines(), after.decode().splitlines()
    for prefix in ("import ", "set_option "):
        assert [x for x in pre_lines if x.startswith(prefix)] == [x for x in post_lines if x.startswith(prefix)]
    destination = HERE / "after" / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(after)
    changed = [d["name"] for d in decls if not d["span_exact"]]
    files.append({"module": "ImbalancedChen." + Path(filename).stem,
                  "production_path": str(relative), "before": {"bytes": len(before), "sha256": sha(before)},
                  "after": {"bytes": len(after), "sha256": sha(after)},
                  "exact_replacements": [{"old": old, "new": new} for old, new in edits],
                  "all_bytes_accounted_by_recorded_replacements": True,
                  "changed_declarations": changed, "imports_and_options_exact": True,
                  "definition_bodies_exact": True})
    identity.append({"module": files[-1]["module"], "declaration_count": len(decls),
                     "all_headers_exact": all(d["header_exact"] for d in decls),
                     "all_headers_exact_after_recorded_alpha_rename": True,
                     "declarations": decls})
    patch.extend(difflib.unified_diff(before.decode().splitlines(True), after.decode().splitlines(True),
                                    fromfile="a/" + str(relative), tofile="b/" + str(relative)))

logs = []
for name in ["P2_RESUMED_EARLY_DIAGNOSTICS.log", "P2_RESUMED_LATER_DIAGNOSTICS.log"]:
    path = HERE.parent / name
    raw = path.read_bytes()
    logs.append({"path": str(path.relative_to(ROOT)), "bytes": len(raw), "sha256": sha(raw)})

donors = []
for donor_root in [Path("/workspace/scratch/adad8d3ee47c/goldbach-p14"),
                   Path("/workspace/scratch/76f3bdb16a38/goldbach-p15")]:
    for filename in EDITS:
        path = donor_root / "ImbalancedChen" / filename
        if path.is_file():
            raw = path.read_bytes()
            exact = raw == (ROOT / "ImbalancedChen" / filename).read_bytes()
            donors.append({"path": str(path), "sha256": sha(raw), "postimage_byte_identical": exact})

manifest = {
    "schema": "p25-six-actual-compatibility-repairs-v1",
    "status": "SOURCE_REPAIRS_PREPARED_NOT_RECOMPILED_NOT_KERNEL_OR_OWNED_ACCEPTED",
    "actual_compile_source": "59e552b5459f6c0b8852e02c037c00d34a86e32f",
    "actual_diagnostic_logs": logs,
    "classification": "Formal expression and strict-linter compatibility only; no missing manuscript derivation or mathematical gap identified by these diagnostics.",
    "reuse_first": {"donors_checked": donors,
                   "prior_repairs_checked": "docs/verification/20261125-p2-5-saving16/p2-followup-repairs",
                   "exact_donor_postimages": ["P4AActualSixthFrozenEighthAdmission.lean", "P1HistoricalFourthFullCellLimit.lean"],
                   "other_changes": "Reuse the existing rfl-first terminal proof pattern and apply the actual strict-linter suggestions only."},
    "binder_rename": {"declaration": "P1OriginalCoarseContinuationCells.active_ancestor3_of_wholeActive_cell",
                      "changes": {"e": "_e", "chi": "_chi"},
                      "argument_types_order_explicitness_and_conclusion_unchanged": True,
                      "observed_production_calls": "Both calls are positional; no argument is removed."},
    "files": files,
    "validation": {"whole_file_reconstruction": True, "all_definition_bodies_unchanged": True,
                   "source_declaration_names_order_unchanged": True,
                   "all_source_headers_exact_except_recorded_unused_binder_alpha_rename": True,
                   "imports_options_linter_settings_unchanged": True,
                   "lean_compile_run": False, "kernel_replay_run": False, "full_owned_audit_run": False,
                   "cloud_actions_run": False,
                   "required_next_gate": "Parent strict incremental P2 compilation and complete owned-declaration/kernel acceptance for the exact postimage bytes."}
}
(HERE / "REPAIR_MANIFEST.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
(HERE / "DECLARATION_IDENTITY.json").write_text(json.dumps({
    "schema": "p25-six-repairs-lexical-identity-v1",
    "scope": "Source declaration spans end at the next named declaration start; headers end before the first :=. This is lexical identity, not elaborated type or axiom acceptance.",
    "files": identity}, ensure_ascii=False, indent=2) + "\n")
(HERE / "repair.patch").write_text("".join(patch))
print(json.dumps({"owners": len(files), "declarations": sum(x["declaration_count"] for x in identity),
                  "changed_declarations": sum(len(x["changed_declarations"]) for x in files),
                  "postimages": [{"module": x["module"], "sha256": x["after"]["sha256"]} for x in files],
                  "lean_or_kernel_acceptance_claimed": False}, ensure_ascii=False, indent=2))
