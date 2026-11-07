"""Static source metadata only. Does not run Lean, guards, or numeric replay."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def receipt(path, role, declarations=()):
    p = ROOT / path
    raw = p.read_bytes()
    text = raw.decode("utf-8-sig")
    lines = text.splitlines()
    found = []
    for name in declarations:
        matches = [i for i, line in enumerate(lines, 1)
                   if re.match(r"\s*(?:private\s+)?(?:def|theorem|abbrev|structure|inductive)\s+"
                               + re.escape(name) + r"(?:\s|[({:]|$)", line)]
        found.append({"name": name, "lines": matches})
    return {"path": path, "role": role, "sha256": hashlib.sha256(raw).hexdigest(),
            "bytes": len(raw), "line_count": len(lines), "declarations": found}

scope = HERE.relative_to(ROOT).as_posix()
source_map = {
    "ImbalancedChen.P2OriginalLiteralW1OldProfile":
        "docs/source-only/20261102-resume-30p/h247_step_profiles/P2OriginalLiteralW1OldProfile.lean",
    "ImbalancedChen.RenewalFiniteErrorPropagationP5": "ImbalancedChen/RenewalFiniteErrorPropagationP5.lean",
    "ImbalancedChen.P2Selected430CausalOccurrenceExporter":
        "docs/source-only/20261028-resume-30c/certificate_triple/P2Selected430CausalOccurrenceExporter.lean",
}
for p in HERE.glob("*.lean"):
    source_map["ImbalancedChen." + p.stem] = p.relative_to(ROOT).as_posix()

new = []
for p in sorted(HERE.glob("*.lean")):
    item = receipt(p.relative_to(ROOT).as_posix(), "new_source")
    text = p.read_text(encoding="utf-8")
    namespace = re.search(r"^namespace\s+(\S+)", text, re.M).group(1)
    item.update({"namespace": namespace, "intended_module": "ImbalancedChen." + p.stem,
                 "intended_install_path": "ImbalancedChen/" + p.name,
                 "compiled": False, "kernel_verified": False, "formal_credit": 0})
    item["declarations"] = [{"kind": m.group(1), "name": namespace + "." + m.group(2),
                             "line": text[:m.start()].count("\n") + 1}
                            for m in re.finditer(r"^(def|abbrev|theorem)\s+(\S+?)(?=\s|\{|\(|:)", text, re.M)]
    item["direct_imports"] = []
    for module in re.findall(r"^import\s+(\S+)", text, re.M):
        r = receipt(source_map[module], "direct_import")
        r.update({"module": module,
                  "installed_at_intended_path": source_map[module] == module.replace(".", "/") + ".lean"})
        item["direct_imports"].append(r)
    item["forbidden_tokens"] = re.findall(r"\b(?:sorry|admit|axiom|native_decide|run_tac|unsafe)\b|#(?:eval|reduce|check)", text)
    new.append(item)

specs = [
 ("ImbalancedChen/P5OriginalActionMassBound.lean", "actual_scalar_mass",
  ["W2FeedbackMass_le_59_fifths", "original70W1_feedback_mass_le_five_halves", "original36W2_feedback_mass_lt_twelve"]),
 ("ImbalancedChen/P5OriginalFeedbackTableKernels.lean", "closed_table_integrals",
  ["tableFunction", "tableFunction_bounds", "weightedTable_integral_atom_sum"]),
 ("ImbalancedChen/P5OriginalFeedbackDomains.lean", "literal_profiles",
  ["pairProfile", "W2PairDomain_geometry", "measurable_singletonProfile"]),
 ("ImbalancedChen/Part5OriginalUpsilon5FloorKernel.lean", "literal_closed_atoms",
  ["FloorAtom", "floorAtomValue", "floorKnotValue"]),
 ("ImbalancedChen/Part5RenewalTablePositivity.lean", "unit_bounded_table",
  ["UnitBoundedData", "upperFloor_bounds_of_data"]),
 ("ImbalancedChen/P2EnhancedTwentyOneSameQWeighted.lean", "original_theta", ["Theta"]),
 ("ImbalancedChen/P2MarkedThetaLiNormalization.lean", "separate_true_li_conversion",
  ["trueTheta_eq_Theta_add", "uniform_trueTheta_relative_error"]),
 ("ImbalancedChen/RenewalFiniteErrorPropagationP5.lean", "unchanged_propagation",
  ["localBudget", "iterate", "iterate_430_rounds_11_depth", "rootCoefficient_norm", "exists_local_reserve"]),
 ("docs/source-only/20261102-resume-30m/h247_w2_mass_license/P2OriginalChildPhysicalNormalization.lean",
  "exact_sameQ_local_factors", ["thetaAtom", "Theta_eq_sum_atoms", "thetaAtom_single", "thetaAtom_pair", "localPrimeFactor_pos"]),
 ("docs/source-only/20261102-resume-30m/h247_w2_mass_license/P2OriginalBankChildPrimeMass.lean",
  "prime_mass_source", ["scaledPrimeSum", "single_integral_coordinates"]),
 ("docs/source-only/20261102-resume-30m/h247_w2_mass_license/P2OriginalBankThetaMassLimits.lean",
  "prime_local_factor_error", ["local_error", "pair_local_error", "physical_log_ratio"]),
 ("docs/source-only/20261102-resume-30o/h247_moving_mass/P2OriginalCompactMovingGateMass.lean",
  "compact_uniform_gate_source", ["compact_uniform_affine_gates"]),
 ("docs/source-only/20261102-resume-30o/h247_moving_mass/P2OriginalCompactScaledPrimeMass.lean",
  "moving_residual_uniformity", ["compact_uniform_scaled_affine"]),
 ("docs/source-only/20261102-resume-30o/h247_moving_mass/P2OriginalCompactThetaMass.lean",
  "compact_physical_mass", ["compact_multiplier_error", "bank_compact_uniform_masses"]),
 ("docs/source-only/20261102-resume-30o/h247_moving_mass/P2OriginalPositiveSameQMassLift.lean",
  "positive_sameQ_lift", ["thetaAtom_nonneg", "sameQ_residual_gt_one", "finite_nonnegative_absolute_lift"]),
 ("docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalHalfOpenProfileCarrier.lean",
  "actual_half_open_carriers", ["singleHalf", "pairHalf", "pairHalf_geometry", "profileAtomSum", "profileSum_eq_atoms"]),
 ("docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalAffineProfilePassage.lean",
  "arithmetic_wall_payment", ["compact_uniform_sandwich"]),
 ("docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalClosedCellProfileAtoms.lean",
  "all_closed_atom_uniformity", ["compact_uniform_profile_atom"]),
 ("docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalOldProfilePrimeLimits.lean",
  "old_profile_prime_source", ["compact_uniform_old_profile"]),
 ("docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalPhysicalOldProfileMass.lean",
  "physical_local_factors_and_profiles", ["trueSingleTest_error", "truePairTest_error", "single_profile_original_integral", "pair_profile_original_integral"]),
 ("docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalBankOldProfilePassage.lean",
  "original_106_profiles", ["W1OldIntegral", "W2OldIntegral", "W1_endpoints", "W2_singleton_top"]),
 ("docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalProfileThetaNormalization.lean",
  "actual_sameQ_bank_passage", ["singleThetaOldProfile", "pairThetaOldProfile", "W2ThetaOldProfile", "all106_sameQ_Theta_profile_passage"]),
 ("docs/source-only/20261102-resume-30p/h247_moving_mass/P2OriginalPrefixMaskMass.lean",
  "W1_dN_mask_payment", ["compact_uniform_moving_prefixMask_difference"]),
 ("docs/source-only/20261102-resume-30p/h247_step_profiles/P2OriginalLiteralW1OldProfile.lean",
  "literal_W1_sameQ_source", ["prefix_le_target_of_true_alpha", "literalW1ThetaOldProfile", "literalW1ThetaOldProfile_eq", "all70_literal_sameQ_Theta_profile_passage"]),
 ("docs/source-only/20261028-resume-30c/certificate_triple/P2Selected430LiteralActionData.lean",
  "immutable106_literal_data_unevaluated", ["Row", "q", "rows"]),
 ("docs/source-only/20261028-resume-30c/certificate_triple/P2Selected430CausalOccurrenceExporter.lean",
  "actual_immutable430_predecessor_source", ["seed", "candidate", "roundDecision", "roundTable", "iterate", "selectedW1_source"]),
 ("docs/source-only/20261028-resume-30d/certificate_triple/P2Selected430ActualW1SourceCoverage.lean",
  "existing_partial_actual_history_source", ["SourceSteps", "source_steps_sound"]),
 (".lake/proof-continuation/source-reviews/drafts/20261024z-P5/adopted-full-c/OriginalThetaChildArithmeticP5.lean",
  "hidden_prior_exact_arithmetic_reuse_not_imported", ["original_density_ratio", "thetaUnit_child_sameQ"]),
]
reused = [receipt(p, role, names) for p, role, names in specs]

baseline_paths = [
 "docs/source-only/20261102-resume-30r/BRIEF.md",
 "docs/source-only/20261102-resume-30r/DISPATCH.json",
 "docs/source-only/20261102-resume-30q/q03_original_gap_triage/NEXT_DIRECT_PROOF_REVIEW.md",
 "docs/source-only/20261102-resume-30q/h430_descendants/REPORT.md",
 "docs/source-only/20261102-resume-30q/h430_descendants/REGISTRY.json",
 "docs/source-only/20261102-resume-30q/reviews/q26_review_h430.md",
 "docs/source-only/20261102-resume-30p/h430_smooth_causal_boxes/REPORT.md",
 "docs/source-only/20261102-resume-30p/h430_smooth_causal_boxes/REGISTRY.json",
 "docs/source-only/20261102-resume-30p/h430_frozen_q/REPORT.md",
 "docs/source-only/20261102-resume-30p/h430_frozen_q/REGISTRY.json",
 "docs/source-only/20261102-resume-30p/reviews/t25_review_h430.md",
 "docs/source-only/20261102-resume-30p/h247_step_profiles/REPORT.md",
 "docs/source-only/20261102-resume-30p/h247_step_profiles/REGISTRY.json",
 "../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex",
 "../chen-imbalanced-semiprimes/paper/source/modules/global-chen-lower-completion-20261010.txt",
 "lakefile.toml", "lake-manifest.json",
]
baselines = [receipt(p, "read_baseline") for p in baseline_paths]

table = "| File | SHA256 |\n| --- | --- |\n" + "\n".join(
    "| `" + Path(x["path"]).name + "` | `" + x["sha256"] + "` |" for x in new)
report = HERE / "REPORT.md"
report_text = report.read_text(encoding="utf-8")
if "<!-- SOURCE_HASH_TABLE -->" in report_text:
    report.write_text(report_text.replace("<!-- SOURCE_HASH_TABLE -->", table), encoding="utf-8", newline="\n")
else:
    report_text = re.sub(r"\| File \| SHA256 \|\n\| --- \| --- \|\n(?:\|.*\|\n?){4}", table + "\n", report_text)
    report.write_text(report_text, encoding="utf-8", newline="\n")

data = {
 "schema_version": 1, "batch": "20261102-resume-30r", "task_id": "h430_parent_theta_441",
 "task_number": 16, "proof_plan_item": "D14", "author_agent": "/root/r16_h430_parent_theta_441",
 "write_scope": scope, "status": "PARTIAL_SOURCE_INCREMENT", "full_target_status": "OPEN",
 "task_complete": False, "local_delivery_complete": True, "compiled": False,
 "kernel_verified": False, "formal_credit": 0, "ready_to_install": False,
 "finite_guards": "UNEVALUATED", "new_lean_files": new, "reused_sources": reused,
 "baselines": baselines, "report": receipt(scope + "/REPORT.md", "delivery_report"),
 "removed_local_premises": [
  "For the explicitly constructed 106 actual arithmetic carrier rows, coefficient nonnegativity is derived.",
  "For the same rows, normalized parent-Theta mass <= 12 is derived from actual arithmetic passage and scalar mass margin.",
  "Zero-Theta absolute feedback coefficient vanishing is derived before division.",
  "Arithmetic and normalized-coordinate ideal closed-atom row/profile identities are derived.",
  "The displayed localBudget normalization formula retains an unpaid base discrepancy and is proved, not assumed.",
  "One arithmetic threshold for all actual seed-only430 predecessor-array bank profiles is derived."
 ],
 "remaining_dependencies": [
  "All physical full-Member/causal history carrier and same-source coefficient identifications.",
  "Actual Buchstab arithmetic rows and full native-coordinate/parent-family conversion.",
  "Coefficientwise absolute error and actual ordinary/fixed/switched base discrepancy payment.",
  "Original 400-state closed-minimum-owner and literal candidate-weight/floor bridge.",
  "One nested smooth causal realization for all queries and 441 generations, pre-N tau/caps/refinement.",
  "Old analytic count licences, switched-cost licences, final root reserve and actual h34."
 ],
 "difficulty": {"class_1": "All Lean API/elaboration unverified; source-only imports and external source receipts unresolved.",
  "class_2": "Actual arithmetic 106-bank mass, finite atom identities and exact predecessor profile threshold supplied in source form.",
  "class_3": "Full physical common realization and absolute local budgets remain open; no manuscript counterexample."},
 "remote_reuse_probe": {
  "repository": "subfish-zhou/goldbach-lean", "revision": "09b97db5764ade1246bfb77206baa1b124760958",
  "paths_probed": ["MathlibNt/Wu2008DoubleSieve/ReboxingNormalization.lean", "MathlibNt/Wu2008DoubleSieve/BoxMassTheta.lean"],
  "raw_result": "404 for the literal paths", "recursive_tree_result": "GitHub API rate limit",
  "github_fetch_result": "Tool unavailable", "downloaded_bytes": None,
  "conclusion": "External exact bytes not verified; no alternative path or theorem absence inferred."
 },
 "verification": {"source_tokens_only": True, "hashes_and_json_only": True,
  "lean_compiler_invoked": False, "lake_invoked": False, "ci_dispatched": False,
  "numeric_replay": False, "finite_guard_execution": False, "git_operations": False,
  "subagents_spawned": False, "old_files_modified": False},
 "independent_review": {"agent": "/root/r28_review_h430", "scope": "Four source proof bodies and actual principal dependencies read during development; full target HOLD.",
  "expected_final_review_path": "docs/source-only/20261102-resume-30r/reviews/r28_review_h430.md", "final_review_received": False, "inherits_kernel_credit": False}
}
(HERE / "REGISTRY.json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
missing = [(x["path"], d["name"]) for x in reused for d in x["declarations"] if len(d["lines"]) != 1]
print(json.dumps({"new_sources": len(new), "new_declarations": sum(len(x["declarations"]) for x in new),
 "missing_or_ambiguous_declaration_receipts": missing,
 "forbidden_tokens": {Path(x["path"]).name: x["forbidden_tokens"] for x in new},
 "report_sha256": data["report"]["sha256"],
 "registry_sha256": hashlib.sha256((HERE / "REGISTRY.json").read_bytes()).hexdigest()}, ensure_ascii=False))
