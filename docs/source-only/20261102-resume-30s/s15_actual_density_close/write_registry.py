"""Read source bytes and emit S15 metadata. No mathematical code is executed."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(r"E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation")
HERE = ROOT / "docs/source-only/20261102-resume-30s/s15_actual_density_close"
SOURCE = ROOT / "docs/source-only"

new_names = [
    "P4AActualRefinableArchivePayment.lean",
    "P4AActualFinitePositiveEndpoint.lean",
    "P4AActualJointDensitySchedule.lean",
]
reused = [
    (SOURCE / "20261102-resume-30r/fifth_reserve64/P5HistoricalActualReserve64Schedule.lean", "R05 original full archive schedule; arbitrary eta reserve64 and old-literal estimates"),
    (SOURCE / "20261102-resume-30r/fifth_reserve64/P5HistoricalActualReserve64Budget.lean", "Actual all-index reserve64 <= gatePaidEnvelope"),
    (SOURCE / "20261102-resume-30h/upper_jensen/P5HistoricalGatePaidReserveSchedule.lean", "Actual gatePaidEnvelope continuity at zero and literal integral estimate"),
    (ROOT / "ImbalancedChen/P1OriginalFifthGrid400RefinedFullBoxCover.lean", "Original aligned mesh and arbitrarily small step with complete cover"),
    (SOURCE / "20261102-resume-30s/s13_all22_actual_ledger/P4AOriginalCatalogFiveArchiveSchedule.lean", "Consumed actual catalogue-five schedule, same data, slot-five source endpoint"),
    (SOURCE / "20261102-resume-30s/s13_all22_actual_ledger/P4AOriginalFourPositiveEndpoints.lean", "Consumed actual first/compact/third-tail positive endpoint bindings"),
    (SOURCE / "20261102-resume-30s/s08_full_fifth_floor/P5OriginalFullFifthFloorIntegral.lean", "Consumed universal complete actual stored old/64 fifth floor, same reserve once"),
    (SOURCE / "20261102-resume-30s/s14_full_buffered_compiler/P4AFiniteCapTaggedPayment.lean", "Existing complete compiler payment for explicit finite-cap constructor; actual full87 instantiation remains, not imported by S15"),
    (SOURCE / "20261102-resume-30r/actual_density_reserve/P4AActualCompleteCatalogFiveCapPayment.lean", "Complete R07 ordinary catalogue and two Q22 caps paid once, upstream of S13"),
    (SOURCE / "20261102-resume-30r/actual_density_reserve/P4AActualSmallTailDensityCatalogue.lean", "Literal catalogFiveCapError definition only; old tail-bearing payment not additionally charged"),
    (SOURCE / "20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveSmallThirdPayment.lean", "Complete ordinary catalogue source, including full-List omitted-small-third; already paid"),
    (SOURCE / "20261102-resume-30r/full_buffered_policy/P4AOriginalBufferedArchiveContinuation.lean", "Actual originalSchedule and exact original fourth/fifth signed gains"),
    (SOURCE / "20261102-resume-30o/all22_common_history/P4AOriginalCausalHistory.lean", "ArchiveSchedule.data source definition"),
    (SOURCE / "20261028-resume-30e/upper_mesh/P1HistoricalFifthCommonPolicyInputs.lean", "Literal sourceData fields, original aligned mesh and indexed owners"),
    (ROOT / "ImbalancedChen/Part4ActualThirdFiniteDensityReserve.lean", "Consumed original finite-third u_d/4 supplier; never spent twice"),
    (ROOT / "ImbalancedChen/P4AAll22OriginalKLedger.lean", "Original E/u_d/u_c/K and explicit remaining 3u_d/4 identity"),
    (ROOT / "ImbalancedChen/P4AAll22ActualCompactPositiveBinding.lean", "Actual compact/positive-four definitions and original root dictionary"),
    (ROOT / "ImbalancedChen/P4AActualFirstIntegralSelectedK.lean", "Selected actual first-integral endpoint, inherited through S13"),
    (SOURCE / "20261102-resume-30o/compact_total_endpoint/P2OriginalCompactWholeFunctionalEndpoint.lean", "Complete original compact endpoint, inherited through S13; uncompiled"),
    (SOURCE / "20261102-certificates-l/compact_run_certificate/P2OriginalCompactCachedEndpointCandidate.lean", "Inherited two-million-split cached candidate; finite body UNEVALUATED"),
    (SOURCE / "20261102-resume-30o/compact_total_endpoint/P2OriginalCompactArchivedTotalCandidate.lean", "Inherited original compact archived-total candidate; UNEVALUATED"),
    (ROOT / "ImbalancedChen/ActualUpperDensityAssembly.lean", "Existing conditional full-policy and compiler interfaces; not new supply"),
    (ROOT / "ImbalancedChen/ActualFirstExitDensityProjection.lean", "Actual same-retain upper presieve projection and uniform beta reserve"),
    (ROOT / "ImbalancedChen/ActualCompilerDensityReserve.lean", "Actual same-small-weights compiler slope; total compiler error remains separate"),
    (ROOT / "ImbalancedChen/ActualUpperCountingInputs.lean", "Exact attachedUpperCoefficient and moduli definitions"),
    (ROOT / "ImbalancedChen/P4BCoefficientTransport.lean", "Existing first-exit attachment adapter, not a general compiled coefficient identity"),
    (ROOT / "ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean", "Exact present hdensity endpoint, lines 40-44"),
    (ROOT / "ImbalancedChen/RealUpperCountingAssembly.lean", "Existing general same-Q/same-rho endpoint; no new final consumer"),
    (SOURCE / "20261102-resume-30o/actual_two_reserves/P4ACommonPolicyTaggedCompiler.lean", "Exact held general compiledRho constructor"),
    (SOURCE / "20261102-resume-30p/actual_two_reserves/P4AUpperTaggedContinuationAccounting.lean", "Exact signed compiler and presieve correction accounting"),
]
context = [
    (SOURCE / "20261102-resume-30s/BRIEF.md", "S authoritative constraints"),
    (SOURCE / "20261102-resume-30r/actual_density_reserve/REPORT.md", "R10 final report"),
    (SOURCE / "20261102-resume-30r/actual_density_reserve/REGISTRY.json", "R10 final source registry"),
    (SOURCE / "20261102-resume-30r/reviews/r26_review_reserves_density.md", "R26 independent reserve and same-rho review"),
    (SOURCE / "20261102-resume-30s/s14_full_buffered_compiler/REPORT.md", "S14 final explicit finite-cap payment/full87 candidate scope"),
    (ROOT.parent / "chen-imbalanced-semiprimes/paper/source/manuscript-body.tex", "Body 453-509 original finite realization/two reserves/density"),
    (ROOT.parent / "chen-imbalanced-semiprimes/paper/source/modules/global-positive-upper-completion-20261010.txt", "Upper 183-281 original quantifiers/errors/reserves"),
    (ROOT.parent / "1_+_1.748_lean_proofs/main.md", "Authoritative yellow-node tracker, not modified"),
]

all_modules = {p.stem: p for p, _ in reused}
all_modules.update({Path(n).stem: HERE / n for n in new_names})

def evidence(path, role):
    raw = path.read_bytes()
    lines = raw.decode("utf-8-sig").splitlines()
    item = {
        "path": path.as_posix(),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "bytes": len(raw),
        "line_count": len(lines),
        "role": role,
    }
    if path.suffix == ".lean":
        item["module"] = "ImbalancedChen." + path.stem
        item["imports"] = []
        item["declarations"] = []
        namespace = []
        for lineno, line in enumerate(lines, 1):
            m = re.match(r"^import\s+([\w.]+)\s*$", line)
            if m:
                module = m.group(1)
                target = all_modules.get(module.rsplit(".", 1)[-1])
                item["imports"].append({"module": module, "line": lineno,
                    "explicit_resolved_path": target.as_posix() if target else None,
                    "resolution_note": "exact cited source" if target else "not recursively resolved by this metadata packet"})
            m = re.match(r"^namespace\s+(\S+)", line)
            if m:
                namespace.append(m.group(1))
            m = re.match(r"^(?:private\s+)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+([^\s:{(]+)", line)
            if m:
                item["declarations"].append({"kind": m.group(1), "name": m.group(2),
                    "line": lineno})
        item["compiled"] = False
        item["kernel_verified"] = False
        item["finite_proof_bodies"] = "UNEVALUATED"
    return item

registry = {
    "packet": "S15",
    "assigned_node": "P4A.5 actual same-rho hdensity",
    "status": "ACTUAL_COMMON_SCHEDULE_AND_FINITE_POSITIVE_AND_SAFE_FIFTH_SOURCE_COMPLETE; FULL_NODE_HOLD",
    "whole_assigned_scope_source_complete": False,
    "compiled": False,
    "kernel_verified": False,
    "formal_credit": 0,
    "target_premises_removed": {"hdensity": 0, "hUniformPP": 0, "hUpper": 0},
    "actual_local_terminal": "ImbalancedChen.P4AActualJointDensitySchedule.exists_joint_original_density_schedule",
    "original_terminal": "P4BCurrentSmoothBadUpperSuppliers.current_realBad_upper_of_actual_density_and_uniform_smooth_PP.hdensity (lines 40-44)",
    "quantifier_order": "eta,eMax -> a0 -> any 0<a<=a0 -> e0 -> any rational 0<e<e0 -> qMin,mMin -> q0 -> all q>=q0 -> actual fallback m,buffer -> N0 -> every later even N",
    "actual_instance": "originalSchedule e q (e/20) a, original fourth byte bank and actual fifth indexed owners; m_old=475*q-1",
    "accounting": {
        "third": "Existing actual u_d/4 carried once; not included again in local catalogue",
        "local_total": "catalogFiveCapError + sum(indexedActualReserve64) < eta, each < eta/2",
        "safe_fifth": "Same reserve64 also < original exact fifth endpoint - 10051/1000000; S08 universal endpoint gives original safe integral on same schedule, no additional spend",
        "old_literal": "Separately bounded < eta/2, not added to local total or safe-fifth payment",
        "r07_r10": "Complete original small omission and two caps already paid; partial catalogues alternatives, not extra costs",
        "remaining_density": "Full other density catalogue still must fit 3*u_d/4",
        "compiler": "Independent complete u_c not supplied here",
    },
    "removed_local_hypotheses": [
        "R10 literal old-data width conditions discharged by S13 on same original schedule",
        "Independent existential e/q mismatch between reserve64 and catalogue supplier",
        "Arbitrary supplied bank envelope or actual reserve-smallness premise",
        "Stale coarse first/compact positive excess at actual finite positive endpoint",
        "OldBranchDefect at original fifth integral: consumed actual completed S08 proof, not zeroed or assumed small",
    ],
    "remaining_exact_obligations": [
        "Full87 actual current-parent/history and finite higher-cap realization on same policy",
        "All22 full signed source ledger and original endpoints on that realization",
        "Every remaining actual finite source/cap/wall/tail/attachment cost, once each, total <3u_d/4",
        "Complete source-specific changed/mixed compiler payment <u_c with same actual beta weights",
        "Final compiled general-coefficient handoff to existing same-rho counting/PP interface; no forced first-exit identity",
    ],
    "new_sources": [evidence(HERE / n, "new actual supplier/compatibility proof") for n in new_names],
    "reused_sources": [evidence(p, role) for p, role in reused],
    "context": [evidence(p, role) for p, role in context],
    "report": evidence(HERE / "REPORT.md", "scope, original target, actual terminals, remaining obligations and remote plan"),
    "metadata_generator": evidence(Path(__file__), "read-only byte/text metadata plus this registry write; no mathematical evaluation"),
    "independent_review": {"reviewer": "/root/s27_review_density", "narrow_source_review": "Initial radius/refinement, S13 refactor and finite-positive integration passed by message; final S08 small integration submitted", "kernel_evidence": None},
    "remote_plan": {"dispatcher": "root/S02 only", "lean": "leanprover/lean4:v4.33.0-rc1", "mathlib": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1", "native_upstream": "09b97db5764ade1246bfb77206baa1b124760958", "targets": ["ImbalancedChen." + Path(n).stem for n in new_names], "evidence_required": "exact source/dependency/toolchain hashes, successful elaboration/kernel and declaration axiom report; all imported finite candidates require actual remote evaluation"},
}
(HERE / "REGISTRY.json").write_text(json.dumps(registry, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"new_sources": len(registry["new_sources"]), "reused_sources": len(registry["reused_sources"]), "new_declarations": sum(len(x["declarations"]) for x in registry["new_sources"]), "whole_node_source_complete": False}))
