"""Raw source receipts only: no proof execution, imports, guards or numerics."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OWN = [
    "P4AActualOwnCubeCapPayment.lean",
    "P4AActualBufferedFallbackCapPayment.lean",
    "P4AActualLocalDensityCatalogue.lean",
    "P4AActualSmallTailDensityCatalogue.lean",
    "P4AActualCompleteCatalogFiveCapPayment.lean",
]
IMPORTS = {
    "ImbalancedChen.P1VariableOwnCubeResidualUniformity": "ImbalancedChen/P1VariableOwnCubeResidualUniformity.lean",
    "ImbalancedChen.ActualExtendedThirdLowerFactorRegularity": "ImbalancedChen/ActualExtendedThirdLowerFactorRegularity.lean",
    "Mathlib.Topology.UniformSpace.HeineCantor": ".lake/packages/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean",
    "ImbalancedChen.P4AOriginalBufferedFallbackCaps": "docs/source-only/20261102-resume-30q/buffered_policy/P4AOriginalBufferedFallbackCaps.lean",
    "ImbalancedChen.P4AAll22OriginalKLedger": "ImbalancedChen/P4AAll22OriginalKLedger.lean",
    "ImbalancedChen.P4ACatalogFiveCoarseWeightedPayment": "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveCoarseWeightedPayment.lean",
    "ImbalancedChen.P4ACatalogFiveHistoricalPairBoundaryPayment": "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveHistoricalPairBoundaryPayment.lean",
    "ImbalancedChen.P4ACatalogFiveGlobalLossReduction": "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveGlobalLossReduction.lean",
    "ImbalancedChen.P4ACatalogFiveSmallThirdPayment": "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveSmallThirdPayment.lean",
    "ImbalancedChen.P4AOriginalBufferedArchiveContinuation": "docs/source-only/20261102-resume-30r/full_buffered_policy/P4AOriginalBufferedArchiveContinuation.lean",
}
for name in OWN:
    IMPORTS["ImbalancedChen." + Path(name).stem] = (HERE / name).relative_to(ROOT).as_posix()

def receipt(path, module=None):
    p = ROOT / path
    item = {"path": path, "exists": p.is_file()}
    if module is not None:
        item["module"] = module
    if not p.is_file():
        item["raw_sha256"] = None
        return item
    raw = p.read_bytes()
    text = raw.decode("utf-8-sig")
    item.update(bytes=len(raw), raw_sha256=hashlib.sha256(raw).hexdigest())
    if p.suffix == ".lean":
        item.setdefault("module", "ImbalancedChen." + p.stem)
        item["imports"] = re.findall(r"^import\s+(\S+)", text, re.M)
        item["declarations"] = [
            {"line": n, "kind": m[2], "name": m[3], "private": bool(m[1])}
            for n, line in enumerate(text.splitlines(), 1)
            if (m := re.match(r"^(private )?(theorem|def|abbrev)\s+(\S+)", line))
        ]
    return item

new_sources = [receipt((HERE / p).relative_to(ROOT).as_posix(), "ImbalancedChen." + Path(p).stem) for p in OWN]
direct = sorted({m for src in new_sources for m in src["imports"]})
direct_receipts = []
for module in direct:
    item = receipt(IMPORTS[module], module)
    target = module.replace(".", "/") + ".lean"
    item["logical_installation_target"] = target
    item["at_logical_installation_target"] = (ROOT / target).is_file()
    item["verification_inherited"] = False
    direct_receipts.append(item)

references = [
    "docs/source-only/20261102-resume-30r/BRIEF.md",
    "docs/source-only/20261102-resume-30r/DISPATCH.json",
    "docs/source-only/20261102-resume-30r/r01_reuse_archive_policy/FOLLOWUP.md",
    "docs/source-only/20261102-resume-30q/buffered_policy/REPORT.md",
    "docs/source-only/20261102-resume-30q/buffered_policy/REGISTRY.json",
    "docs/source-only/20261102-resume-30q/q03_original_gap_triage/NEXT_DIRECT_PROOF_REVIEW.md",
    "docs/source-only/20261102-resume-30q/reviews/q30_review_history_final.md",
    "../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex",
    "../chen-imbalanced-semiprimes/paper/source/modules/global-positive-upper-completion-20261010.txt",
    "ImbalancedChen/ActualPrimeBoxOwnCubeResidual.lean",
    "ImbalancedChen/ActualPrimeBoxMass.lean",
    "ImbalancedChen/ActualExtendedThirdOrderedIntegral.lean",
    "ImbalancedChen/ActualExtendedThirdCompactKernelApproximation.lean",
    "ImbalancedChen/ActualUpperDensityAssembly.lean",
    "ImbalancedChen/ActualFirstExitDensityProjection.lean",
    "ImbalancedChen/P4AAll22ActualCompactPositiveBinding.lean",
    "ImbalancedChen/Part4ActualThirdFiniteDensityReserve.lean",
    "ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean",
    "docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean",
    "docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalFourteenThirteenCurrentSource.lean",
    "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveOmittedOrderPayment.lean",
    "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveSmallThirdMass.lean",
    "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveSmallThirdEndpointTail.lean",
    "docs/source-only/20261102-resume-30r/fifth_reserve64/P5HistoricalActualReserve64Schedule.lean",
    "docs/source-only/20261102-resume-30r/full_buffered_policy/P4AHeldTaggedCompilerSupport.lean",
    "docs/source-only/20261102-resume-30r/compiler_reserve/P4AUpperTaggedFrozenAdmissionCatalogue.lean",
    "docs/source-only/20261102-resume-30r/compiler_reserve/P4AHeldTaggedFiniteAdmissionPayment.lean",
]
registry = {
    "task": "R10 / D08 actual_density_reserve",
    "date": "2026-11-02",
    "status": "COMPLETE_DISPLAYED_CATALOGUE5_AND_CAP_PAYMENT; full remaining 3*u_d/4 and same-rho hdensity HOLD",
    "compiled": False,
    "kernel_verified": False,
    "formal_credit": 0,
    "finite_bodies": "UNEVALUATED",
    "verification": "Static mathematical/source reading and raw bytes/declaration/import metadata only",
    "new_sources": new_sources,
    "direct_import_resolution": direct_receipts,
    "transitive_dependency_closure_claimed": False,
    "reference_receipts": [receipt(p) for p in references],
    "report": receipt((HERE / "REPORT.md").relative_to(ROOT).as_posix()),
    "metadata_helper": receipt((HERE / "write_registry.py").relative_to(ROOT).as_posix()),
    "peer_consumed_declarations": [
        "ImbalancedChen.P4ACatalogFiveCoarseWeightedPayment.exists_complete_coarseRow_payment",
        "ImbalancedChen.P4ACatalogFiveHistoricalPairBoundaryPayment.exists_historical_endpoint_approx_integral",
        "ImbalancedChen.P4ACatalogFiveGlobalLossReduction.exists_actual_saving_approx_with_small_omission",
        "ImbalancedChen.P4ACatalogFiveSmallThirdPayment.exists_complete_actual_catalog5_approx",
        "ImbalancedChen.P4AOriginalBufferedArchiveContinuation.original_archives_two_signed_gains",
    ],
    "eliminated_local_obligations": [
        "Canonical profile cap modulus for every nonempty prefix rank, without assuming a modulus",
        "Weighted actual own-cube cap difference on all later subsets/cap tables, without assuming their error",
        "One Q22 finite m/buffer paying both concrete selectedThird fallback cap defects",
        "Common N0 for actual coarseRow, historical endpoint and fallback cap partial catalogue",
        "Original fourth/fifth complete signed-gain preservation on those same witnesses, supplied by R08",
        "Alternative actual catalogue-five-plus-cap comparison, including paid compact order omission and retaining the explicit smallOmittedSum",
        "Complete actual catalogue-five-plus-cap error <eta after a0(eta), directly consuming R07's full-List small-third payment; no unpaid local tail or new gap premise",
    ],
    "true_premises": [
        "Positive requested error; latest terminal supplies a0 first, then accepts any positive cutoff a<=a0<19/96",
        "Actual old source buffer and mesh restrictions; latest complete terminal uses omega=a",
        "Generic fixed-rank cap comparison uses actual cap range and cap closeness, not a density-error premise",
        "Sufficiently large even N and a covering enumeration cap",
    ],
    "remaining_dependencies": [
        "Full87 frozen finite higher-cap construction and exact source/density binding",
        "All four sharp actual positive endpoints and all 22 same-policy saving increments",
        "Other full-policy source/tail/wall/higher-cap costs beyond the paid catalogue-five-plus-cap quantity",
        "Fifth old Jensen/Taylor defect and compatible accounting of R05's distinct child and literal errors",
        "Whole same-rho compiler coverage/payment <u_c from R09",
        "Complete total remaining density cost <3*u_d/4 on the actual final attached coefficient",
        "Installation, elaboration and independent kernel verification",
    ],
    "budget": {
        "existing_third": "u_d/4, unchanged and not included in localDensityError",
        "cap_only_available_allocation": "<u_d/8 on the defined Q22 compact residual defects",
        "joint_local_catalogue": "arbitrary eta, three proved components at eta/3 once each",
        "earlier_tail_reduced_catalogue": "R07 actual saving error eta/2 (three shares eta/6) plus two R10 cap errors eta/2 (two shares eta/4); that earlier theorem retains smallOmittedSum",
        "complete_catalogue5_cap_payment": "R07 complete actual catalogue-five source including small-third eta/2 once, plus two R10 cap defects eta/4 each; catalogFiveCapError<eta",
        "catalogue_overlap": "The local, tail-reduced and complete catalogue-five/cap conclusions are alternatives, never added together",
        "compiler": "u_c independent; no R10 expenditure",
        "full_remaining_density_status": "HOLD; no closed global balance claimed",
    },
    "new_axioms": [],
    "new_external_assumptions": [],
    "goal_equivalent_hypotheses": [],
    "terminal_hdensity_premises_removed": 0,
    "complete_local_terminal": "ImbalancedChen.P4AActualCompleteCatalogFiveCapPayment.exists_original_archive_complete_catalog5_cap_payment",
    "complete_local_parameter_order": "eta -> a0 -> a -> delta -> original e,q,chi,omega -> m,buffer -> N0 -> N",
    "catalogue5_small_tail_dependency_removed": True,
    "manuscript_locations": ["Body:451-509", "Upper:175-242", "Upper:259-281"],
}
(HERE / "REGISTRY.json").write_text(json.dumps(registry, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"registry": str(HERE / "REGISTRY.json"), "sources": [{"path": p["path"], "sha256": p["raw_sha256"]} for p in new_sources]}, ensure_ascii=False))
