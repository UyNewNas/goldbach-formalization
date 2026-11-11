import ImbalancedChen
import Lean.Util.CollectAxioms

/-! Round 3 type export after the full root build.
This reuses the verified LongSlotAudit defining-module inventory and checks.
The original eight-module 198-name census is retained exactly; 39 declarations
now owned by FinitePrimeGeometryCore are mapped by the recorded migration.
The complete new core is additionally audited by Round6Audit.
The existing final bridge is printed separately with all its analytic hypotheses.
Compiling this audit does not rebuild or replay any production module. -/

set_option pp.all true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required : Array (Name × Name) := #[
    (`ImbalancedChen.actualSelectedPrefixLowerOwnCubeSum_eq_cells, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.ordinaryLowerFourFrontierTuples_cell_filter, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.ordinaryLowerFourFrontierTuples_cell_filter._simp_1_1, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.ordinaryLowerFourFrontierTuples_cell_filter._simp_1_2, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.ordinaryLowerFourFrontierTuples_cube_filter, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.ordinaryLowerFourFrontierTuples_cube_filter._simp_1_1, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.ordinaryLowerFourFrontier_cell_ownCube_difference, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.ordinaryLowerFourFrontier_cell_ownCube_difference._simp_1_1, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.ordinaryLowerFourFrontier_cell_weighted_sum, `ImbalancedChen.ActualSelectedPrefixLowerCellSum),
    (`ImbalancedChen.actualSelectedPrefixLowerDensity, `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral),
    (`ImbalancedChen.actualSelectedPrefixLowerDensity.eq_1, `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral),
    (`ImbalancedChen.selectedPrefixLowerRestorationIntegral, `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral),
    (`ImbalancedChen.selectedPrefixLowerRestorationIntegral_eq_integrals, `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral),
    (`ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_ceil_normalized, `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral),
    (`ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_normalized, `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral),
    (`ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_restoration, `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral),
    (`ImbalancedChen.tendsto_actualSelectedPrefixLowerOwnCubeSum, `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral),
    (`ImbalancedChen.Certificates.PairedV2.E0Geometry, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.E0Geometry.cutoff_bound, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.E0Geometry.fibre_argument, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.E0Geometry.fibre_nonempty, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.E0Geometry.residual_bound, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.e0GeometryCheck, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.e0GeometryCheck_fibre_argument, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.e0GeometryCheck_sound, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.instDecidableE0Geometry, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.openFibreSupport, `ImbalancedChen.Certificates.PairedV2Geometry),
    (`ImbalancedChen.Certificates.PairedV2.E0Geometry.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate_inputs, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificates.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificates_checked, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.fibre_argument, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.fibre_nonempty, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.geometry_checked, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.integral, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.integral.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.integral_bounds, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.integral_bounds._simp_1_2, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.integral_pos, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.integral_semantics, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.lower_sum, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.row0000_checked, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.row0001_checked, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.row0002_checked, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.row0003_checked, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral_eq_certificate, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound.eq_1, `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.upper_sum, `ImbalancedChen.Certificates.PairedV2Prefix4),
    ((Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.Certificates.PairedV2Prefix4 0) "ImbalancedChen") "Certificates") "PairedV2") "Prefix4") "rowIndices") "match_1") "eq_1"), `ImbalancedChen.Certificates.PairedV2Prefix4),
    ((Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.Certificates.PairedV2Prefix4 0) "ImbalancedChen") "Certificates") "PairedV2") "Prefix4") "rowIndices") "match_1") "eq_2"), `ImbalancedChen.Certificates.PairedV2Prefix4),
    ((Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.Certificates.PairedV2Prefix4 0) "ImbalancedChen") "Certificates") "PairedV2") "Prefix4") "rowIndices") "match_1") "eq_3"), `ImbalancedChen.Certificates.PairedV2Prefix4),
    ((Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.Certificates.PairedV2Prefix4 0) "ImbalancedChen") "Certificates") "PairedV2") "Prefix4") "rowIndices") "match_1") "eq_4"), `ImbalancedChen.Certificates.PairedV2Prefix4),
    ((Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.Certificates.PairedV2Prefix4 0) "ImbalancedChen") "Certificates") "PairedV2") "Prefix4") "rowIndices") "match_1") "splitter"), `ImbalancedChen.Certificates.PairedV2Prefix4),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.certificates, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowOrdinal, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound, `ImbalancedChen.Certificates.PairedV2Prefix4Data),
    (`ImbalancedChen.HistoricalPrefixCapData, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData._sizeOf_1, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData._sizeOf_inst, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.a, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.actual_thirdToFifthSaving_eq, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.actual_thirdToFifthSaving_eq._proof_1_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.b, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.cap3, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.cap4, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.cap5, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.casesOn, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.cell3, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.cell4, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.cell5, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.cells3, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.cells4, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.cells5, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.ctorIdx, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent3, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent3_le_exponent4, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent3_on_cell, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent3_outside, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent4, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent4.eq_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent4_apply_sub, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent4_le_exponent5, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent4_on_cell, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent4_outside, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent5, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent5.eq_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent5_apply_sub, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent5_on_cell, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.exponent5_outside, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level3, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.level3_ancestor_le_level4, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level3_ancestor_le_level4._proof_1_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level3_outside, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level4, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level4_ancestor_le_level5, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level4_ancestor_le_level5._proof_1_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level4_outside, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level4_outside._proof_1_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level5, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level5_outside, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.level5_outside._proof_1_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.levelCheck, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.levelCheck.eq_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.levelCheck_of_selectedBoxCapChecks, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.levelCheck_sound, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.m, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.mk, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.mk._flat_ctor, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.mk.inj, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.mk.injEq, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.mk.noConfusion, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.mk.sizeOf_spec, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.noConfusion, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.noConfusionType, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.old, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.old4, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.old4._proof_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.old4._proof_2, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.old5, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.old5._proof_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.old5._proof_2, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.old_le_exponent3, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.rec, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.recOn, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy.eq_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy_eq_oddFirstExitPolicy, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy_even, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy.eq_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy_even, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy.eq_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy_even, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.HistoricalPrefixCapData.upperThirdToFifthSaving_eq, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.fifthCappedUpperPolicy.eq_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.fourthCappedUpperPolicy.eq_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.historicalPrefixAncestorCell_unique, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.historicalPrefixLookup, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.historicalPrefixLookup_apply_sub, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.historicalPrefixLookup_apply_sub._simp_1_1, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.historicalPrefixLookup_apply_sub._simp_1_2, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.historicalPrefixLookup_ge_fallback, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.historicalPrefixLookup_on_any_cell, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.historicalPrefixLookup_on_cell, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.historicalPrefixLookup_outside, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.historicalPrefixProject, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.historicalPrefixProject.congr_simp, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.historicalPrefixProject.eq_1, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.historicalPrefixProject_comp, `ImbalancedChen.HistoricalPrefixCertificate),
    (`ImbalancedChen.mem_logPrimeMeshCell_historicalPrefixProject, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.primeHistoryLogCoordinates_eq_historicalPrefixProject, `ImbalancedChen.FinitePrimeGeometryCore),
    (`ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff_log, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff_of_cutoff_le_cap, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.mem_ordinaryLowerFourGateRegion, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.mem_ordinaryLowerFourGateRegion._simp_1_3, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.mem_ordinaryLowerFourGateRegion._simp_1_4, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateBounds, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateBounds.eq_1, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateForms, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateForms._proof_1, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateForms._proof_2, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateForms._proof_3, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateForms._proof_4, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateForms._proof_5, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateForms.eq_1, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFourGateForms_ne_zero, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFour_cube_test_iff_log, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryLowerFour_parent_valid_iff, `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.ordinaryRosserPrefixAdmissible_lower_two_iff, `ImbalancedChen.OrdinaryLowerFourFrontier),
    ((Name.str (Name.str (Name.num `_private.ImbalancedChen.OrdinaryLowerFourFrontier 0) "ImbalancedChen") "lowerRosserAdmissibleSet_two_iff"), `ImbalancedChen.OrdinaryLowerFourFrontier),
    ((Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.OrdinaryLowerFourFrontier 0) "ImbalancedChen") "lowerRosserAdmissibleSet_two_iff") "_proof_1_4"), `ImbalancedChen.OrdinaryLowerFourFrontier),
    ((Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.OrdinaryLowerFourFrontier 0) "ImbalancedChen") "lowerRosserAdmissibleSet_two_iff") "_proof_1_5"), `ImbalancedChen.OrdinaryLowerFourFrontier),
    ((Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.OrdinaryLowerFourFrontier 0) "ImbalancedChen") "lowerRosserAdmissibleSet_two_iff") "_simp_1_1"), `ImbalancedChen.OrdinaryLowerFourFrontier),
    ((Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.OrdinaryLowerFourFrontier 0) "ImbalancedChen") "lowerRosserAdmissibleSet_two_iff") "_simp_1_2"), `ImbalancedChen.OrdinaryLowerFourFrontier),
    ((Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.OrdinaryLowerFourFrontier 0) "ImbalancedChen") "lowerRosserAdmissibleSet_two_iff") "_simp_1_3"), `ImbalancedChen.OrdinaryLowerFourFrontier),
    ((Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.OrdinaryLowerFourFrontier 0) "ImbalancedChen") "lowerRosserAdmissibleSet_two_iff") "_simp_1_6"), `ImbalancedChen.OrdinaryLowerFourFrontier),
    ((Name.str (Name.str (Name.str (Name.num `_private.ImbalancedChen.OrdinaryLowerFourFrontier 0) "ImbalancedChen") "lowerRosserAdmissibleSet_two_iff") "_simp_1_7"), `ImbalancedChen.OrdinaryLowerFourFrontier),
    (`ImbalancedChen.part3_eventually_longSlot_logAccuracy, `ImbalancedChen.Part3LongSlotNormalization),
    (`ImbalancedChen.part3_eventually_longSlot_singularNormalization, `ImbalancedChen.Part3LongSlotNormalization)]
  let modules := required.foldl (fun ms entry => if ms.contains entry.2 then ms else ms.push entry.2) (#[] : Array Name)
  let finalBridge := `ImbalancedChen.current_theorem_1_1_of_manuscript_bounds
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := required.map (·.1)
  for (name, owner) in required do
    let some idx := env.getModuleIdxFor? name | throwError "Missing original Round 3 declaration {name}"
    unless env.header.moduleNames[idx]! == owner do
      throwError "Wrong migrated defining module for {name}"
  let originalModules := modules.filter (· != `ImbalancedChen.FinitePrimeGeometryCore)
  let discovered := env.constants.fold (init := #[]) fun found name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if originalModules.contains env.header.moduleNames[idx]! || names.contains name then
        found.push name
      else found
    | none => found
  unless discovered.qsort Name.lt == names.qsort Name.lt do
    throwError "Original Round 3 census plus exact migrated names differs from original 198"
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in (names.push finalBridge).qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in a P0 batch module: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in a P0 batch module: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let idx := (env.getModuleIdxFor? name).get!
    let moduleName := env.header.moduleNames[idx]!
    counts := counts.map fun (m, count) => (m, if m == moduleName then count + 1 else count)
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let type ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let readableType ← liftTermElabM do
      withOptions (fun opts => (opts.setBool `pp.all false).setBool `pp.explicit false) do
        return (← Meta.ppExpr info.type).pretty
    if type.contains '⋯' || readableType.contains '⋯' then
      throwError "Truncated compiler type for {name}"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    if name == finalBridge then
      liftIO <| IO.println s!"P0_ROUND3_FINAL_BRIDGE {record.compress}"
    else
      liftIO <| IO.println s!"P0_ROUND3_DECL {record.compress}"
  for (m, count) in counts do
    let wanted := required.foldl (fun n entry => if entry.2 == m then n + 1 else n) 0
    unless count == wanted do
      throwError "Round 3 declaration count mismatch for {m}: expected {wanted}, got {count}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P0_ROUND3_MODULE {record.compress}"
  unless names.size == 198 do
    throwError "Round 3 total declaration count mismatch: expected 198, got {names.size}"
  liftIO <| IO.println s!"P0_ROUND3_COUNT {names.size}"
