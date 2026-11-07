import ImbalancedChen.P5FullArchiveOwnerIntegralAssembly
import ImbalancedChen.P1ActualVariableFifthPhysicalIntegralTransfer

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_CREDIT.
Consumers use existing independently defined common literal charge and
the production counting coefficient. The old-branch and strict-owner
reserves are never assumed small or discarded. Each parent still has its
original64 children. No numerical sum, checker or compilation was run.
-/
namespace ImbalancedChen.P5FullStoredSavingPhysicalConsumers
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1HistoricalFifthIndexedOwnerArchive
open P5HistoricalMask56FullSourceChildren P5FullStoredParentSameOwnerBinding
open P5FullArchiveOwnerIntegralAssembly P5OriginalFifthArchiveActualMean
open P5OriginalFifthArchiveFiniteIdentity
open P1OriginalFifthMovingScaleLimit

/-- One threshold on ALL even targets, for the actual common finite
charge and fixed source parameters. Neither the desired charge bound nor
the archive mean is supplied as a premise. -/
theorem eventually_common_charge_ge_full_stored_minus_defects
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in evenTargets,
      (∑ i ∈ mask56Indices, (storedNewQ i : ℝ)) -
        (∑ i ∈ mask56Indices, (oldBranchDefectQ i : ℝ)) -
        (∑ i ∈ mask56Indices, indexedActualReserve64 i e q chi omega) - eta ≤
      commonLiteralCharge rows4 licensed4 e q chi omega N (cap N)
        ((N : ℝ) ^ (19 / 96 : ℝ)) := by
  have hfloor := full_stored_minus_defects_le_archiveFifthIntegral
    e he q chi omega hw hwr rows4 licensed4 hgeometry
  filter_upwards [eventually_commonLiteralCharge_error rows4 licensed4 e he q chi omega
    hw hwr cap hcap eta heta] with N hN
  have hlow := (abs_lt.mp hN).1
  linarith

/-- The physical coefficient is the original counting coefficient itself.
The one attachment epsilon is chosen BEFORE the source buffer/mesh/bank.
The true fourth integral stays in the ledger; the fifth integral is now
paid by the stored archive minus exactly the two explicit defects.

This is an original-variable-policy statement. The preceding theorem is
the separately justified common-charge statement; neither asserts an
unproved global equality of the two complete physical policies.
-/
theorem exists_attached_density_le_third_sub_full_stored_saving
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax)
    (hrho : nu * r = (19 / 96 : ℝ)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ^ 2 ≤ r ∧
      ∀ (e : ℚ), 0 ≤ e → ∀ (q : ℕ) (chi omega : ℝ),
      0 < omega → omega < (19 / 96 : ℝ) →
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 →
      ∀ (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop),
      (∀ row ∈ rows4, licensed4 row → row.Geometry) → ∀ (cap : ℕ → ℕ),
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      ∀ᶠ N : ℕ in evenTargets,
        physicalDensitySum
            (attachedUpperModuli nu r epsilon
              (fun N => P1OriginalVariableFifthContinuation.policy5 e chi (refinedMesh q) omega
                (N : ℝ) rows4 licensed4 (globalOwners e q chi omega) (licensedRows e q chi omega) false)
              cap N)
            (attachedUpperCoefficient nu r epsilon
              (fun N => P1OriginalVariableFifthContinuation.policy5 e chi (refinedMesh q) omega
                (N : ℝ) rows4 licensed4 (globalOwners e q chi omega) (licensedRows e q chi omega) false)
              cap N) * Real.log (N : ℝ) / singularSeries N ≤
          P1OriginalFourthFifthTotalTupleSource.originalThirdRetained
              e chi (refinedMesh q) omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) *
              Real.log (N : ℝ) / singularSeries N -
            P1OriginalVariableFourthFullActiveIntegral.fullActiveIntegral
              e chi (refinedMesh q) omega rows4 licensed4 -
            (∑ i ∈ mask56Indices, (storedNewQ i : ℝ)) +
            (∑ i ∈ mask56Indices, (oldBranchDefectQ i : ℝ)) +
            (∑ i ∈ mask56Indices, indexedActualReserve64 i e q chi omega) + eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, hsupply⟩ :=
    P1ActualVariableFifthPhysicalIntegralTransfer.exists_attached_normalized_le_originalThird_sub_totalIntegral
      nu r eta epsilonMax hnu hr heta hepsilonMax hrho
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, ?_⟩
  intro e he q chi omega hw hwr hmesh rows4 licensed4 hgeometry cap hcap
  have hfloor := full_stored_minus_defects_le_archiveFifthIntegral
    e he q chi omega hw hwr rows4 licensed4 hgeometry
  filter_upwards [hsupply e he chi (refinedMesh q) omega hw hwr hmesh rows4 licensed4
    (globalOwners e q chi omega) (licensedRows e q chi omega) cap hcap] with N hN
  dsimp only [P1ActualVariableFifthPhysicalIntegralTransfer.totalIntegral] at hN
  dsimp only [archiveFifthIntegral] at hfloor
  linarith

end
end ImbalancedChen.P5FullStoredSavingPhysicalConsumers
