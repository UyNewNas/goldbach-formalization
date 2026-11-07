import ImbalancedChen.P5ActualFifthGateStripVolume

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
True source-index mass payment of the proper-affine rejected SUPPORT core.
The actual pointwise-invalid remainder is kept as its own measurable
region and cost. No desired full-bank trim bound is assumed or concluded.
-/
namespace ImbalancedChen.P5HistoricalRejectedCoreReserve
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthCorrelatedRawBoxGates P1OriginalFifthQuantitativeGateRefinement
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthLiteralKernelModulus
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P1OriginalFifthAdoptedOwnerBank P5HistoricalIndexedTrimGeometry
open P5ActualFifthGateStripLocalization P5ActualFifthGateStripVolume

theorem pointwiseSupport_measurable (I : Finset (Fin 5)) : MeasurableSet (pointwiseSupport I) := by
  have heq : pointwiseSupport I = ⋂ g : Gate,
      if gateAllowed I g = true then {t | (gateAffine I g).eval t < candidate 0 I t} else Set.univ := by
    ext t
    simp [pointwiseSupport]
  rw [heq]
  apply MeasurableSet.iInter
  intro g
  by_cases hg : gateAllowed I g = true
  · rw [if_pos hg]
    have ha : Continuous (fun t : Fin 5 → ℝ => (gateAffine I g).eval t) := by
      unfold Affine5.eval
      fun_prop
    have hc : Continuous (candidate 0 I) := by unfold candidate envelope; fun_prop
    exact measurableSet_lt ha.measurable hc.measurable
  · rw [if_neg hg]
    exact MeasurableSet.univ

theorem rejectedSupportCore_measurable (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    MeasurableSet (rejectedSupportCore i e q chi omega) :=
  (gateRejected_measurable i e q chi omega).inter (pointwiseSupport_measurable _)

theorem rejectedInvalidCore_measurable (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    MeasurableSet (rejectedInvalidCore i e q chi omega) :=
  (gateRejected_measurable i e q chi omega).diff (pointwiseSupport_measurable _)

theorem gateRejected_subset_unitCube (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    gateRejectedDomain i e q chi omega ⊆ unitCube := by
  intro t ht k _
  have hp := gateRejected_subset_parent i e q chi omega ht
  have hk := mem_logPrimeBox.mp hp.2 k
  exact ⟨hk.1, by linarith [hk.2]⟩

def supportCoreCost (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  rowMassBound (archiveRow i) * (volume (rejectedSupportCore i e q chi omega)).toReal

def invalidCoreCost (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  rowMassBound (archiveRow i) * (volume (rejectedInvalidCore i e q chi omega)).toReal

theorem gateRejectedCost_exact_core_split (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    gateRejectedCost i e q chi omega = supportCoreCost i e q chi omega + invalidCoreCost i e q chi omega := by
  have hunit : volume unitCube = 1 := by simp [unitCube, volume_pi_pi, Real.volume_Icc]
  have hfinite : volume (gateRejectedDomain i e q chi omega) < ∞ :=
    (measure_mono (gateRejected_subset_unitCube i e q chi omega)).trans_lt (by rw [hunit]; simp)
  have hs : volume (rejectedSupportCore i e q chi omega) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt hfinite).ne
  have hi : volume (rejectedInvalidCore i e q chi omega) ≠ ∞ :=
    ((measure_mono sdiff_subset).trans_lt hfinite).ne
  unfold gateRejectedCost supportCoreCost invalidCoreCost
  rw [rejectedDomain_exact_partition,
    measure_union (rejected_cores_disjoint i e q chi omega)
      (rejectedInvalidCore_measurable i e q chi omega), ENNReal.toReal_add hs hi, mul_add]

/-- No primitive source-key or precomputed pass is needed for this rate;
the actual rejected support core is inside the original compact ambient. -/
theorem supportCoreCost_le_actual_strip_rate (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e)
    (q : ℕ) (chi omega : ℝ) :
    supportCoreCost i e q chi omega ≤ rowMassBound (archiveRow i) *
      (88 * (2 * (e : ℝ) + 32 * (meshStepQ (refinedMesh q) : ℝ))) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hd : 0 ≤ 88 * (2 * (e : ℝ) + 32 * (meshStepQ (refinedMesh q) : ℝ)) := by
    have hh : (0 : ℝ) < (meshStepQ (refinedMesh q) : ℝ) := by exact_mod_cast meshStepQ_pos (refinedMesh q)
    positivity
  have hv := ENNReal.toReal_mono (by simp : ENNReal.ofReal
      (88 * (2 * (e : ℝ) + 32 * (meshStepQ (refinedMesh q) : ℝ))) ≠ ∞)
    (rejectedSupportCore_volume i e he q chi omega)
  rw [ENNReal.toReal_ofReal hd] at hv
  exact mul_le_mul_of_nonneg_left hv (by linarith [one_le_rowMassBound (archiveRow i)])

def sourceMassSum (S : Finset ArchiveIndex) : ℝ := ∑ i ∈ S, rowMassBound (archiveRow i)

def supportCoreBankCost (S : Finset ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ S, supportCoreCost i e q chi omega

def invalidCoreBankCost (S : Finset ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ S, invalidCoreCost i e q chi omega

/-- Finite source positions, including duplicates, are summed ONCE.
Taking S=univ gives the complete original292633-position support-core rate. -/
theorem supportCoreBankCost_le_actual_strip_rate (S : Finset ArchiveIndex)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ) :
    supportCoreBankCost S e q chi omega ≤ sourceMassSum S *
      (88 * (2 * (e : ℝ) + 32 * (meshStepQ (refinedMesh q) : ℝ))) := by
  calc
    _ ≤ ∑ i ∈ S, rowMassBound (archiveRow i) *
        (88 * (2 * (e : ℝ) + 32 * (meshStepQ (refinedMesh q) : ℝ))) :=
      Finset.sum_le_sum (fun i _ => supportCoreCost_le_actual_strip_rate i e he q chi omega)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem supportCoreBankCost_le_linear_buffer (S : Finset ArchiveIndex)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    supportCoreBankCost S e q chi omega ≤ 352 * sourceMassSum S * (e : ℝ) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hs : 0 ≤ sourceMassSum S :=
    Finset.sum_nonneg (fun i _ => by linarith [one_le_rowMassBound (archiveRow i)])
  have hh : (meshStepQ (refinedMesh q) : ℝ) ≤ (e : ℝ) / 20 := by
    simpa only [cast_meshStepQ] using hstep
  have hrate : 88 * (2 * (e : ℝ) + 32 * (meshStepQ (refinedMesh q) : ℝ)) ≤ 352 * (e : ℝ) := by linarith
  exact (supportCoreBankCost_le_actual_strip_rate S e he q chi omega).trans
    ((mul_le_mul_of_nonneg_left hrate hs).trans_eq (by ring))

theorem gateRejectedBankCost_exact_core_split (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    gateRejectedBankCost e q chi omega =
      supportCoreBankCost licensedIndices e q chi omega + invalidCoreBankCost licensedIndices e q chi omega := by
  unfold gateRejectedBankCost supportCoreBankCost invalidCoreBankCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => gateRejectedCost_exact_core_split i e q chi omega)

/-- Only the true proper-affine support part has been paid. The original
canonical margin residue and pointwise-invalid source core stay explicit.
Parameter aggregation may absorb the displayed linear rate into B13's
continuous envelope; no old B13 statement is applied to a new parent. -/
theorem actual_licensedTrimCost_le_unpaid_cores_add_buffer_rate
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10) (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400)
    (hstepE : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20) :
    licensedTrimCost e q chi omega ≤ residualCanonicalTrim e q chi omega +
      invalidCoreBankCost licensedIndices e q chi omega + 352 * sourceMassSum licensedIndices * (e : ℝ) := by
  rw [actual_licensedTrimCost_eq_two_geometric_residuals e he hemax chi omega hchi q hq hstep hw,
    gateRejectedBankCost_exact_core_split]
  have hrate := supportCoreBankCost_le_linear_buffer licensedIndices e he.le q chi omega hstepE
  linarith

end
end ImbalancedChen.P5HistoricalRejectedCoreReserve
