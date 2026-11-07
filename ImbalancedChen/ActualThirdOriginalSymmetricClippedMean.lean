import ImbalancedChen.ActualThirdOriginalSymmetricJensenLeaf
import ImbalancedChen.ActualThirdOriginalFixedpointClippedChord

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30.
Attach after the reviewed symmetric-Jensen V2 module and fixedpoint-clipped-chord
module. This is one candidate, before mass interval/ceil and all-min/tree closure. -/
namespace ImbalancedChen.OriginalThirdSymmetricClippedMeanSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdClippedChordSourceOnly

/-- The exact real OLD weight underlying the producer's pre-clipping interval. -/
def oldWeight (a b c d : ℝ) : ℝ :=
  (oldMean a b c d-oldLow b d)/(oldHigh a c-oldLow b d)

/-- This range is derived from the actual ordered-prism geometry and the proved
ordered moments. It is not an assumption about a rounded mean or leaf allowance. -/
theorem actual_oldMean_mem_range {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : VariableEnvelope.mu≤a) :
    oldMean a b c d ∈ Icc (oldLow b d) (oldHigh a c) := by
  have hc : 0<c := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) hg.cutoff
  have ha : 0<a := hc.trans_le (hg.width_z.le.trans hg.z_below_xy)
  let := prismProbability_isProbability ha hg.width_xy hc hg.width_z
  have hmem : ∀ᵐ p ∂prismProbability a b c d, p∈prismRegion a b c d := by
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem ((measurableSet_xyTriangle a b).prod measurableSet_Icc))
  have hr : ∀ᵐ p ∂prismProbability a b c d,
      prismAffine (57/64) (-(5/2)) (-1) (-1) p∈Icc (oldLow b d) (oldHigh a c) := by
    filter_upwards [hmem] with p hp
    exact (actual_prism_old_minorant_range hg hmu hp).2
  have hm : Measurable (prismAffine (57/64) (-(5/2)) (-1) (-1)) := by
    unfold prismAffine
    fun_prop
  have hi : Integrable (prismAffine (57/64) (-(5/2)) (-1) (-1))
      (prismProbability a b c d) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (|oldLow b d|+|oldHigh a c|)
    filter_upwards [hr] with p hp
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (oldLow b d),abs_nonneg (oldHigh a c),hp.1]
    · linarith [le_abs_self (oldHigh a c),abs_nonneg (oldLow b d),hp.2]
  have heq : (∫ p, prismAffine (57/64) (-(5/2)) (-1) (-1) p
      ∂prismProbability a b c d)=oldMean a b c d := by
    rw [prism_affine_mean hg]
    unfold oldMean minMean
    ring
  have hlo := integral_mono_ae (integrable_const (oldLow b d)) hi
    (hr.mono (fun _ h=>h.1))
  have hhi := integral_mono_ae hi (integrable_const (oldHigh a c))
    (hr.mono (fun _ h=>h.2))
  rw [heq] at hlo hhi
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hlo hhi
  exact ⟨hlo,hhi⟩

/-- Clipping to [0,1] is justified by the true OLD weight. -/
theorem actual_oldWeight_mem_unit {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : VariableEnvelope.mu≤a)
    (hspan : oldLow b d<oldHigh a c) : oldWeight a b c d ∈ Icc 0 1 := by
  have hr := actual_oldMean_mem_range hg hmu
  have hs := sub_pos.mpr hspan
  constructor
  · exact div_nonneg (sub_nonneg.mpr hr.1) hs.le
  · apply (div_le_iff₀ hs).2
    linarith [hr.2]

/-- One original mean_upper candidate, in original P160 integer units.
The raw weight enclosure hwtlo/hwthi is the precise still-separate interval-
arithmetic dependency for (old-low)/(high-low). No target integral bound,
minimum-of-candidates bound, or node/query soundness is assumed here.
The NEW rational argument is outward rounded via hnew; its query and the two
OLD endpoint queries supply hquery/hfl/hfh. -/
theorem original_symmetric_clipped_mean_candidate
    {a b c d : ℝ} {l u fl fh out : ℤ} {qnew : ℚ}
    (hg : SymmetricFullBox a b c d) (hmu : VariableEnvelope.mu≤a)
    (hlo : 2≤oldLow b d) (hspan : oldLow b d<oldHigh a c)
    (hwtlo : value l≤oldWeight a b c d) (hwthi : oldWeight a b c d≤value u)
    (hfl : value fl≤actualExtendedThirdLowerFactor (oldLow b d))
    (hfh : value fh≤actualExtendedThirdLowerFactor (oldHigh a c))
    (hnew : newMean a b c d≤(qnew:ℝ))
    (hquery : actualExtendedThirdLowerFactor (qnew:ℝ)≤value out) :
    (∫ t in compactRegion ∩ symmetricBox a b c d, compactKernel t)≤
      prismMass a b c d*value (meanHigh l u fl fh out) := by
  have hw := actual_oldWeight_mem_unit hg hmu hspan
  have hround := meanHigh_sound (fl:=fl) (fh:=fh) (out:=out) hw.1 hw.2 hwtlo hwthi
  have hc : max 0 (value out-symmetricChordMean a b c d (value fl) (value fh))≤
      value (meanHigh l u fl fh out) := by
    simpa only [symmetricChordMean,oldWeight] using hround
  have hout := symmetric_new_upper_of_query a b c d qnew (value out) hnew hquery
  have ha := original_symmetric_above_mu_leaf_upper hg hmu hlo hspan hfl hfh hout
  have hp : 0<c := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) hg.cutoff
  have hpa : 0<a := hp.trans_le (hg.width_z.le.trans hg.z_below_xy)
  have hmass : 0≤prismMass a b c d := by
    exact (mul_pos (mul_pos (by norm_num) (triangleMass_pos hpa hg.width_xy))
      (div_pos (sub_pos.mpr hg.width_z) (mul_pos hp (hp.trans hg.width_z)))).le
  exact ha.trans (mul_le_mul_of_nonneg_left hc hmass)

end
end ImbalancedChen.OriginalThirdSymmetricClippedMeanSourceOnly
