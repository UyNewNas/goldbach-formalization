import ImbalancedChen.P2LowerActualL6FiniteKnotMass
import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapCompiler

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Actual cell-static native D,Z are bound to their logarithmic query and to
the original clamped residual by an explicit geometric error. No native
rho mean or H248 semantic licence is inferred from this dictionary. -/

namespace ImbalancedChen.P2UpperActualCompiledQueryBuffer

noncomputable section
open scoped Classical BigOperators
open Set
open P5Z U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy selectedPolicy ownerBox tupleTag)
open P5U1011JointOverlap

private abbrev a : ℝ := 417 / 5000
private abbrev d : ℝ := 59 / 250

def idealQuery (n N : ℕ) (t : Four) : ℝ :=
  max 2 (typedResidual (selectedPolicy n N t) (coordinates N t) /
    coordinates N t 3)

def compiledQuery (n N : ℕ) (eta : ℚ) (t : Four) : ℝ :=
  Real.log (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) / Real.log (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)

def boxBuffer (p : Policy) (B : Box) (eta : ℚ) : ℝ :=
  (5 / 2 : ℝ) * U1011OriginalSixteenNearCapBoxProfiles.diameter B +
    (21 / 16 : ℝ) * (eta : ℝ)

/-- A quantitative scalar estimate for the actual buffered max query.
The positive-measure clamp is included in the max inequality. -/
theorem physical_query_error {R w t x r b : ℝ}
    (hw : a ≤ w ∧ w ≤ d) (hR : 0 ≤ R ∧ R ≤ 1)
    (ht : 0 ≤ t ∧ t ≤ b) (hx : 0 ≤ x ∧ x ≤ b)
    (hr : 0 ≤ r ∧ r ≤ b) (hb : b ≤ a / 2) :
    |BufferedOrdinaryClamp.physicalQuery R w t x r - max 2 (R / w)| ≤ 500 * b := by
  have ha : 0 < a := by norm_num [a]
  have hb0 : 0 ≤ b := ht.1.trans ht.2
  have hw0 : 0 < w := ha.trans_le hw.1
  have hh : a / 2 ≤ w - x := by linarith
  have hden0 : 0 < w * (w - x) := mul_pos hw0 (by linarith)
  have hden : a ^ 2 / 2 ≤ w * (w - x) := by
    have h := mul_le_mul hw.1 hh (by linarith : (0 : ℝ) ≤ a / 2) hw0.le
    nlinarith
  have hnum : |R * x - t * w| ≤ b * (1 + d) := by
    have hRx : R * x ≤ b := by nlinarith [mul_le_mul_of_nonneg_right hR.2 hx.1]
    have htw : t * w ≤ b * d := mul_le_mul ht.2 hw.2 hw0.le hb0
    have habs : |R * x - t * w| ≤ R * x + t * w := by
      simpa only [sub_eq_add_neg, abs_neg,
        abs_of_nonneg (mul_nonneg hR.1 hx.1),
        abs_of_nonneg (mul_nonneg ht.1 hw0.le)] using
        (abs_add_le (R * x) (-(t * w)))
    nlinarith
  have hratio : |(R - t) / (w - x) - R / w| ≤ 500 * b := by
    have hid : (R - t) / (w - x) - R / w =
        (R * x - t * w) / (w * (w - x)) := by
      field_simp [hw0.ne', (show 0 < w - x by linarith).ne']
      <;> ring
    rw [hid, abs_div, abs_of_pos hden0]
    apply (div_le_iff₀ hden0).mpr
    have hc : 1 + d ≤ 500 * (a ^ 2 / 2) := by norm_num [a, d]
    calc
      _ ≤ b * (1 + d) := hnum
      _ ≤ (500 * b) * (a ^ 2 / 2) := by nlinarith [mul_le_mul_of_nonneg_left hc hb0]
      _ ≤ (500 * b) * (w * (w - x)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
  have hmax := abs_max_sub_max_le_max (2 + r) ((R - t) / (w - x)) 2 (R / w)
  unfold BufferedOrdinaryClamp.physicalQuery
  apply hmax.trans
  apply max_le
  · rw [show (2 + r) - 2 = r by ring, abs_of_nonneg hr.1]
    linarith
  · exact hratio

theorem cap_le_one_on_actual_cube (p : Policy) (v : LogFour) (hv : v ∈ cube) :
    cap p v ≤ 1 := by
  have hcoord (i : Fin 4) : 0 ≤ v i ∧ v i ≤ d := by
    have h := mem_logPrimeBox.mp hv i
    constructor
    · exact (by norm_num [lower] : (0 : ℝ) ≤ (lower : ℝ)).trans h.1
    · simpa [upper, d] using h.2.le
  have hm : selectedMass p v ≤ 4 * d := by
    calc
      selectedMass p v ≤ ∑ _i : Fin 4, d := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hs : Selected p i
        · simpa only [if_pos hs] using (hcoord i).2
        · simp only [if_neg hs]
          norm_num [d]
      _ = 4 * d := by simp
  by_cases hp : p.val < 15
  · simp only [cap, if_pos hp]
    exact (min_le_left _ _).trans (by norm_num [d] at hm ⊢; linarith)
  · simp only [cap, if_neg hp]
    linarith [(hcoord 2).1]

theorem residual_le_one_on_actual_cube (p : Policy) (v : LogFour) (hv : v ∈ cube) :
    typedResidual p v ≤ 1 := by
  have hc := cap_le_one_on_actual_cube p v hv
  have hsum : 0 ≤ U11SelectedLargest.prefixSum v := by
    rw [U1011OriginalSixteenOscillation.prefixSum_eq_sum]
    apply Finset.sum_nonneg
    intro i hi
    have h := (mem_logPrimeBox.mp hv i).1
    exact (by norm_num [lower] : (0 : ℝ) ≤ (lower : ℝ)).trans h
  unfold typedResidual
  linarith

theorem compiled_query_eq_frozen_ratio {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {eta : ℚ} (heta : 0 < eta) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :
    compiledQuery n N eta t =
      (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual
        (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) /
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
        (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) := by
  have hl := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  have hNp : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hNl : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  unfold compiledQuery U1011OriginalSixteenJointNearCapCompiler.D
    U1011OriginalSixteenJointNearCapCompiler.Z
    U1011OriginalSixteenJointNearCapCompiler.rowD
    U1011OriginalSixteenJointNearCapCompiler.rowZ
  rw [Real.log_rpow hNp, Real.log_rpow hNp]
  by_cases hz : (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) = 0
  · simp only [hz, zero_mul, div_zero]
  · field_simp [hNl, hz]
    <;> ring

/-- The real source supplies the original low-unmasked/high-complement
mask and its actual frozen selected policy. Every geometric buffer is
the parameter of that same row. -/
theorem actual_compiled_query_error {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {eta : ℚ} (heta : 0 < eta) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hsmall : boxBuffer (selectedPolicy n N t) (ownerBox n N t) eta ≤ a / 2) :
    |compiledQuery n N eta t - idealQuery n N t| ≤
      500 * boxBuffer (selectedPolicy n N t) (ownerBox n N t) eta := by
  have hs := (Finset.mem_filter.mp ht).1
  have hne := (Finset.mem_filter.mp ht).2
  have htest := (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate
    (ownerBox n N t) hne).2
  have hcube := U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hs
  have hcell := owner_mem n hcube
  have hbox := cell_subset_closed_box n _ hcell
  have hvalid := gridBox_valid n (owner n (coordinates N t))
  have hpositive := gridBox_lower_positive n (owner n (coordinates N t)) 3
  have he := wholeBoxEligibleTest_sound (selectedPolicy n N t) (ownerBox n N t) htest
    (coordinates N t) hbox
  have hw : a ≤ coordinates N t 3 ∧ coordinates N t 3 ≤ d := by
    have h := mem_logPrimeBox.mp hcube 3
    exact ⟨by simpa [lower, a] using h.1, by simpa [upper, d] using h.2.le⟩
  have hR : 0 ≤ typedResidual (selectedPolicy n N t) (coordinates N t) ∧
      typedResidual (selectedPolicy n N t) (coordinates N t) ≤ 1 := by
    refine ⟨?_, residual_le_one_on_actual_cube _ _ hcube⟩
    have h := typedEligible_residual_gt_smallest _ _ he
    have ha : 0 < a := by norm_num [a]
    exact (ha.trans_le hw.1).le.trans h.le
  have hb := U1011OriginalSixteenNearCapBoxProfiles.uniform_buffer_bound
    (selectedPolicy n N t) (ownerBox n N t) eta hvalid hpositive htest heta
    (coordinates N t) hbox
  have htB := (le_max_left _ _).trans hb.2.2.2
  have hxB := (le_max_of_le_right (le_max_left _ _)).trans hb.2.2.2
  have hrB := (le_max_of_le_right (le_max_right _ _)).trans hb.2.2.2
  have hphys := (U1011OriginalSixteenNearCapBoxProfiles.physical_profile_dictionary
    (selectedPolicy n N t) (ownerBox n N t) eta hvalid hpositive htest heta
    (coordinates N t)).2
  rw [compiled_query_eq_frozen_ratio hN heta ht, hphys]
  exact physical_query_error hw hR ⟨hb.1, htB⟩ ⟨hb.2.1, hxB⟩
    ⟨hb.2.2.1, hrB⟩ hsmall

/-- Frozen-query knots pull back to an enlarged ideal-query neighborhood.
At a fixed mesh the enlargement cannot be silently dropped. -/
theorem actual_frozen_knot_implies_enlarged_ideal {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {eta : ℚ} (heta : 0 < eta) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hsmall : boxBuffer (selectedPolicy n N t) (ownerBox n N t) eta ≤ a / 2)
    (q radius : ℝ) (hnear : |compiledQuery n N eta t - q| ≤ radius) :
    |idealQuery n N t - q| ≤ radius +
      500 * boxBuffer (selectedPolicy n N t) (ownerBox n N t) eta := by
  have he := actual_compiled_query_error hN heta ht hsmall
  calc
    _ ≤ |idealQuery n N t - compiledQuery n N eta t| +
        |compiledQuery n N eta t - q| := abs_sub_le _ _ _
    _ ≤ _ := by rw [abs_sub_comm] at he; linarith

end
end ImbalancedChen.P2UpperActualCompiledQueryBuffer
