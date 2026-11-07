import ImbalancedChen.P5ZU11SelectedLargestOrdinary
import ImbalancedChen.P5ZU1011H248CommonPartition
import ImbalancedChen.AffinePrimeWallReserve

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Actual arithmetic payment of every high H248 knot for the ORIGINAL
selected-largest policy. Its physical cap is the minimum of the two
original affine caps, not an arbitrary affine residual. The 150 knots
51,...,200 on each of the two physical branches give 300 explicitly
nonzero walls. The actual prime thin-strip theorem pays these walls;
Lebesgue nullity is never used to delete arithmetic prime atoms.

Deleting only these high-knot table values has a uniformly vanishing
effect after an arbitrary finite-policy minimum and an arbitrary moving
tuple mask. The clamp knot50 is retained. Other policies, their gates,
and their candidate values remain entirely unchanged. This is a boundary
supplier for the full mean, not an assertion of that mean or of any
Rosser, AP, policy, feedback-table or numerical certificate licence.
-/

namespace ImbalancedChen.P5Z.U1011SelectedLargestKnotPayment

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open U11Integral U11H248 U1011H248Partition U1011AdaptivePrimeError
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

def prefixLinear : LogFour →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1 +
    ContinuousLinearMap.proj 2 + ContinuousLinearMap.proj 3

def capLinear (left : Bool) : LogFour →L[ℝ] ℝ :=
  (if left then (1 / 2 : ℝ) else -(3 / 2 : ℝ)) • ContinuousLinearMap.proj 0

def capConstant (left : Bool) : ℝ := if left then 1 / 2 else 57 / 64

def branchLinear (left : Bool) : LogFour →L[ℝ] ℝ := capLinear left - prefixLinear

def branchResidual (left : Bool) (v : LogFour) : ℝ :=
  branchLinear left v + capConstant left

theorem branchResidual_true (v : LogFour) :
    branchResidual true v = (1+v 0)/2-U11SelectedLargest.prefixSum v := by
  simp only [branchResidual, branchLinear, capLinear, capConstant, if_true,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, prefixLinear,
    ContinuousLinearMap.add_apply, U11SelectedLargest.prefixSum]
  ring

theorem branchResidual_false (v : LogFour) :
    branchResidual false v = 57/64-(3/2:ℝ)*v 0-U11SelectedLargest.prefixSum v := by
  simp only [branchResidual, branchLinear, capLinear, capConstant, Bool.false_eq_true,
    if_false, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, prefixLinear,
    ContinuousLinearMap.add_apply, U11SelectedLargest.prefixSum]
  ring

/-- The actual piecewise-affine original cap supplies one of these two
branches at EVERY point, including the cap-switch equality. -/
theorem residual_eq_branch (v : LogFour) :
    ∃ left : Bool, U11SelectedLargest.residual 0 v = branchResidual left v := by
  by_cases h : (1+v 0)/2 ≤ 57/64-(3/2:ℝ)*v 0
  · refine ⟨true, ?_⟩
    rw [branchResidual_true]
    simp only [U11SelectedLargest.residual, U11SelectedLargest.cap, min_eq_left h]
  · refine ⟨false, ?_⟩
    rw [branchResidual_false]
    simp only [U11SelectedLargest.residual, U11SelectedLargest.cap,
      min_eq_right (le_of_not_ge h)]

def highKnot (i : Fin 150) : Fin 201 := ⟨i.val+51, by omega⟩

def knotForm (left : Bool) (j : Fin 201) : LogFour →L[ℝ] ℝ :=
  branchLinear left - floorGrid j.val • ContinuousLinearMap.proj 3

/-- The y coefficient is literally -1, for BOTH cap branches and EVERY
table knot. No caller-supplied nondegeneracy premise is required. -/
theorem knotForm_ne_zero (left : Bool) (j : Fin 201) : knotForm left j ≠ 0 := by
  intro h
  have hv := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![0,1,0,0]) h
  cases left <;>
    norm_num [knotForm, branchLinear, capLinear, prefixLinear] at hv

def wallForms : Fin (150+150) → LogFour →L[ℝ] ℝ :=
  Fin.append (fun i => knotForm true (highKnot i))
    (fun i => knotForm false (highKnot i))

def wallBounds : Fin (150+150) → ℝ :=
  Fin.append (fun _ => -capConstant true) (fun _ => -capConstant false)

theorem wallForms_ne_zero : ∀ i, wallForms i ≠ 0 := by
  simp only [wallForms, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  exact ⟨fun i => knotForm_ne_zero true _, fun i => knotForm_ne_zero false _⟩

def highKnots : Set LogFour := {v | 0 < v 3 ∧ ∃ j : Fin 201,
  50 < j.val ∧ max 2 (U11SelectedLargest.residual 0 v / v 3) = floorGrid j.val}

theorem highKnots_subset_strip {delta : ℝ} (hd : 0 ≤ delta) :
    highKnots ⊆ primeAffineWallStrip wallForms wallBounds delta := by
  rintro v ⟨hw, j, hj, hquery⟩
  have hgrid : (2 : ℝ) < floorGrid j.val := by
    have hjR : (50 : ℝ) < (j.val : ℝ) := by exact_mod_cast hj
    dsimp [floorGrid]
    linarith
  have hq : U11SelectedLargest.residual 0 v / v 3 = floorGrid j.val := by
    have hquery2 : 2 ≤ U11SelectedLargest.residual 0 v / v 3 := by
      by_contra hn
      rw [max_eq_left (le_of_lt (lt_of_not_ge hn))] at hquery
      linarith
    simpa only [max_eq_right hquery2] using hquery
  have heq : U11SelectedLargest.residual 0 v = floorGrid j.val * v 3 :=
    (div_eq_iff hw.ne').1 hq
  let i : Fin 150 := ⟨j.val-51, by have hmax := j.isLt; omega⟩
  have hi : highKnot i = j := by apply Fin.ext; dsimp [highKnot, i]; omega
  obtain ⟨left, hbranch⟩ := residual_eq_branch v
  have hwall : knotForm left j v = -capConstant left := by
    simp only [knotForm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    dsimp only [branchResidual] at hbranch
    linarith
  cases left
  · refine ⟨Fin.natAdd 150 i, ?_⟩
    simp only [wallForms, wallBounds, Fin.append_right, hi, hwall, sub_self, abs_zero]
    exact hd
  · refine ⟨Fin.castAdd 150 i, ?_⟩
    simp only [wallForms, wallBounds, Fin.append_left, hi, hwall, sub_self, abs_zero]
    exact hd

def knotMass (N : ℕ) : ℝ :=
  ∑ p ∈ (actualPrimeBoxTuples N (fun _ : Fin 4 => (417/5000:ℝ))
    (fun _ => (59/250:ℝ))).filter (fun p => actualPrimeTupleLog N p ∈ highKnots),
      ∏ i, 1 / ((p i : ℝ)-1)

theorem knotMass_nonneg (N : ℕ) : 0 ≤ knotMass N := by
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

theorem knotMass_le_strip (N : ℕ) {delta : ℝ} (hd : 0 ≤ delta) :
    knotMass N ≤ actualPrimeAffineWallStripMass N
      (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ))
        wallForms wallBounds delta := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hx⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp, highKnots_subset_strip hd hx⟩
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- Every arithmetic knot atom is retained until the TRUE prime thin-strip
bound pays it. This proves zero arithmetic mass, not just zero volume. -/
theorem tendsto_knotMass_zero : Tendsto knotMass atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon he
  obtain ⟨delta, hd, N0, hN0, hpay⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by norm_num : (0:ℝ)<417/5000) (by norm_num : (417/5000:ℝ)<59/250)
    wallForms wallBounds wallForms_ne_zero epsilon he
  filter_upwards [eventually_ge_atTop N0] with N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (knotMass_nonneg N)]
  exact (knotMass_le_strip N hd.le).trans_lt (hpay N hN)

def erasedH248 (s : ℝ) : ℝ :=
  if ∃ j : Fin 201, 50 < j.val ∧ s = floorGrid j.val then 0 else H248 s

theorem erasedH248_bounds (s : ℝ) : 0 ≤ erasedH248 s ∧ erasedH248 s ≤ 1 := by
  unfold erasedH248
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact H248_bounds s

/-- The full positive-measure clamp state is never erased. -/
theorem erasedH248_two : erasedH248 2 = H248 2 := by
  have hn : ¬ ∃ j : Fin 201, 50 < j.val ∧ (2:ℝ) = floorGrid j.val := by
    rintro ⟨j, hj, heq⟩
    have hjR : (50:ℝ)<(j.val:ℝ) := by exact_mod_cast hj
    dsimp [floorGrid] at heq
    linarith
  simp only [erasedH248, if_neg hn]

theorem erasedOrdinary_bounds (mask : Set (ℝ × ℝ)) (v : LogFour)
    (hv : v ∈ originalDomain mask) (he : U11SelectedLargest.eligible 0 v) :
    0 ≤ ordinaryKernel erasedH248 U11SelectedLargest.residual 0 v ∧
      ordinaryKernel erasedH248 U11SelectedLargest.residual 0 v ≤ (20000/417:ℝ) := by
  have hw := (originalDomain_denominators_pos mask v hv).1
  have hr := U11SelectedLargest.eligible_residual_gt_smallest mask 0 v hv he
  have hp : 0 < U11SelectedLargest.residual 0 v := hw.trans hr
  have ha : (417/5000:ℝ) ≤ v 3 := hv.1
  have hH := erasedH248_bounds (max 2 (U11SelectedLargest.residual 0 v / v 3))
  unfold ordinaryKernel
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hH.2)) hp.le
  · apply (div_le_iff₀ hp).2
    nlinarith [hH.1]

def bound : ℝ := 20000/417

/-- Literal original residual, true selected-square eligibility, actual
H248 and erased H248. The only discrepancy is on the paid high knots. -/
theorem ordinary_knot_error (mask : Set (ℝ × ℝ)) (v : LogFour)
    (hv : v ∈ originalDomain mask) (he : U11SelectedLargest.eligible 0 v) :
    |ordinaryKernel H248 U11SelectedLargest.residual 0 v -
      ordinaryKernel erasedH248 U11SelectedLargest.residual 0 v| ≤
        highKnots.indicator (fun _ => bound) v := by
  by_cases hk : v ∈ highKnots
  · rw [indicator_of_mem hk]
    have ho := U11SelectedLargest.ordinary_actual_bounds mask 0 v hv he
    have hn := erasedOrdinary_bounds mask v hv he
    apply abs_le.mpr
    constructor <;> dsimp [bound] <;> linarith
  · have hw := (originalDomain_denominators_pos mask v hv).1
    have hn : ¬ ∃ j : Fin 201, 50 < j.val ∧
        max 2 (U11SelectedLargest.residual 0 v / v 3) = floorGrid j.val :=
      fun h => hk ⟨hw, h⟩
    rw [indicator_of_notMem hk]
    simp only [ordinaryKernel, erasedH248, if_neg hn, sub_self, abs_zero, le_refl]

def branchEligibility (tag : ℕ) (other : ℕ → LogFour → Prop) (j : ℕ) (v : LogFour) : Prop :=
  if j = tag then U11SelectedLargest.eligible 0 v else other j v

def branchOrdinary (tag : ℕ) (other : ℕ → LogFour → ℝ) (H : ℝ → ℝ)
    (j : ℕ) (v : LogFour) : ℝ :=
  if j = tag then ordinaryKernel H U11SelectedLargest.residual 0 v else other j v

def branchEnvelope (bank : Finset ℕ) (tag : ℕ) (otherEligible : ℕ → LogFour → Prop)
    (switched : LogFour → ℝ) (other : ℕ → LogFour → ℝ) (H : ℝ → ℝ) : LogFour → ℝ :=
  envelope bank (guarded (branchEligibility tag otherEligible) switched
    (branchOrdinary tag other H))

/-- Every other policy can vary arbitrarily. The nonlinear finite minimum
pays a SINGLE knot discrepancy, independently of bank cardinality. -/
theorem envelope_knot_error (mask : Set (ℝ × ℝ)) (bank : Finset ℕ) (tag : ℕ)
    (otherEligible : ℕ → LogFour → Prop) (switched : LogFour → ℝ)
    (other : ℕ → LogFour → ℝ) (v : LogFour) (hv : v ∈ originalDomain mask) :
    |branchEnvelope bank tag otherEligible switched other H248 v -
      branchEnvelope bank tag otherEligible switched other erasedH248 v| ≤
      highKnots.indicator (fun _ => bound) v := by
  apply guarded_envelope_abs_sub_le
  · have hb : (0:ℝ)≤highKnots.indicator (fun _ => bound) v := by
      by_cases hk : v ∈ highKnots
      · rw [indicator_of_mem hk]; norm_num [bound]
      · simp only [indicator_of_notMem hk, le_refl]
    simpa only [sub_self, abs_zero] using hb
  · intro j hj he
    by_cases htag : j = tag
    · have he0 : U11SelectedLargest.eligible 0 v := by
        simpa only [branchEligibility, if_pos htag] using he
      simpa only [branchOrdinary, if_pos htag] using ordinary_knot_error mask v hv he0
    · have hb : (0:ℝ)≤highKnots.indicator (fun _ => bound) v := by
        by_cases hk : v ∈ highKnots
        · rw [indicator_of_mem hk]; norm_num [bound]
        · simp only [indicator_of_notMem hk, le_refl]
      simpa only [branchOrdinary, if_neg htag, sub_self, abs_zero] using hb

theorem masked_envelope_knot_error (N : ℕ) (mask : Set (ℝ × ℝ))
    (keep : (Fin 4 → ℕ) → Prop) (bank : Finset ℕ) (tag : ℕ)
    (otherEligible : ℕ → LogFour → Prop) (switched : LogFour → ℝ)
    (other : ℕ → LogFour → ℝ)
    (hkeep : ∀ p ∈ actualPrimeBoxTuples N
      (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)),
      keep p → actualPrimeTupleLog N p ∈ originalDomain mask) :
    |maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
        (branchEnvelope bank tag otherEligible switched other H248) -
      maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
        (branchEnvelope bank tag otherEligible switched other erasedH248)| ≤ bound*knotMass N := by
  unfold maskedTestSum knotMass
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hw := actualPrimeBoxWeight_nonneg hp
  by_cases hk : keep p
  · have he := envelope_knot_error mask bank tag otherEligible switched other _ (hkeep p hp hk)
    simp only [if_pos hk, ← mul_sub, abs_mul, abs_of_nonneg hw]
    by_cases hs : actualPrimeTupleLog N p ∈ highKnots
    · simpa only [if_pos hs, indicator_of_mem hs, mul_comm bound] using
        mul_le_mul_of_nonneg_left he hw
    · simpa only [if_neg hs, indicator_of_notMem hs, mul_zero, mul_comm bound] using
        mul_le_mul_of_nonneg_left he hw
  · simp only [if_neg hk, sub_self, abs_zero]
    by_cases hs : actualPrimeTupleLog N p ∈ highKnots <;>
      simp only [hs, if_true, if_false, mul_zero, le_refl]
    exact mul_nonneg (by norm_num [bound]) hw

/-- A common target threshold is chosen BEFORE bank, alternate policies
and the arbitrary moving arithmetic gainmask. No masked mean is assumed. -/
theorem eventually_uniform_masked_envelope_knot_error (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ (mask : Set (ℝ × ℝ)) (keep : (Fin 4 → ℕ) → Prop)
      (bank : Finset ℕ) (tag : ℕ) (otherEligible : ℕ → LogFour → Prop)
      (switched : LogFour → ℝ) (other : ℕ → LogFour → ℝ),
      (∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => (417/5000:ℝ))
        (fun _ => (59/250:ℝ)), keep p → actualPrimeTupleLog N p ∈ originalDomain mask) →
      |maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
          (branchEnvelope bank tag otherEligible switched other H248) -
        maskedTestSum N (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ)) keep
          (branchEnvelope bank tag otherEligible switched other erasedH248)| < epsilon := by
  have ht : Tendsto (fun N => bound*knotMass N) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_knotMass_zero.const_mul bound
  filter_upwards [ht.eventually (gt_mem_nhds he)] with N hN
  intro mask keep bank tag otherEligible switched other hkeep
  exact (masked_envelope_knot_error N mask keep bank tag otherEligible switched other hkeep).trans_lt hN

end

end ImbalancedChen.P5Z.U1011SelectedLargestKnotPayment
