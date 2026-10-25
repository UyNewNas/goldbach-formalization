import ImbalancedChen.Part3PositiveRectangleSmoothTensorDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Global planar L2 approximation of every continuous compactly supported
function whose topological support is strictly inside the positive chart.
The output belongs to the actual finite complex span of compact smooth
positive-height separated tensors. No tensor-density premise is used.

The earlier rectangle theorem is applied on a *larger* positive rectangle.
A common explicit smooth cutoff equals one on the original support and
vanishes outside that larger rectangle. Thus the approximation controls
the entire plane, including the outer region where the input is zero.
The finite rectangle measure converts the uniform error to an L2 error.

Density for arbitrary upper-supported planar L2 classes, and canonical
weighted L2 quotient transport, remain separate steps.
-/

namespace ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a

noncomputable section
open Set Metric MeasureTheory
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a

def planeTensor (T : SmoothPositiveTensor) (p : ℝ × ℝ) : ℂ :=
  ((T.horizontal p.1 * T.vertical p.2 : ℝ) : ℂ)

def planeTensorSpan : Submodule ℂ ((ℝ × ℝ) → ℂ) :=
  Submodule.span ℂ (Set.range planeTensor)

theorem planeTensor_continuous (T : SmoothPositiveTensor) : Continuous (planeTensor T) :=
  Complex.continuous_ofReal.comp
    ((T.horizontal_smooth.continuous.comp continuous_fst).mul
      (T.vertical_smooth.continuous.comp continuous_snd))

theorem planeTensor_compact (T : SmoothPositiveTensor) : HasCompactSupport (planeTensor T) := by
  apply HasCompactSupport.intro (T.horizontal_compact.prod T.vertical_compact)
  intro p hp
  by_cases hx : p.1 ∈ tsupport T.horizontal
  · have hy : p.2 ∉ tsupport T.vertical := fun hy => hp ⟨hx, hy⟩
    simp [planeTensor, image_eq_zero_of_notMem_tsupport hy]
  · simp [planeTensor, image_eq_zero_of_notMem_tsupport hx]

theorem span_continuous_compact {G : (ℝ × ℝ) → ℂ} (hG : G ∈ planeTensorSpan) :
    Continuous G ∧ HasCompactSupport G := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
      obtain ⟨T, rfl⟩ := hG
      exact ⟨planeTensor_continuous T, planeTensor_compact T⟩
  | zero => exact ⟨continuous_const, HasCompactSupport.zero⟩
  | add F G hF hG ihF ihG => exact ⟨ihF.1.add ihG.1, ihF.2.add ihG.2⟩
  | smul c G hG ihG => exact ⟨continuous_const.smul ihG.1, ihG.2.smul_left⟩

/-- A local finite tensor combination lifts to a genuine global finite
tensor combination, retaining equality throughout the whole rectangle. -/
theorem lift_rectangle_span (A a b : ℝ) {g : C(rectangle A a b, ℂ)}
    (hg : g ∈ Submodule.span ℂ (tensorRestrictions A a b)) :
    ∃ G ∈ planeTensorSpan, ∀ p : rectangle A a b, G p.1 = g p := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨T, rfl⟩ := hg
      exact ⟨planeTensor T, Submodule.subset_span ⟨T, rfl⟩, fun _ => rfl⟩
  | zero => exact ⟨0, planeTensorSpan.zero_mem, by intro p; rfl⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨F, hF, hFeq⟩ := ihf
      obtain ⟨G, hG, hGeq⟩ := ihg
      refine ⟨F + G, planeTensorSpan.add_mem hF hG, ?_⟩
      intro p
      simp only [Pi.add_apply, ContinuousMap.add_apply, hFeq p, hGeq p]
  | smul c g hg ih =>
      obtain ⟨G, hG, hGeq⟩ := ih
      refine ⟨c • G, planeTensorSpan.smul_mem c hG, ?_⟩
      intro p
      simp only [Pi.smul_apply, ContinuousMap.smul_apply, hGeq p]

theorem tensor_mul_span_mem (T : SmoothPositiveTensor)
    {G : (ℝ × ℝ) → ℂ} (hG : G ∈ planeTensorSpan) :
    planeTensor T * G ∈ planeTensorSpan := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
      obtain ⟨U, rfl⟩ := hG
      apply Submodule.subset_span
      refine ⟨multiplyTensor T U, ?_⟩
      funext p
      simp only [planeTensor, multiplyTensor, Pi.mul_apply]
      push_cast
      ring
  | zero => simpa using planeTensorSpan.zero_mem
  | add F G hF hG ihF ihG =>
      simpa only [mul_add] using planeTensorSpan.add_mem ihF ihG
  | smul c G hG ih =>
      simpa only [mul_smul_comm] using planeTensorSpan.smul_mem c ih

def outerRectangle (A a b : ℝ) : Set (ℝ × ℝ) :=
  rectangle (A + 2) (a / 2) (b + a / 2)

theorem cutoff_norm_le_one (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) (p : ℝ × ℝ) :
    ‖planeTensor (cutoffTensor A a b hA ha hab) p‖ ≤ 1 := by
  simp only [planeTensor, cutoffTensor, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (horizontalBump A hA).nonneg
    (verticalBump a b ha hab).nonneg)]
  nlinarith [(horizontalBump A hA).nonneg (x := p.1),
    (horizontalBump A hA).le_one (x := p.1),
    (verticalBump a b ha hab).nonneg (x := p.2),
    (verticalBump a b ha hab).le_one (x := p.2)]

theorem cutoff_nonzero_mem_outer (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) {p : ℝ × ℝ}
    (hp : planeTensor (cutoffTensor A a b hA ha hab) p ≠ 0) :
    p ∈ outerRectangle A a b := by
  have hx0 : horizontalBump A hA p.1 ≠ 0 := by
    intro h
    exact hp (by simp [planeTensor, cutoffTensor, h])
  have hy0 : verticalBump a b ha hab p.2 ≠ 0 := by
    intro h
    exact hp (by simp [planeTensor, cutoffTensor, h])
  have hx : p.1 ∈ tsupport (horizontalBump A hA) := subset_tsupport _ hx0
  have hy : p.2 ∈ tsupport (verticalBump a b ha hab) := subset_tsupport _ hy0
  rw [(horizontalBump A hA).tsupport_eq, Metric.mem_closedBall,
    Real.dist_eq, sub_zero, abs_le] at hx
  rw [(verticalBump a b ha hab).tsupport_eq, Metric.mem_closedBall,
    Real.dist_eq, abs_le] at hy
  change -(A + 2) ≤ p.1 ∧ p.1 ≤ A + 2 at hx
  change -((b - a) / 2 + a / 2) ≤ p.2 - (a + b) / 2 ∧
    p.2 - (a + b) / 2 ≤ (b - a) / 2 + a / 2 at hy
  change (-(A + 2) ≤ p.1 ∧ p.1 ≤ A + 2) ∧
    a / 2 ≤ p.2 ∧ p.2 ≤ b + a / 2
  exact ⟨hx, by constructor <;> linarith [hy.1, hy.2]⟩

/-- The cutoff fixes the whole input, including outside its support. -/
theorem cutoff_mul_eq_input (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) (F : (ℝ × ℝ) → ℂ)
    (hsupp : tsupport F ⊆ rectangle A a b) (p : ℝ × ℝ) :
    planeTensor (cutoffTensor A a b hA ha hab) p * F p = F p := by
  by_cases hp : p ∈ tsupport F
  · have hi := hsupp hp
    have hc := congrFun (congrArg (fun f : C(rectangle A a b, ℂ) =>
      (f : rectangle A a b → ℂ)) (restrict_cutoffTensor A a b hA ha hab)) ⟨p, hi⟩
    change planeTensor (cutoffTensor A a b hA ha hab) p = 1 at hc
    rw [hc, one_mul]
  · simp only [image_eq_zero_of_notMem_tsupport hp, mul_zero]

/-- Full-plane approximation, with the outer-region error paid explicitly.
Only continuous input and geometric support data are hypotheses. -/
theorem exists_plane_tensor_L2_approx_of_support_rectangle
    (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (F : (ℝ × ℝ) → ℂ) (hF : Continuous F)
    (hsupp : tsupport F ⊆ rectangle A a b)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0) :
    ∃ H ∈ planeTensorSpan, eLpNorm (F - H) 2 volume < epsilon := by
  let K := outerRectangle A a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := hK.measurableSet
  have hfinite : (volume : Measure (ℝ × ℝ)) K ≠ ⊤ := hK.measure_lt_top.ne
  let C : ℝ≥0∞ := (volume : Measure (ℝ × ℝ)) K ^ (1 / (2 : ℝ≥0∞).toReal)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfinite
  obtain ⟨delta, hdelta, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hC hepsilon
  let f : C(rectangle (A + 2) (a / 2) (b + a / 2), ℂ) :=
    ⟨fun p => F p.1, hF.comp continuous_subtype_val⟩
  obtain ⟨g, hg, hnear⟩ := exists_smooth_tensor_span_uniform_approx
    (A + 2) (a / 2) (b + a / 2) (by linarith) (by linarith)
    (by linarith) f (delta : ℝ) (by exact_mod_cast hdelta)
  obtain ⟨G, hG, hGeq⟩ := lift_rectangle_span _ _ _ hg
  let T := cutoffTensor A a b hA ha hab
  let H := planeTensor T * G
  refine ⟨H, tensor_mul_span_mem T hG, ?_⟩
  have hpoint (p : ℝ × ℝ) :
      ‖(F - H) p‖ ≤ K.indicator (fun _ => (delta : ℝ)) p := by
    have hfix := cutoff_mul_eq_input A a b hA ha hab F hsupp p
    by_cases hp : p ∈ K
    · rw [Set.indicator_of_mem hp]
      have hlocal := hnear ⟨p, hp⟩
      rw [← hGeq ⟨p, hp⟩] at hlocal
      have hdiff : F p - H p = planeTensor T p * (F p - G p) := by
        dsimp only [H, Pi.mul_apply]
        rw [mul_sub, hfix]
      rw [Pi.sub_apply, hdiff, norm_mul]
      have hb : ‖F p - G p‖ ≤ (delta : ℝ) := by
        simpa only [f, norm_sub_rev] using hlocal.le
      exact (mul_le_mul_of_nonneg_right
        (cutoff_norm_le_one A a b hA ha hab p) (norm_nonneg _)).trans
          (by simpa only [one_mul] using hb)
    · have hzero : planeTensor T p = 0 := by
        by_contra hn
        exact hp (cutoff_nonzero_mem_outer A a b hA ha hab hn)
      have hFzero : F p = 0 := by
        rw [hzero, zero_mul] at hfix
        exact hfix.symm
      simp [H, hzero, hFzero, Set.indicator_of_notMem hp]
  have hbound := eLpNorm_mono_real hpoint (p := (2 : ℝ≥0∞)) (μ := volume)
  rw [eLpNorm_indicator_const hKm (by norm_num) (by norm_num)] at hbound
  have hnorm : ‖(delta : ℝ)‖ₑ = (delta : ℝ≥0∞) := by simp
  rw [hnorm] at hbound
  exact hbound.trans_lt hsmall

/-- A compact set strictly inside the positive chart has an actual
positive rectangular enclosure. The lower height is attained on the set. -/
theorem compact_positive_support_rectangle (F : (ℝ × ℝ) → ℂ)
    (hcompact : HasCompactSupport F)
    (hpositive : tsupport F ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    ∃ A a b : ℝ, 0 ≤ A ∧ 0 < a ∧ a ≤ b ∧ tsupport F ⊆ rectangle A a b := by
  by_cases hs : (tsupport F).Nonempty
  · obtain ⟨p0, hp0, hmin⟩ :=
      hcompact.exists_isMinOn hs continuous_snd.continuousOn
    obtain ⟨A0, hA0⟩ := hcompact.bddAbove_image
      (continuous_abs.comp continuous_fst).continuousOn
    obtain ⟨B0, hB0⟩ := hcompact.bddAbove_image continuous_snd.continuousOn
    refine ⟨max 0 A0, p0.2, max p0.2 B0, le_max_left _ _, hpositive hp0,
      le_max_left _ _, ?_⟩
    intro p hp
    have hx : |p.1| ≤ max 0 A0 :=
      (hA0 ⟨p, hp, rfl⟩).trans (le_max_right _ _)
    have hy : p.2 ≤ max p0.2 B0 :=
      (hB0 ⟨p, hp, rfl⟩).trans (le_max_right _ _)
    exact ⟨abs_le.mp hx, hmin hp, hy⟩
  · refine ⟨1, 1, 2, by norm_num, by norm_num, by norm_num, ?_⟩
    intro p hp
    exact (hs ⟨p, hp⟩).elim

/-- Every actual continuous compact positive-chart function is globally
L2-approximated by the actual finite complex smooth tensor span. -/
theorem exists_plane_tensor_L2_approx (F : (ℝ × ℝ) → ℂ)
    (hF : Continuous F) (hcompact : HasCompactSupport F)
    (hpositive : tsupport F ⊆ {p : ℝ × ℝ | 0 < p.2})
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0) :
    ∃ H ∈ planeTensorSpan, eLpNorm (F - H) 2 volume < epsilon := by
  obtain ⟨A, a, b, hA, ha, hab, hsupp⟩ :=
    compact_positive_support_rectangle F hcompact hpositive
  exact exists_plane_tensor_L2_approx_of_support_rectangle
    A a b hA ha hab F hF hsupp epsilon hepsilon

end
end ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a
