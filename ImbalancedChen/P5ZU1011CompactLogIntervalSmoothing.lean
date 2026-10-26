import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import Mathlib.Topology.Algebra.Support

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual compact one-dimensional log weights. `inner = true` spends its
reserve inside the literal Ico interval; `inner = false` spends it outside.
At the lower endpoint the inner weight is zero, and at the upper endpoint
the outer weight is one. Neither arithmetic endpoint is erased.
The fixed-order constant is chosen before width and both endpoints.
-/
namespace ImbalancedChen.P5Z.U1011CompactLogIntervalSmoothing
noncomputable section
open Set
open P4B

def shift (inner : Bool) (δ : ℝ) : ℝ := if inner then δ else 0

def weight (inner : Bool) (δ a b x : ℝ) : ℝ :=
  smoothGateUpperStep δ (x - a - shift inner δ) *
    smoothGateUpperStep δ (b - x - shift inner δ)

def literal (a b x : ℝ) : ℝ := if a ≤ x ∧ x < b then 1 else 0

theorem bounds (inner : Bool) (δ a b x : ℝ) :
    0 ≤ weight inner δ a b x ∧ weight inner δ a b x ≤ 1 := by
  obtain ⟨h0, h1⟩ := smoothGateUpperStep_bounds δ (x - a - shift inner δ)
  obtain ⟨g0, g1⟩ := smoothGateUpperStep_bounds δ (b - x - shift inner δ)
  exact ⟨mul_nonneg h0 g0, (mul_le_mul h1 g1 g0 zero_le_one).trans_eq (one_mul 1)⟩

theorem contDiff_weight (inner : Bool) (δ a b : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (weight inner δ a b) := by
  exact ((contDiff_smoothGateUpperStep δ).comp
    ((contDiff_id.sub contDiff_const).sub contDiff_const)).mul
    ((contDiff_smoothGateUpperStep δ).comp
      ((contDiff_const.sub contDiff_id).sub contDiff_const))

theorem inner_zero_outside {δ a b x : ℝ} (hδ : 0 < δ)
    (hx : ¬ (a ≤ x ∧ x < b)) : weight true δ a b x = 0 := by
  by_cases ha : a ≤ x
  · have hb : b ≤ x := le_of_not_gt (fun h => hx ⟨ha, h⟩)
    have hz : smoothGateUpperStep δ (b - x - shift true δ) = 0 :=
      smoothGateUpperStep_eq_zero hδ (by dsimp [shift]; linarith)
    unfold weight
    rw [hz, mul_zero]
  · have hz : smoothGateUpperStep δ (x - a - shift true δ) = 0 :=
      smoothGateUpperStep_eq_zero hδ (by dsimp [shift]; linarith)
    unfold weight
    rw [hz, zero_mul]

theorem inner_le_literal {δ : ℝ} (hδ : 0 < δ) (a b x : ℝ) :
    weight true δ a b x ≤ literal a b x := by
  by_cases hx : a ≤ x ∧ x < b
  · simpa [literal, hx] using (bounds true δ a b x).2
  · simp only [literal, if_neg hx, inner_zero_outside hδ hx, le_refl]

theorem outer_one {δ a b x : ℝ} (hδ : 0 < δ)
    (ha : a ≤ x) (hb : x ≤ b) : weight false δ a b x = 1 := by
  unfold weight
  rw [smoothGateUpperStep_eq_one hδ (by dsimp [shift]; linarith),
    smoothGateUpperStep_eq_one hδ (by dsimp [shift]; linarith), one_mul]

theorem literal_le_outer {δ : ℝ} (hδ : 0 < δ) (a b x : ℝ) :
    literal a b x ≤ weight false δ a b x := by
  by_cases hx : a ≤ x ∧ x < b
  · simp only [literal, if_pos hx, outer_one hδ hx.1 hx.2.le, le_refl]
  · simpa [literal, hx] using (bounds false δ a b x).1

theorem inner_one {δ a b x : ℝ} (hδ : 0 < δ)
    (ha : a + δ ≤ x) (hb : x ≤ b - δ) : weight true δ a b x = 1 := by
  unfold weight
  rw [smoothGateUpperStep_eq_one hδ (by dsimp [shift]; linarith),
    smoothGateUpperStep_eq_one hδ (by dsimp [shift]; linarith), one_mul]

theorem outer_zero_left {δ a b x : ℝ} (hδ : 0 < δ)
    (hx : x ≤ a - δ) : weight false δ a b x = 0 := by
  unfold weight
  rw [smoothGateUpperStep_eq_zero hδ (by dsimp [shift]; linarith), zero_mul]

theorem outer_zero_right {δ a b x : ℝ} (hδ : 0 < δ)
    (hx : b + δ ≤ x) : weight false δ a b x = 0 := by
  have hz : smoothGateUpperStep δ (b - x - shift false δ) = 0 :=
    smoothGateUpperStep_eq_zero hδ (by dsimp [shift]; linarith)
  unfold weight
  rw [hz, mul_zero]

/-- Exact one-sided inner reserve; the weak lower arithmetic wall belongs. -/
def innerReserve (δ a b x : ℝ) : Prop :=
  a ≤ x ∧ x < b ∧ (x < a + δ ∨ b - δ < x)

/-- Exact one-sided outer reserve; the strict upper arithmetic wall belongs. -/
def outerReserve (δ a b x : ℝ) : Prop :=
  (a - δ < x ∧ x < a) ∨ (b ≤ x ∧ x < b + δ)

theorem inner_error_support {δ a b x : ℝ} (hδ : 0 < δ)
    (he : literal a b x - weight true δ a b x ≠ 0) : innerReserve δ a b x := by
  have hx : a ≤ x ∧ x < b := by
    by_contra hn
    exact he (by simp [literal, hn, inner_zero_outside hδ hn])
  refine ⟨hx.1, hx.2, ?_⟩
  by_contra hn
  have ha : a + δ ≤ x := le_of_not_gt (fun h => hn (Or.inl h))
  have hb : x ≤ b - δ := le_of_not_gt (fun h => hn (Or.inr h))
  exact he (by simp [literal, hx, inner_one hδ ha hb])

theorem outer_error_support {δ a b x : ℝ} (hδ : 0 < δ)
    (he : weight false δ a b x - literal a b x ≠ 0) : outerReserve δ a b x := by
  by_cases ha : x < a
  · left
    refine ⟨?_, ha⟩
    by_contra hn
    have hz := outer_zero_left (a := a) (b := b) hδ (le_of_not_gt hn)
    exact he (by simp [hz, literal, not_le.mpr ha])
  · right
    have hax : a ≤ x := le_of_not_gt ha
    have hb : b ≤ x := by
      by_contra hn
      have hxb : x < b := lt_of_not_ge hn
      exact he (by simp [literal, hax, hxb, outer_one hδ hax hxb.le])
    refine ⟨hb, ?_⟩
    by_contra hn
    have hz := outer_zero_right (a := a) (b := b) hδ (le_of_not_gt hn)
    exact he (by simp [hz, literal, not_lt.mpr hb])

/-- Every actual atom is compact. No interval ordering is required. -/
theorem hasCompactSupport_weight {δ : ℝ} (hδ : 0 < δ) (inner : Bool) (a b : ℝ) :
    HasCompactSupport (weight inner δ a b) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (a - δ) (b + δ)))
  intro x hx
  have hn : weight inner δ a b x ≠ 0 := hx
  have hs : 0 ≤ shift inner δ := by cases inner <;> simp [shift, hδ.le]
  constructor
  · by_contra h
    have hx' : x < a - δ := lt_of_not_ge h
    apply hn
    unfold weight
    rw [smoothGateUpperStep_eq_zero hδ (by linarith), zero_mul]
  · by_contra h
    have hx' : b + δ < x := lt_of_not_ge h
    apply hn
    have hz : smoothGateUpperStep δ (b - x - shift inner δ) = 0 :=
      smoothGateUpperStep_eq_zero hδ (by linarith)
    unfold weight
    rw [hz, mul_zero]

/-- Quantitative derivative cost of the actual compact atom. The same
constant works for all endpoints, all positive widths and both reserves. -/
theorem exists_derivative_budget (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (inner : Bool) (δ : ℝ), 0 < δ → ∀ a b x : ℝ,
      |iteratedDeriv k (weight inner δ a b) x| ≤ C / δ ^ k := by
  obtain ⟨B, hB, hscalar⟩ := exists_smoothGateUpperStep_finite_derivative_budget k
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  refine ⟨B * B * 2 ^ k, by positivity, ?_⟩
  intro inner δ hδ a b x
  let f : ℝ → ℝ := fun t => smoothGateUpperStep δ (-a - shift inner δ + 1 * t)
  let g : ℝ → ℝ := fun t => smoothGateUpperStep δ (b - shift inner δ + (-1) * t)
  have hf : ContDiff ℝ ∞ f := (contDiff_smoothGateUpperStep δ).comp
    (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hg : ContDiff ℝ ∞ g := (contDiff_smoothGateUpperStep δ).comp
    (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hfactor (c s : ℝ) (hs : |s| = 1) (j : ℕ) (hj : j ≤ k) :
      |iteratedDeriv j (fun t => smoothGateUpperStep δ (c + s * t)) x| ≤ B * (δ⁻¹) ^ j := by
    rw [iteratedDeriv_comp_real_affine j (smoothGateUpperStep δ)
      (contDiff_smoothGateUpperStep δ) c s x, abs_mul, abs_pow, hs, one_pow, one_mul]
    simpa only [div_eq_mul_inv, inv_pow] using hscalar j hj δ hδ (c + s * x)
  have hp := abs_iteratedDeriv_two_mul_le k f g hf hg x (δ⁻¹) B B
    (inv_nonneg.mpr hδ.le) hB0 hB0
    (fun j hj => hfactor _ 1 (by norm_num) j hj)
    (fun j hj => hfactor _ (-1) (by norm_num) j hj)
  have heq : weight inner δ a b = fun t => f t * g t := by
    funext t
    dsimp [weight, f, g]
    congr 1 <;> congr 1 <;> ring
  rw [heq]
  convert hp using 1 <;> simp only [mul_pow, inv_pow, div_eq_mul_inv] <;> ring

end
end ImbalancedChen.P5Z.U1011CompactLogIntervalSmoothing
