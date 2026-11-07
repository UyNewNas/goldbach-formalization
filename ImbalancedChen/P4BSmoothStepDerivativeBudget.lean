import ImbalancedChen.P4BSmoothGateUpperStep
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Ring

/-!
# Quantitative derivatives of the genuine smooth upper step

SOURCE ONLY / YELLOW / UNCOMPILED (2026-10-24).

The companion import is a future normal module import. The base is the
actual pinned `Real.smoothTransition`, not a function carrying an assumed
derivative budget. Each fixed natural derivative order has a global bound:
order zero is bounded by one; positive orders vanish on the open constant
plateaus and are bounded on the compact transition interval by continuity.

The affine chain rule then gives the exact width factor and a constant
chosen before every width and argument. This supplies scalar derivative
quantification only. It does not certify the multivariable logarithmic
wall profiles, their product chain rules, or any P3/PP licensing condition.

Pinned APIs were read at mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1:
SmoothTransition; IteratedDeriv/Defs and /Lemmas; Normed/Group/Bounded.
-/

namespace ImbalancedChen.P4B

noncomputable section

open Filter Set Topology

/-- The exact zeroth derivative bound uses the proved range [0,1]. -/
theorem smoothTransition_iteratedDeriv_zero_abs_le_one (x : ℝ) :
    |iteratedDeriv 0 Real.smoothTransition x| ≤ 1 := by
  simp only [iteratedDeriv_zero]
  rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
  exact Real.smoothTransition.le_one x

/-- The left plateau is locally the constant zero function. This also
holds at order zero; no claim at the transition endpoint is needed here. -/
theorem smoothTransition_iteratedDeriv_eq_zero_of_neg
    (k : ℕ) {x : ℝ} (hx : x < 0) :
    iteratedDeriv k Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  simpa only [iteratedDeriv_fun_const_zero] using
    Filter.EventuallyEq.iteratedDeriv_eq k heq

/-- Every positive order vanishes on the right open constant plateau. -/
theorem smoothTransition_iteratedDeriv_eq_zero_of_one_lt
    (k : ℕ) (hk : 0 < k) {x : ℝ} (hx : 1 < x) :
    iteratedDeriv k Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  simpa only [iteratedDeriv_const, if_neg (ne_of_gt hk)] using
    Filter.EventuallyEq.iteratedDeriv_eq k heq

/-- Genuine continuity of the requested derivative, obtained from the
proved ContDiff theorem at the requested finite order. -/
theorem continuous_iteratedDeriv_smoothTransition (k : ℕ) :
    Continuous (iteratedDeriv k Real.smoothTransition) := by
  exact ContDiff.continuous_iteratedDeriv' k
    (Real.smoothTransition.contDiff (n := (k : ℕ∞)))

/-- Compactness supplies a bound on the closed transition interval,
including its two endpoints. The bound is enlarged to at least one. -/
theorem exists_smoothTransition_compact_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |iteratedDeriv k Real.smoothTransition x| ≤ C := by
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_iteratedDeriv_smoothTransition k).continuousOn
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro x hx
  have hBx : |iteratedDeriv k Real.smoothTransition x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB x hx
  exact hBx.trans (le_max_left _ _)

/-- For each fixed natural order, one constant bounds the actual base
transition everywhere. The constant is independent of width and argument. -/
theorem exists_smoothTransition_global_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ,
      |iteratedDeriv k Real.smoothTransition x| ≤ C := by
  cases k with
  | zero =>
    exact ⟨1, le_rfl, smoothTransition_iteratedDeriv_zero_abs_le_one⟩
  | succ k =>
    obtain ⟨C, hC, hcompact⟩ :=
      exists_smoothTransition_compact_derivative_bound (k + 1)
    refine ⟨C, hC, ?_⟩
    intro x
    by_cases hleft : x < 0
    · rw [smoothTransition_iteratedDeriv_eq_zero_of_neg (k + 1) hleft, abs_zero]
      exact zero_le_one.trans hC
    by_cases hright : 1 < x
    · rw [smoothTransition_iteratedDeriv_eq_zero_of_one_lt
        (k + 1) (Nat.succ_pos k) hright, abs_zero]
      exact zero_le_one.trans hC
    exact hcompact x ⟨le_of_not_gt hleft, le_of_not_gt hright⟩

/-- Exact affine derivative formula for the defined genuine step.
Totalized inverse makes the identity valid even at width zero; the useful
quantitative bound below assumes positive width. -/
theorem iteratedDeriv_smoothGateUpperStep (k : ℕ) (width x : ℝ) :
    iteratedDeriv k (smoothGateUpperStep width) x =
      (width⁻¹) ^ k *
        iteratedDeriv k Real.smoothTransition (1 + x / width) := by
  let f : ℝ → ℝ := fun y => Real.smoothTransition (1 + y)
  have hf : ContDiff ℝ k f :=
    Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id)
  have hfunction : smoothGateUpperStep width = fun y => f (width⁻¹ * y) := by
    funext y
    simp only [smoothGateUpperStep, f, div_eq_mul_inv, mul_comm]
  have hshift : iteratedDeriv k f =
      fun y => iteratedDeriv k Real.smoothTransition (1 + y) :=
    iteratedDeriv_comp_const_add k Real.smoothTransition 1
  rw [hfunction, iteratedDeriv_comp_const_mul hf (width⁻¹), hshift]
  simp only [div_eq_mul_inv, mul_comm]

/-- Scalar quantitative smoothness: choose C_k first, then vary any
positive width and any real argument. No derivative bound is assumed. -/
theorem exists_smoothGateUpperStep_derivative_budget (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ width : ℝ, 0 < width → ∀ x : ℝ,
      |iteratedDeriv k (smoothGateUpperStep width) x| ≤ C / width ^ k := by
  obtain ⟨C, hC, hbase⟩ := exists_smoothTransition_global_derivative_bound k
  refine ⟨C, hC, ?_⟩
  intro width hwidth x
  rw [iteratedDeriv_smoothGateUpperStep, abs_mul, abs_pow,
    abs_of_pos (inv_pos.mpr hwidth)]
  calc
    (width⁻¹) ^ k *
        |iteratedDeriv k Real.smoothTransition (1 + x / width)| ≤
        (width⁻¹) ^ k * C :=
      mul_le_mul_of_nonneg_left (hbase _) (pow_nonneg (inv_nonneg.mpr hwidth.le) k)
    _ = C / width ^ k := by rw [inv_pow, div_eq_mul_inv]; ring

end

end ImbalancedChen.P4B
