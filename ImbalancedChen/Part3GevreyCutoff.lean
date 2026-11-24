/-
Copyright (c) 2026 Joris Roos. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Upstream authors: Codex.

Adapted, with changes, from TrilinearHT/Auto/Prerequisites/GevreyCutoffs.lean
at roos-j/lean-trilinearht commit 7b4209609e6a7fb9d9935973ee8541495f943660.
Source: https://github.com/roos-j/lean-trilinearht/blob/7b4209609e6a7fb9d9935973ee8541495f943660/TrilinearHT/Auto/Prerequisites/GevreyCutoffs.lean
License text: docs/licenses/Part3GevreyCutoff-Apache-2.0.txt.
-/
import Mathlib
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryPoisson

/-!
# Order-four compact cutoff with the medium dispersion plateau

The polynomial estimate for `expNegInvGlue`, normalized compact density and
step construction come from the cited upstream proof. The order-four
estimate keeps the exact binomial factor in the reflected bump, and the
cutoff is the difference of two translates of the same step.
-/

namespace ImbalancedChen.Part3.GevreyCutoff

noncomputable section

open Filter Polynomial
open scoped Topology ContDiff

noncomputable def gevreyDerivativePolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => X ^ 2 * (gevreyDerivativePolynomial n - (gevreyDerivativePolynomial n).derivative)

/-- Blueprint Lemma `lem:gevrey`: the recurrence describes all derivatives,
including at the gluing point and on the negative half-line. -/
theorem iteratedDeriv_expNegInvGlue (n : ℕ) :
    iteratedDeriv n expNegInvGlue =
      fun x => (gevreyDerivativePolynomial n).eval x⁻¹ * expNegInvGlue x := by
  induction n with
  | zero => simp [gevreyDerivativePolynomial, iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul _ x).deriv

/-- Blueprint Lemma `lem:gevrey`: derivative polynomials have degree at most `2n`. -/
theorem gevreyDerivativePolynomial_natDegree (n : ℕ) :
    (gevreyDerivativePolynomial n).natDegree ≤ 2 * n := by
  induction n with
  | zero => simp [gevreyDerivativePolynomial]
  | succ n ih =>
    have hd := Polynomial.natDegree_derivative_le (gevreyDerivativePolynomial n)
    have hs := Polynomial.natDegree_sub_le
      (gevreyDerivativePolynomial n) (gevreyDerivativePolynomial n).derivative
    have hm := Polynomial.natDegree_mul_le (p := (X ^ 2 : Polynomial ℝ))
      (q := gevreyDerivativePolynomial n - (gevreyDerivativePolynomial n).derivative)
    simp only [Polynomial.natDegree_X_pow] at hm
    change (X ^ 2 * (gevreyDerivativePolynomial n -
      (gevreyDerivativePolynomial n).derivative)).natDegree ≤ 2 * (n + 1)
    omega

/-- Coefficient bound for one step of the source's derivative recurrence. -/
theorem polynomial_derivative_step_coeff_le {p : Polynomial ℝ} {d : ℕ} {M : ℝ}
    (hd : p.natDegree ≤ d) (hM : 0 ≤ M) (hp : ∀ i, |p.coeff i| ≤ M) (i : ℕ) :
    |(X ^ 2 * (p - p.derivative)).coeff i| ≤ (d + 1 : ℝ) * M := by
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with hi
  · rw [Polynomial.coeff_sub, Polynomial.coeff_derivative]
    have hder : |(i - 2 + 1 : ℕ) * p.coeff (i - 2 + 1)| ≤ (d : ℝ) * M := by
      by_cases hk : i - 2 + 1 ≤ d
      · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul (by exact_mod_cast hk) (hp _) (abs_nonneg _) (Nat.cast_nonneg _)
      · have hz : p.coeff (i - 2 + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp only [hz, mul_zero, abs_zero]
        positivity
    have hsub := abs_sub (p.coeff (i - 2)) ((i - 2 + 1 : ℕ) * p.coeff (i - 2 + 1))
    have := hp (i - 2)
    push_cast at hder hsub
    rw [mul_comm (p.coeff (i - 2 + 1))]
    nlinarith only [this, hder, hsub]
  · simp only [abs_zero]
    positivity

/-- Blueprint Lemma `lem:gevrey`: a factorial coefficient majorant.
This slightly coarser bound still gives one fixed Gevrey order. -/
theorem gevreyDerivativePolynomial_coeff_le (n i : ℕ) :
    |(gevreyDerivativePolynomial n).coeff i| ≤ ((2 * n).factorial : ℝ) := by
  induction n generalizing i with
  | zero => simp [gevreyDerivativePolynomial, Polynomial.coeff_one]; split_ifs <;> norm_num
  | succ n ih =>
    have h := polynomial_derivative_step_coeff_le (gevreyDerivativePolynomial_natDegree n)
      (show (0 : ℝ) ≤ (2 * n).factorial by positivity) ih i
    change |(X ^ 2 * (gevreyDerivativePolynomial n -
      (gevreyDerivativePolynomial n).derivative)).coeff i| ≤ ((2 * (n + 1)).factorial : ℝ)
    refine h.trans ?_
    have heq : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [heq, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    exact le_mul_of_one_le_left (by positivity) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

/-- The exponential series controls every monomial in a derivative polynomial. -/
theorem monomial_mul_exp_neg_le_factorial {z : ℝ} (hz : 0 ≤ z) (i : ℕ) :
    z ^ i * Real.exp (-z) ≤ (i.factorial : ℝ) := by
  have hi : (0 : ℝ) < i.factorial := by positivity
  have h := (div_le_iff₀ hi).mp (Real.pow_div_factorial_le_exp z hz i)
  calc
    z ^ i * Real.exp (-z) ≤ (Real.exp z * (i.factorial : ℝ)) * Real.exp (-z) := by gcongr
    _ = i.factorial := by rw [mul_right_comm, ← Real.exp_add]; simp

/-- A quantitative derivative bound for the source's smooth gluing function. -/
theorem iteratedDeriv_expNegInvGlue_factorial_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤ (2 * n + 1 : ℝ) * ((2 * n).factorial : ℝ) ^ 2 := by
  rw [iteratedDeriv_expNegInvGlue]
  dsimp only
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    positivity
  have hxpos : 0 < x := lt_of_not_ge hx
  have hz : 0 ≤ x⁻¹ := inv_nonneg.mpr hxpos.le
  have hglue : expNegInvGlue x = Real.exp (-x⁻¹) := by
    simp [expNegInvGlue, hx]
  rw [hglue, abs_mul, abs_of_pos (Real.exp_pos _),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (gevreyDerivativePolynomial_natDegree n))]
  calc
    |∑ i ∈ Finset.range (2 * n + 1), (gevreyDerivativePolynomial n).coeff i * (x⁻¹) ^ i| *
        Real.exp (-x⁻¹) ≤
        (∑ i ∈ Finset.range (2 * n + 1),
          |(gevreyDerivativePolynomial n).coeff i * (x⁻¹) ^ i|) * Real.exp (-x⁻¹) := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (2 * n + 1),
        |(gevreyDerivativePolynomial n).coeff i| * ((x⁻¹) ^ i * Real.exp (-x⁻¹)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (pow_nonneg hz i)]
      ring
    _ ≤ ∑ _i ∈ Finset.range (2 * n + 1), ((2 * n).factorial : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ 2 * n := by simp only [Finset.mem_range] at hi; omega
      have hf : (i.factorial : ℝ) ≤ (2 * n).factorial := by exact_mod_cast Nat.factorial_le hi'
      calc
        _ ≤ ((2 * n).factorial : ℝ) * (i.factorial : ℝ) :=
          mul_le_mul (gevreyDerivativePolynomial_coeff_le n i)
            (monomial_mul_exp_neg_le_factorial hz i) (by positivity) (by positivity)
        _ ≤ _ := by rw [pow_two]; gcongr
    _ = _ := by simp

/-- Blueprint Lemma `lem:gevrey`: the gluing function has a fixed Gevrey order.
The explicit order four is sufficient for the source's existential fixed-order requirement. -/
theorem iteratedDeriv_expNegInvGlue_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤ (4 * ((n : ℝ) + 1)) ^ (4 * (n + 1)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb : 1 ≤ 4 * ((n : ℝ) + 1) := by linarith only
  have hf : ((2 * n).factorial : ℝ) ≤ (4 * ((n : ℝ) + 1)) ^ (2 * n) := by
    calc
      _ ≤ ((2 * n : ℕ) : ℝ) ^ (2 * n) := by exact_mod_cast Nat.factorial_le_pow (2 * n)
      _ ≤ _ := by push_cast; gcongr <;> linarith
  calc
    _ ≤ (2 * n + 1 : ℝ) * ((2 * n).factorial : ℝ) ^ 2 :=
      iteratedDeriv_expNegInvGlue_factorial_bound n x
    _ ≤ (4 * ((n : ℝ) + 1)) * ((4 * ((n : ℝ) + 1)) ^ (2 * n)) ^ 2 := by
      gcongr
      linarith
    _ = (4 * ((n : ℝ) + 1)) ^ (4 * n + 1) := by
      rw [← pow_mul, show 2 * n * 2 = 4 * n by omega, pow_succ]
      ring
    _ ≤ _ := pow_le_pow_right₀ hb (by omega)

/-- The compact bump `g(x)g(1-x)` in blueprint Lemma `lem:gevrey`. -/
noncomputable def gevreyBump (x : ℝ) : ℝ := expNegInvGlue x * expNegInvGlue (1 - x)

theorem gevreyBump_nonneg (x : ℝ) : 0 ≤ gevreyBump x :=
  mul_nonneg (expNegInvGlue.nonneg x) (expNegInvGlue.nonneg (1 - x))

theorem gevreyBump_pos {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < gevreyBump x :=
  mul_pos (expNegInvGlue.pos_of_pos hx.1) (expNegInvGlue.pos_of_pos (sub_pos.mpr hx.2))

theorem gevreyBump_zero {x : ℝ} (hx : x ∉ Set.Ioo (0 : ℝ) 1) : gevreyBump x = 0 := by
  by_cases h : x ≤ 0
  · simp [gevreyBump, expNegInvGlue.zero_of_nonpos h]
  · have h' : 1 ≤ x := by
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
      rcases hx with hx | hx <;> linarith only [h, hx]
    simp [gevreyBump, expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)]

theorem gevreyBump_contDiff {n : ℕ∞} : ContDiff ℝ n gevreyBump := by
  exact expNegInvGlue.contDiff.mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem gevreyBump_hasCompactSupport : HasCompactSupport gevreyBump := by
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  exact gevreyBump_zero (fun h => hx ⟨h.1.le, h.2.le⟩)
theorem iteratedDeriv_gevreyBump_order_four (n : ℕ) (x : ℝ) :
    |iteratedDeriv n gevreyBump x| ≤
      (2 : ℝ) ^ n * (4 * ((n : ℝ) + 1)) ^ (4 * (n + 2)) := by
  let B : ℝ := 4 * ((n : ℝ) + 1)
  have hder (i : ℕ) (hi : i ≤ n) (y : ℝ) :
      |iteratedDeriv i expNegInvGlue y| ≤ B ^ (4 * (i + 1)) := by
    refine (iteratedDeriv_expNegInvGlue_gevrey_bound i y).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    dsimp [B]
    have hi' : (i : ℝ) ≤ n := by exact_mod_cast hi
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hrefl (i : ℕ) :
      |iteratedDeriv i (fun y : ℝ => expNegInvGlue (1 - y)) x| =
        |iteratedDeriv i expNegInvGlue (1 - x)| := by
    simp [iteratedDeriv_comp_const_sub, abs_mul, abs_pow]
  have hleft : ContDiffAt ℝ n expNegInvGlue x := expNegInvGlue.contDiff.contDiffAt
  have hright : ContDiffAt ℝ n (fun y : ℝ => expNegInvGlue (1 - y)) x := by
    fun_prop
  change |iteratedDeriv n (fun y => expNegInvGlue y * expNegInvGlue (1 - y)) x| ≤ _
  rw [iteratedDeriv_fun_mul hleft hright]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        |(n.choose i : ℝ) * iteratedDeriv i expNegInvGlue x *
          iteratedDeriv (n - i) (fun y : ℝ => expNegInvGlue (1 - y)) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B ^ (4 * (n + 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by simp only [Finset.mem_range] at hi; omega
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), hrefl]
      calc
        _ ≤ (n.choose i : ℝ) * B ^ (4 * (i + 1)) * B ^ (4 * (n - i + 1)) := by
          gcongr
          · exact hder i hi' x
          · exact hder (n - i) (Nat.sub_le _ _) (1 - x)
        _ = _ := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
    _ = (2 : ℝ) ^ n * B ^ (4 * (n + 2)) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose n

open MeasureTheory

noncomputable def gevreyBumpIntegral : ℝ := ∫ x : ℝ, gevreyBump x

theorem gevreyBump_integrable : Integrable gevreyBump :=
  (gevreyBump_contDiff (n := 0)).continuous.integrable_of_hasCompactSupport
    gevreyBump_hasCompactSupport

theorem gevreyBumpIntegral_pos : 0 < gevreyBumpIntegral := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (gevreyBump_contDiff (n := 0)).continuous gevreyBump_integrable
    gevreyBump_nonneg (ne_of_gt (gevreyBump_pos (x := 1 / 2) (by constructor <;> norm_num)))

/-- The normalized positive bump in blueprint Lemma `lem:gevrey`. -/
noncomputable def gevreyDensity (x : ℝ) : ℝ := gevreyBump x / gevreyBumpIntegral

theorem gevreyDensity_nonneg (x : ℝ) : 0 ≤ gevreyDensity x :=
  div_nonneg (gevreyBump_nonneg x) gevreyBumpIntegral_pos.le

theorem gevreyDensity_contDiff {n : ℕ∞} : ContDiff ℝ n gevreyDensity :=
  gevreyBump_contDiff.div_const _

theorem gevreyDensity_integral : ∫ x : ℝ, gevreyDensity x = 1 := by
  simp only [gevreyDensity, integral_div]
  exact div_self gevreyBumpIntegral_pos.ne'

theorem gevreyDensity_zero {x : ℝ} (hx : x ∉ Set.Ioo (0 : ℝ) 1) : gevreyDensity x = 0 := by
  simp [gevreyDensity, gevreyBump_zero hx]
noncomputable def gevreyStep (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, gevreyDensity t

theorem gevreyStep_hasDerivAt (x : ℝ) : HasDerivAt gevreyStep (gevreyDensity x) x := by
  exact ((gevreyDensity_contDiff (n := 0)).continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem gevreyStep_deriv : deriv gevreyStep = gevreyDensity := by
  funext x
  exact (gevreyStep_hasDerivAt x).deriv

theorem gevreyStep_contDiff (n : ℕ) : ContDiff ℝ n gevreyStep := by
  have hd : Differentiable ℝ gevreyStep := fun x => (gevreyStep_hasDerivAt x).differentiableAt
  cases n with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = n + 1 from rfl]
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨hd, by simp, ?_⟩
    rw [gevreyStep_deriv]
    exact gevreyDensity_contDiff

theorem iteratedDeriv_gevreyStep_succ (n : ℕ) :
    iteratedDeriv (n + 1) gevreyStep = iteratedDeriv n gevreyDensity := by
  rw [iteratedDeriv_succ', gevreyStep_deriv]

theorem gevreyStep_zero {x : ℝ} (hx : x ≤ 0) : gevreyStep x = 0 := by
  unfold gevreyStep
  calc
    _ = ∫ _t in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_ge hx] at ht
      have ht0 : t ≤ 0 := ht.2
      exact gevreyDensity_zero (fun h => (not_lt_of_ge ht0) h.1)
    _ = 0 := by simp

theorem gevreyStep_one {x : ℝ} (hx : 1 ≤ x) : gevreyStep x = 1 := by
  unfold gevreyStep
  rw [intervalIntegral.integral_eq_integral_of_support_subset, gevreyDensity_integral]
  intro t ht
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
    by_contra h
    exact ht (gevreyDensity_zero h)
  exact ⟨ht'.1, ht'.2.le.trans hx⟩

theorem gevreyStep_monotone : Monotone gevreyStep :=
  monotone_of_hasDerivAt_nonneg gevreyStep_hasDerivAt gevreyDensity_nonneg

theorem gevreyStep_mem_Icc (x : ℝ) : gevreyStep x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · by_cases hx : x ≤ 0
    · rw [gevreyStep_zero hx]
    · have := gevreyStep_monotone (le_of_not_ge hx)
      simpa [gevreyStep_zero (le_refl (0 : ℝ))] using this
  · by_cases hx : 1 ≤ x
    · rw [gevreyStep_one hx]
    · have := gevreyStep_monotone (le_of_not_ge hx)
      simpa [gevreyStep_one (le_refl (1 : ℝ))] using this
/-- Affine rescaling multiplies the `n`th derivative by the `n`th power of the slope. -/
theorem iteratedDeriv_affine (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (c a : ℝ) :
    iteratedDeriv n (fun x => f (c * x + a)) =
      fun x => c ^ n * iteratedDeriv n f (c * x + a) := by
  have ht : ContDiff ℝ n (fun x => f (x + a)) := hf.comp (contDiff_id.add contDiff_const)
  have h := iteratedDeriv_comp_const_mul ht c
  simpa only [iteratedDeriv_comp_add_const] using h

/-- The same smooth step creates both edges of the closed unit plateau. -/
def cutoff (x : ℝ) : ℝ := gevreyStep (2 * x - 1) - gevreyStep (2 * x - 4)

theorem cutoff_mem_Icc (x : ℝ) : cutoff x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sub_nonneg.mpr (gevreyStep_monotone (by linarith)), ?_⟩
  unfold cutoff
  linarith [(gevreyStep_mem_Icc (2 * x - 1)).2, (gevreyStep_mem_Icc (2 * x - 4)).1]

theorem cutoff_eq_one {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) : cutoff x = 1 := by
  unfold cutoff
  rw [gevreyStep_one (show 1 ≤ 2 * x - 1 by linarith [hx.1]),
    gevreyStep_zero (show 2 * x - 4 ≤ 0 by linarith [hx.2]), sub_zero]

theorem cutoff_tsupport_subset : tsupport cutoff ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    apply hx
    unfold cutoff
    rw [gevreyStep_zero (show 2 * x - 1 ≤ 0 by linarith),
      gevreyStep_zero (show 2 * x - 4 ≤ 0 by linarith), sub_self]
  · by_contra h
    apply hx
    unfold cutoff
    rw [gevreyStep_one (show 1 ≤ 2 * x - 1 by linarith),
      gevreyStep_one (show 1 ≤ 2 * x - 4 by linarith), sub_self]

theorem cutoff_hasCompactSupport : HasCompactSupport cutoff :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) cutoff_tsupport_subset

theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff := by
  have hstep : ContDiff ℝ ∞ gevreyStep := contDiff_infty.mpr gevreyStep_contDiff
  exact (hstep.comp (by fun_prop)).sub (hstep.comp (by fun_prop))

private theorem iteratedDeriv_gevreyDensity_order_four (n : ℕ) (x : ℝ) :
    |iteratedDeriv n gevreyDensity x| ≤
      gevreyBumpIntegral⁻¹ * ((2 : ℝ) ^ n * (4 * ((n : ℝ) + 1)) ^ (4 * (n + 2))) := by
  have heq : gevreyDensity = fun y => gevreyBump y * gevreyBumpIntegral⁻¹ := by
    funext y
    exact div_eq_mul_inv _ _
  rw [heq, iteratedDeriv_mul_const_field, abs_mul, abs_of_pos (inv_pos.mpr gevreyBumpIntegral_pos)]
  simpa only [mul_comm _ gevreyBumpIntegral⁻¹] using mul_le_mul_of_nonneg_left
    (iteratedDeriv_gevreyBump_order_four n x) (inv_nonneg.mpr gevreyBumpIntegral_pos.le)

private theorem iteratedDeriv_cutoff_succ (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) cutoff x = (2 : ℝ) ^ (n + 1) *
      (iteratedDeriv n gevreyDensity (2 * x - 1) - iteratedDeriv n gevreyDensity (2 * x - 4)) := by
  have hstep := gevreyStep_contDiff (n + 1)
  have hleft : ContDiffAt ℝ (n + 1 : ℕ) (fun y : ℝ => gevreyStep (2 * y + -1)) x :=
    (hstep.comp (by fun_prop)).contDiffAt
  have hright : ContDiffAt ℝ (n + 1 : ℕ) (fun y : ℝ => gevreyStep (2 * y + -4)) x :=
    (hstep.comp (by fun_prop)).contDiffAt
  rw [show cutoff = (fun y => gevreyStep (2 * y + -1) - gevreyStep (2 * y + -4)) by
       funext y
       unfold cutoff
       simp only [sub_eq_add_neg], iteratedDeriv_fun_sub hleft hright,
    iteratedDeriv_affine _ hstep, iteratedDeriv_affine _ hstep,
    iteratedDeriv_gevreyStep_succ, ← mul_sub]
  rfl

/-- The exponent grows as `4n`. Keeping this order below five allows
integration by parts at the manuscript's `log(x)^5` frequency cutoff. -/
theorem cutoff_order_four : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : ℝ),
    |iteratedDeriv n cutoff x| ≤ C * (4 : ℝ) ^ n * (4 * ((n : ℝ) + 1)) ^ (4 * (n + 1)) := by
  let K := max 1 gevreyBumpIntegral⁻¹
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K, hK, fun n x => ?_⟩
  cases n with
  | zero =>
      rw [iteratedDeriv_zero, abs_of_nonneg (cutoff_mem_Icc x).1]
      norm_num
      nlinarith [(cutoff_mem_Icc x).2, le_max_left (1 : ℝ) gevreyBumpIntegral⁻¹]
  | succ n =>
      let B : ℝ := 4 * ((n : ℝ) + 1)
      have hB : 0 ≤ B := by dsimp [B]; positivity
      rw [iteratedDeriv_cutoff_succ, abs_mul, abs_of_nonneg (by positivity)]
      calc
        _ ≤ (2 : ℝ) ^ (n + 1) *
            (|iteratedDeriv n gevreyDensity (2 * x - 1)| +
              |iteratedDeriv n gevreyDensity (2 * x - 4)|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
        _ ≤ (2 : ℝ) ^ (n + 1) *
            (gevreyBumpIntegral⁻¹ * ((2 : ℝ) ^ n * B ^ (4 * (n + 2))) +
              gevreyBumpIntegral⁻¹ * ((2 : ℝ) ^ n * B ^ (4 * (n + 2)))) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (iteratedDeriv_gevreyDensity_order_four n _) (iteratedDeriv_gevreyDensity_order_four n _))
            (by positivity)
        _ = gevreyBumpIntegral⁻¹ * (4 : ℝ) ^ (n + 1) * B ^ (4 * (n + 2)) := by
          simp only [pow_succ _ n]
          rw [show (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n by rw [← mul_pow]; norm_num]
          ring
        _ ≤ _ := by
          gcongr
          · exact le_max_right _ _
          · dsimp [B]
            push_cast
            linarith

open scoped FourierTransform SchwartzMap

/-- The complex-valued cutoff used in Fourier integrals. -/
def complexCutoff : ℝ → ℂ := Complex.ofRealCLM ∘ cutoff

private theorem complexCutoff_contDiff : ContDiff ℝ ∞ complexCutoff :=
  Complex.ofRealCLM.contDiff.comp cutoff_contDiff

private theorem complexCutoff_tsupport_subset : tsupport complexCutoff ⊆ tsupport cutoff := by
  apply closure_mono
  intro x hx
  exact fun h => hx (by simp [complexCutoff, h])

/-- The same fixed cutoff as a Schwartz profile for the physical
Poisson and E1 completion APIs. -/
def cutoffSchwartz : 𝓢(ℝ, ℂ) := by
  have hcompact : HasCompactSupport complexCutoff :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (complexCutoff_tsupport_subset.trans cutoff_tsupport_subset)
  exact hcompact.toSchwartzMap complexCutoff_contDiff

@[simp] theorem cutoffSchwartz_coe : ⇑cutoffSchwartz = complexCutoff := rfl

private theorem norm_iteratedDeriv_complexCutoff (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n complexCutoff x‖ = |iteratedDeriv n cutoff x| := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hcd : ContDiffAt ℝ n cutoff x := (contDiff_infty.mp cutoff_contDiff n).contDiffAt
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hcd le_rfl

private theorem norm_iteratedDeriv_complexCutoff_eq_zero {x : ℝ}
    (hx : x ∉ Set.Icc (1 / 2 : ℝ) (5 / 2)) (n : ℕ) :
    ‖iteratedDeriv n complexCutoff x‖ = 0 := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_eq_zero]
  by_contra hm
  exact hx (cutoff_tsupport_subset
    (complexCutoff_tsupport_subset (support_iteratedFDeriv_subset n hm)))

private theorem iteratedDeriv_complexCutoff_integrable (n : ℕ) :
    Integrable (iteratedDeriv n complexCutoff) := by
  have hc : HasCompactSupport (iteratedDeriv n complexCutoff) := by
    have hsubset : tsupport (iteratedDeriv n complexCutoff) ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
      apply closure_minimal _ isClosed_Icc
      intro x hx
      by_contra! h
      exact hx (norm_eq_zero.mp (norm_iteratedDeriv_complexCutoff_eq_zero h n))
    exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsubset
  exact ((contDiff_infty.mp complexCutoff_contDiff n).continuous_iteratedDeriv' n).integrable_of_hasCompactSupport hc

private theorem norm_fourier_iteratedDeriv_le {C : ℝ} {n : ℕ}
    (hbound : ∀ x, |iteratedDeriv n cutoff x| ≤ C) (t : ℝ) :
    ‖𝓕 (iteratedDeriv n complexCutoff) t‖ ≤ 2 * C := by
  let interval := Set.Icc (1 / 2 : ℝ) (5 / 2)
  have hm : MeasurableSet interval := measurableSet_Icc
  have hi : Integrable (interval.indicator (fun _ => C)) :=
    (integrable_indicator_iff hm).mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)
  rw [Real.fourier_real_eq]
  calc
    _ ≤ ∫ x : ℝ, ‖iteratedDeriv n complexCutoff x‖ := by
      simpa only [Circle.norm_smul] using norm_integral_le_integral_norm
        (fun x : ℝ => Real.fourierChar (-(x * t)) • iteratedDeriv n complexCutoff x)
    _ ≤ ∫ x : ℝ, interval.indicator (fun _ => C) x := by
      refine integral_mono (iteratedDeriv_complexCutoff_integrable n).norm hi (fun x => ?_)
      by_cases hx : x ∈ interval
      · rw [Set.indicator_of_mem hx, norm_iteratedDeriv_complexCutoff]
        exact hbound x
      · rw [Set.indicator_of_notMem hx, norm_iteratedDeriv_complexCutoff_eq_zero hx]
    _ = 2 * C := by
      rw [integral_indicator_const _ hm, measureReal_def]
      dsimp [interval]
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
      norm_num [smul_eq_mul]

/-- Integrating by parts in the same actual cutoff keeps its order-four growth. -/
theorem cutoff_fourier_moment : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (t : ℝ),
    |t| ^ n * ‖𝓕 complexCutoff t‖ ≤ C * (16384 * ((n : ℝ) + 1) ^ 4) ^ n := by
  obtain ⟨C, hC, hder⟩ := cutoff_order_four
  refine ⟨512 * C, by positivity, fun n t => ?_⟩
  have hn := norm_fourier_iteratedDeriv_le (hder n) t
  have hreal := Real.fourier_iteratedDeriv complexCutoff_contDiff
    (fun k _ => iteratedDeriv_complexCutoff_integrable k) (n := n) (by simp)
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ = 2 * Real.pi * |t| := by
    simp [abs_of_pos Real.pi_pos, Real.norm_eq_abs]
  have hnat : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))
  rw [hreal, norm_smul, norm_pow, hnorm] at hn
  calc
    _ ≤ (2 * Real.pi * |t|) ^ n * ‖𝓕 complexCutoff t‖ := by
      gcongr
      nlinarith [Real.pi_gt_three, abs_nonneg t]
    _ ≤ 2 * (C * (4 : ℝ) ^ n * (4 * ((n : ℝ) + 1)) ^ (4 * (n + 1))) := hn
    _ = (512 * C) * (1024 * ((n : ℝ) + 1) ^ 4) ^ n * ((n : ℝ) + 1) ^ 4 := by
      have hbase : (1024 * ((n : ℝ) + 1) ^ 4) ^ n =
          (4 : ℝ) ^ n * ((4 * ((n : ℝ) + 1)) ^ 4) ^ n := by
        rw [← mul_pow]
        congr 1
        ring
      rw [hbase, pow_mul, pow_succ ((4 * ((n : ℝ) + 1)) ^ 4)]
      ring
    _ ≤ (512 * C) * (1024 * ((n : ℝ) + 1) ^ 4) ^ n * ((2 : ℝ) ^ n) ^ 4 := by gcongr
    _ = _ := by
      rw [← pow_mul, mul_comm n 4, pow_mul, mul_assoc (512 * C), ← mul_pow]
      congr 2
      ring

/-- Above the fixed `log(x)^5` cutoff, two powers of frequency can be retained
while obtaining any prescribed power of `x` in the denominator. -/
theorem cutoff_fourier_log_five (D : ℕ) : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
    (Real.log x) ^ 5 ≤ |t| → |t| ^ 2 * ‖𝓕 complexCutoff t‖ ≤ x ^ (-(D : ℝ)) := by
  obtain ⟨C, hC, hmoment⟩ := cutoff_fourier_moment
  let K : ℝ := (D : ℝ) + 1
  let B : ℝ := 16384 * (K + 4) ^ 4
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop
    (max 1 (max (B * Real.exp 1) (C * B ^ 2 * (Nat.factorial 9 : ℝ))))]
    with x hx hxlarge t ht
  let L := Real.log x
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hxlarge
  have hL : 0 < L := zero_lt_one.trans_le hL1
  let m := ⌈K * L⌉₊
  let A : ℝ := 16384 * ((m : ℝ) + 3) ^ 4
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hceil : K * L ≤ (m : ℝ) := Nat.le_ceil _
  have hceil_upper : (m : ℝ) < K * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hA_le : A ≤ B * L ^ 4 := by
    calc
      A ≤ 16384 * ((K + 4) * L) ^ 4 := by
        dsimp only [A]
        gcongr
        linarith
      _ = _ := by rw [mul_pow]; simp only [B, mul_assoc]
  have hthreshold : A ≤ Real.exp (-1) * |t| := by
    have hBL : B ≤ Real.exp (-1) * L := by
      rw [Real.exp_neg, inv_mul_eq_div]
      exact (le_div_iff₀ (Real.exp_pos _)).mpr
        ((le_max_left _ _).trans ((le_max_right _ _).trans hxlarge))
    calc
      A ≤ B * L ^ 4 := hA_le
      _ ≤ (Real.exp (-1) * L) * L ^ 4 := mul_le_mul_of_nonneg_right hBL (by positivity)
      _ = Real.exp (-1) * L ^ 5 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
  have hfront : C * A ^ 2 ≤ x := by
    have h9 : 0 < (Nat.factorial 9 : ℝ) := by positivity
    have hCL : C * B ^ 2 ≤ L / (Nat.factorial 9 : ℝ) :=
      (le_div_iff₀ h9).mpr ((le_max_right _ _).trans ((le_max_right _ _).trans hxlarge))
    calc
      _ ≤ C * (B * L ^ 4) ^ 2 := by gcongr
      _ = C * B ^ 2 * L ^ 8 := by ring
      _ ≤ (L / (Nat.factorial 9 : ℝ)) * L ^ 8 := mul_le_mul_of_nonneg_right hCL (by positivity)
      _ = L ^ 9 / (Nat.factorial 9 : ℝ) := by ring
      _ ≤ x := by
        simpa only [L, Real.exp_log hx] using Real.pow_div_factorial_le_exp L hL.le 9
  have htail := hmoment (m + 2) t
  have heq : 16384 * (((m + 2 : ℕ) : ℝ) + 1) ^ 4 = A := by
    dsimp only [A]
    push_cast
    ring
  rw [heq] at htail
  have htpos : 0 < |t| := (pow_pos hL 5).trans_le ht
  have hscale : x * Real.exp (-(K * L)) = x ^ (-(D : ℝ)) := by
    have hxexp : Real.exp L = x := Real.exp_log hx
    calc
      _ = Real.exp L * Real.exp (-(K * L)) := by rw [hxexp]
      _ = Real.exp (L - K * L) := by rw [sub_eq_add_neg, Real.exp_add]
      _ = _ := by rw [Real.rpow_def_of_pos hx]; congr 1; dsimp [K, L]; ring
  apply le_of_mul_le_mul_left _ (pow_pos htpos m)
  calc
    |t| ^ m * (|t| ^ 2 * ‖𝓕 complexCutoff t‖) = |t| ^ (m + 2) * ‖𝓕 complexCutoff t‖ := by
      rw [pow_add, mul_assoc]
    _ ≤ C * A ^ (m + 2) := htail
    _ = C * A ^ 2 * A ^ m := by rw [pow_add]; ring
    _ ≤ C * A ^ 2 * (Real.exp (-1) * |t|) ^ m := by gcongr
    _ = |t| ^ m * (C * A ^ 2 * Real.exp (-(m : ℝ))) := by
      rw [mul_pow (Real.exp (-1)) |t| m, ← Real.exp_nat_mul,
        show (m : ℝ) * -1 = -(m : ℝ) by ring]
      ring
    _ ≤ |t| ^ m * (x * Real.exp (-(K * L))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hfront (Real.exp_le_exp.mpr (neg_le_neg hceil)) (Real.exp_pos _).le hx.le)
        (pow_nonneg (abs_nonneg _) _)
    _ = _ := by rw [hscale]

/-- Absolute Poisson tail on the lattice of mesh `t = M/ℓ`. -/
def cutoffFourierTail (t H : ℝ) (h : ℤ) : ℝ :=
  if H < |(h : ℝ)| then t * ‖𝓕 complexCutoff (t * (h : ℝ))‖ else 0

/-- The absolute tail uses the same Fourier coefficients when the
cutoff is passed to a Schwartz-space Poisson identity. -/
theorem cutoffFourierTail_eq_schwartz (t H : ℝ) (h : ℤ) :
    cutoffFourierTail t H h =
      if H < |(h : ℝ)| then t * ‖(𝓕 cutoffSchwartz) (t * (h : ℝ))‖ else 0 := by
  have hFourier : ⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ)) = 𝓕 complexCutoff := by
    rw [SchwartzMap.fourier_coe, cutoffSchwartz_coe]
  rw [cutoffFourierTail, ← hFourier]

/-- The absolute omitted Poisson mass at the fixed `log(x)^5` cutoff is
`O_D(x^{-D})`, with a threshold uniform in every positive mesh. -/
theorem cutoff_fourier_log_five_tail (D : ℕ) : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
    0 < t → ∀ H : ℝ, (Real.log x) ^ 5 ≤ t * H →
      Summable (cutoffFourierTail t H) ∧
        (∑' h : ℤ, cutoffFourierTail t H h) ≤ 8 * x ^ (-(D : ℝ)) := by
  open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry in
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ), cutoff_fourier_log_five D]
    with x hx hxLog hxFourier t ht H hH
  have hlog5 : 1 ≤ Real.log x ^ 5 := one_le_pow₀ hxLog
  let W : ℝ := 4 * x ^ (-(D : ℝ))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨hsDecay, hDecay⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hnonneg (h : ℤ) : 0 ≤ cutoffFourierTail t H h := by
    unfold cutoffFourierTail
    split_ifs <;> positivity
  have hmajor (h : ℤ) : cutoffFourierTail t H h ≤ W * poissonNonzeroDecay t h := by
    by_cases hh : H < |(h : ℝ)|
    · have hfreq : (Real.log x) ^ 5 < |t * (h : ℝ)| := by
        rw [abs_mul, abs_of_pos ht]
        exact hH.trans_lt (mul_lt_mul_of_pos_left hh ht)
      have hu : 1 ≤ |t * (h : ℝ)| := hlog5.trans hfreq.le
      have hh0 : h ≠ 0 := by
        intro heq
        subst h
        norm_num at hfreq
        linarith
      have hden : 0 < (1 + |t * (h : ℝ)|) ^ 2 := by positivity
      have hterm : ‖𝓕 complexCutoff (t * (h : ℝ))‖ ≤ W / (1 + |t * (h : ℝ)|) ^ 2 := by
        apply (le_div_iff₀ hden).mpr
        calc
          _ ≤ ‖𝓕 complexCutoff (t * (h : ℝ))‖ * (2 * |t * (h : ℝ)|) ^ 2 := by
            gcongr
            linarith
          _ = 4 * (|t * (h : ℝ)| ^ 2 * ‖𝓕 complexCutoff (t * (h : ℝ))‖) := by ring
          _ ≤ W := mul_le_mul_of_nonneg_left (hxFourier _ hfreq.le) (by positivity)
      rw [cutoffFourierTail, if_pos hh, poissonNonzeroDecay, if_neg hh0]
      calc
        _ ≤ t * (W / (1 + |t * (h : ℝ)|) ^ 2) := mul_le_mul_of_nonneg_left hterm ht.le
        _ = _ := by ring
    · rw [cutoffFourierTail, if_neg hh]
      apply mul_nonneg hW
      unfold poissonNonzeroDecay
      split_ifs <;> positivity
  have hsMajor := hsDecay.mul_left W
  have hs := Summable.of_nonneg_of_le hnonneg hmajor hsMajor
  refine ⟨hs, (hs.tsum_le_tsum hmajor hsMajor).trans ?_⟩
  rw [tsum_mul_left]
  calc
    _ ≤ W * 2 := mul_le_mul_of_nonneg_left hDecay hW
    _ = _ := by dsimp [W]; ring

end

end ImbalancedChen.Part3.GevreyCutoff
