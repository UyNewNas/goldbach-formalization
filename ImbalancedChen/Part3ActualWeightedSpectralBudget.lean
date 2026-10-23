/-
SOURCEONLY 2026-10-23. UNCOMPILED append; no Lean/lake/typechecker/CI.
Load declarations (collect imports first), without duplicating smooth V2:
1. actual-normalizedF-uniform-derivative-mass-astra, f74bc534064447a2ee566e2388ce466ab3c934fc0dda4ef4ea7d0148feb22f9a
   (already includes exact smooth V2 fc9e3c7266c0291b02c8b385bb0bb4a5c9ac8e97c8cc7a6e5d086ba327fb520a).
2. compact-coordinate-IBP-and-coefficient-continuity; native-torus-period64-actual-Fourier-sampling.
3. actual-FT-sampled-weighted-lattice, 778555adf6025b8d8fc1293fa216b270f6cf4a85dcd958f6f8734dbc9fbe075f.
4. This append. All declarations below have by bodies; no derivative-mass,
   Fourier-decay, weighted-L1, spectral estimate, or reconstruction premise.
Mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Additional import to collect: Mathlib.Algebra.Order.BigOperators.Ring.Finset.
Fixed source APIs: Real.rpow_mul_natCast, one_le_rpow, rpow_inv_le_iff_of_pos;
Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul; Summable.sum_le_tsum;
UnitAddTorus.mFourier definition and pointwise Circle norm.
-/

import ImbalancedChen.Part3ActualSampledFourierLattice
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace P3ActualWeightedSpectralBudgetSourceOnly
noncomputable section

open scoped BigOperators FourierTransform ContDiff
open P3NativePeriod64SamplingSourceOnly (D4 E4 inside64 sampleFreq period64)
open P3ActualSampledLatticeSourceOnly
open ImbalancedChen.Part3.ActualNormalizedSmoothF

abbrev actualW (rho sigma : ℝ) (J0 : ℕ) : ℝ :=
  weightedL1 (normalizedF rho sigma) J0

def actualSampleCoeff (rho sigma : ℝ) (k : D4 → ℤ) : ℂ :=
  ((64 : ℝ)^4)⁻¹ • 𝓕 (normalizedF rho sigma) (sampleFreq k)

theorem actualSampleCoeff_eq (rho sigma : ℝ) (k : D4 → ℤ) :
    actualSampleCoeff rho sigma k = coeff (normalizedF rho sigma) k := by
  symm
  apply P3NativePeriod64SamplingSourceOnly.native_period64_fourier_sample
  simpa only [inside64] using normalizedF_support_inside64 rho sigma

theorem actualW_eq_sampled (rho sigma : ℝ) (J0 : ℕ) :
    actualW rho sigma J0 = ∑' k : D4 → ℤ,
      ‖actualSampleCoeff rho sigma k‖ * (1 + |(k 0 : ℝ)|)^J0 := by
  simp only [actualSampleCoeff_eq, actualW, weightedL1, testWeight]

theorem actualW_nonneg (rho sigma : ℝ) (J0 : ℕ) :
    0 ≤ actualW rho sigma J0 := by
  exact tsum_nonneg (fun k => mul_nonneg (norm_nonneg _) (testWeight_nonneg _ _))

/-- Constant is selected before rho and sigma. The actual mass supplier is
consumed here, rather than added to the assumptions of this result. -/
theorem actual_uniform_weighted_l1 (J0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| ≤ 1 →
      Summable (fun k : D4 → ℤ =>
        ‖coeff (normalizedF rho sigma) k‖ * testWeight J0 (k 0)) ∧
      actualW rho sigma J0 ≤ C * (1 + rho)^(4*(J0+3)) := by
  obtain ⟨D, hD, hm⟩ := actual_uniform_derivative_mass (4*(J0+3))
  let B := scaleCost (4*(J0+3)) * seriesCost J0 * D
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (scaleCost_nonneg _) (seriesCost_nonneg _)) hD.le
  refine ⟨1 + B, by positivity, ?_⟩
  intro rho hrho sigma hsigma
  refine ⟨(actual_normalizedF_weighted_l1 rho sigma J0).1, ?_⟩
  have hd : derivMass (normalizedF rho sigma) (4*(J0+3)) ≤
      D * (1 + rho)^(4*(J0+3)) := hm rho hrho sigma hsigma
  have hb := (weighted_l1_and_square_cost (normalizedF rho sigma) J0 D (1+rho)
    ((normalizedF_contDiff rho sigma).of_le
      (show ((4 * (J0 + 3) : ℕ) : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top))
    (normalizedF_hasCompactSupport rho sigma)
    (by simpa only [inside64] using normalizedF_support_inside64 rho sigma)
    hD.le (by linarith) hd).1
  exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith)
    (pow_nonneg (by linarith) _))

/-- X>=1 is used to pay the actual 1+rho, costing the fixed factor 2^(4L). -/
theorem actual_uniform_X_weighted_budget (J0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ rho : ℝ, 0 ≤ rho → rho ≤ X →
      ∀ sigma : ℝ, |sigma| ≤ 1 →
      Summable (fun k : D4 → ℤ =>
        ‖coeff (normalizedF rho sigma) k‖ * testWeight J0 (k 0)) ∧
      actualW rho sigma J0 ≤ C * X^(4*(J0+3)) ∧
      (actualW rho sigma J0)^2 ≤ C^2 * X^(8*(J0+3)) := by
  obtain ⟨B, hB, hb⟩ := actual_uniform_weighted_l1 J0
  refine ⟨B * 2^(4*(J0+3)), by positivity, ?_⟩
  intro X hX rho hrho hrX sigma hsigma
  obtain ⟨hsum, hw⟩ := hb rho hrho sigma hsigma
  have hp : (1+rho)^(4*(J0+3)) ≤ (2*X)^(4*(J0+3)) :=
    pow_le_pow_left₀ (by linarith) (by linarith) (4*(J0+3))
  have hbound : actualW rho sigma J0 ≤
      (B * 2^(4*(J0+3))) * X^(4*(J0+3)) := by
    calc
      actualW rho sigma J0 ≤ B * (1+rho)^(4*(J0+3)) := hw
      _ ≤ B * (2*X)^(4*(J0+3)) := mul_le_mul_of_nonneg_left hp hB.le
      _ = _ := by rw [mul_pow]; ring
  refine ⟨hsum, hbound, ?_⟩
  have hsq := mul_le_mul hbound hbound (actualW_nonneg rho sigma J0)
    (show 0 ≤ (B * 2^(4*(J0+3))) * X^(4*(J0+3)) by positivity)
  have he : (4*(J0+3))*2 = 8*(J0+3) := by omega
  simpa only [← pow_two, mul_pow, ← pow_mul, he] using hsq

theorem rpow_nat_power (x eta : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (x^eta)^n = x^((n : ℝ)*eta) := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  ring

/-- The true common range rho<=x^eta. C precedes x,eta,rho,sigma. -/
theorem actual_uniform_xeta_weighted_budget (J0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ eta : ℝ, 0 ≤ eta →
      ∀ rho : ℝ, 0 ≤ rho → rho ≤ x^eta → ∀ sigma : ℝ, |sigma| ≤ 1 →
      Summable (fun k : D4 → ℤ =>
        ‖coeff (normalizedF rho sigma) k‖ * testWeight J0 (k 0)) ∧
      actualW rho sigma J0 ≤ C * x^((4*(J0+3) : ℕ)*eta) ∧
      (actualW rho sigma J0)^2 ≤ C^2 * x^((8*(J0+3) : ℕ)*eta) := by
  obtain ⟨C, hC, hb⟩ := actual_uniform_X_weighted_budget J0
  refine ⟨C, hC, ?_⟩
  intro x hx eta heta rho hrho hrX sigma hsigma
  obtain ⟨hs, h1, h2⟩ := hb (x^eta) (Real.one_le_rpow hx heta)
    rho hrho hrX sigma hsigma
  exact ⟨hs, by simpa only [rpow_nat_power x eta (by linarith)] using h1,
    by simpa only [rpow_nat_power x eta (by linarith)] using h2⟩

def budgetOrder (J0 : ℕ) : ℕ := 8*(J0+3)+2

/-- Fix J0 FIRST, C SECOND, eta=eps/(8L+2) THIRD, threshold LAST.
The +2 pays C^2 by x^(2eta), so no circular choice is concealed. -/
theorem actual_square_budget_absorbed (J0 : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∀ rho : ℝ, 0 ≤ rho → rho ≤ x^(eps/(budgetOrder J0 : ℝ)) →
      ∀ sigma : ℝ, |sigma| ≤ 1 → (actualW rho sigma J0)^2 ≤ x^eps := by
  obtain ⟨C, hC, hb⟩ := actual_uniform_xeta_weighted_budget J0
  let eta : ℝ := eps / (budgetOrder J0 : ℝ)
  have horder : 0 < (budgetOrder J0 : ℝ) := by
    dsimp [budgetOrder]
    positivity
  have heta : 0 < eta := div_pos heps horder
  refine ⟨max 1 (C^(eta⁻¹)), le_max_left _ _, ?_⟩
  intro x hx rho hrho hrX sigma hsigma
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hCx : C ≤ x^eta :=
    (Real.rpow_inv_le_iff_of_pos hC.le hx0.le heta).mp ((le_max_right _ _).trans hx)
  have hC2 : C^2 ≤ (x^eta)^2 := by
    simpa only [pow_two] using mul_le_mul hCx hCx hC.le (Real.rpow_nonneg hx0.le eta)
  have hs := (hb x hx1 eta heta.le rho hrho hrX sigma hsigma).2.2
  have hexp : (2 : ℝ)*eta + (8*(J0+3) : ℕ)*eta = eps := by
    calc
      (2 : ℝ)*eta + (8*(J0+3) : ℕ)*eta = (budgetOrder J0 : ℝ)*eta := by
        dsimp [budgetOrder]
        push_cast
        ring
      _ = eps := by dsimp [eta]; field_simp [horder.ne']
  calc
    (actualW rho sigma J0)^2 ≤ C^2*x^((8*(J0+3) : ℕ)*eta) := hs
    _ ≤ (x^eta)^2*x^((8*(J0+3) : ℕ)*eta) :=
      mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hx0.le _)
    _ = x^eps := by
      rw [rpow_nat_power x eta hx0.le, ← Real.rpow_add hx0, Nat.cast_ofNat, hexp]

theorem native_phase_norm (k : D4 → ℤ) (z : UnitAddTorus D4) :
    ‖UnitAddTorus.mFourier k z‖ = 1 := by
  simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
    norm_prod, Circle.norm_coe, Finset.prod_const_one]

/-- Actual Fourier truncation; the remaining row-mode energy is preserved.
U is the literal row family supplied by the later packet adapter, with all
its masks. No bound on U or its spectral norm is assumed. -/
theorem actual_finite_fourier_cauchy (rho sigma : ℝ) (J0 : ℕ)
    (K : Finset (D4 → ℤ)) (z : UnitAddTorus D4) (U : (D4 → ℤ) → ℂ) :
    ‖∑ k ∈ K, actualSampleCoeff rho sigma k * UnitAddTorus.mFourier k z * U k‖^2 ≤
      actualW rho sigma J0 *
        ∑ k ∈ K, (‖actualSampleCoeff rho sigma k‖ / testWeight J0 (k 0)) * ‖U k‖^2 := by
  let a := actualSampleCoeff rho sigma
  let w := fun k : D4 → ℤ => testWeight J0 (k 0)
  have hw (k : D4 → ℤ) : 0 < w k := by dsimp [w, testWeight]; positivity
  have htri : ‖∑ k ∈ K, a k * UnitAddTorus.mFourier k z * U k‖ ≤
      ∑ k ∈ K, ‖a k‖ * ‖U k‖ := by
    calc
      _ ≤ ∑ k ∈ K, ‖a k * UnitAddTorus.mFourier k z * U k‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, native_phase_norm, mul_one]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul K
    (r := fun k => ‖a k‖*‖U k‖) (f := fun k => ‖a k‖*w k)
    (g := fun k => (‖a k‖/w k)*‖U k‖^2)
    (fun k _ => mul_nonneg (norm_nonneg _) (hw k).le)
    (fun k _ => mul_nonneg (div_nonneg (norm_nonneg _) (hw k).le) (sq_nonneg _))
    (fun k _ => by
      apply le_of_eq
      field_simp [(hw k).ne'])
  have hsum : (∑ k ∈ K, ‖a k‖*w k) ≤ actualW rho sigma J0 := by
    have hs := (actual_normalizedF_weighted_l1 rho sigma J0).1
    simpa only [a, w, actualSampleCoeff_eq, actualW, weightedL1] using!
      hs.sum_le_tsum K (fun k _ => mul_nonneg (norm_nonneg _) (testWeight_nonneg _ _))
  have henergy : 0 ≤ ∑ k ∈ K, (‖a k‖/w k)*‖U k‖^2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg
      (div_nonneg (norm_nonneg _) (hw k).le) (sq_nonneg _))
  have hsq : ‖∑ k ∈ K, a k * UnitAddTorus.mFourier k z * U k‖^2 ≤
      (∑ k ∈ K, ‖a k‖*‖U k‖)^2 := by
    simpa only [pow_two] using mul_le_mul htri htri (norm_nonneg _)
      (Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  exact hsq.trans (hcs.trans (mul_le_mul_of_nonneg_right hsum henergy))

/-- Sum the positive row squares on the original finite outer carrier.
No signed Gram block is discarded and no mode energy is replaced by a bound. -/
theorem actual_finite_row_square_cauchy {O : Type*} (S : Finset O)
    (rho sigma : ℝ) (J0 : ℕ) (K : Finset (D4 → ℤ))
    (z : O → UnitAddTorus D4) (U : O → (D4 → ℤ) → ℂ) :
    (∑ o ∈ S, ‖∑ k ∈ K,
      actualSampleCoeff rho sigma k * UnitAddTorus.mFourier k (z o) * U o k‖^2) ≤
      actualW rho sigma J0 * (∑ o ∈ S, ∑ k ∈ K,
        (‖actualSampleCoeff rho sigma k‖ / testWeight J0 (k 0)) * ‖U o k‖^2) := by
  calc
    _ ≤ ∑ o ∈ S, actualW rho sigma J0 * (∑ k ∈ K,
        (‖actualSampleCoeff rho sigma k‖ / testWeight J0 (k 0)) * ‖U o k‖^2) :=
      Finset.sum_le_sum (fun o _ => actual_finite_fourier_cauchy rho sigma J0 K (z o) (U o))
    _ = _ := by rw [Finset.mul_sum]

/-- Squaring the already-retained slow fee charges 10*kappa, exactly once. -/
theorem slow_fee_square (x kappa W : ℝ) (hx : 0 ≤ x) :
    (x^((5 : ℝ)*kappa)*W)^2 = x^((10 : ℝ)*kappa)*W^2 := by
  rw [mul_pow, rpow_nat_power x (5*kappa) hx]
  congr 2
  ring

/-- Taking the positive root returns the original 5*kappa fee. -/
theorem slow_fee_square_root (x kappa W : ℝ) (hx : 0 ≤ x) (hW : 0 ≤ W) :
    Real.sqrt (x^((10 : ℝ)*kappa)*W^2) = x^((5 : ℝ)*kappa)*W := by
  rw [← slow_fee_square x kappa W hx, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx _) hW)]

end
end P3ActualWeightedSpectralBudgetSourceOnly
