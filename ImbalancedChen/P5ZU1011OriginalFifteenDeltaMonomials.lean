import ImbalancedChen.P5ZU1011OriginalFifteenJointKappaMonomials

/-!
# Unweakened delta reserves for the same ORIGINAL15 native factors

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The physical run level remains N^(nu-2*delta), and the deterministic
factors are literally OriginalFifteenJointSelectedCompletion.factors.
The successful branch keeps the actual selected product. The below-one
branch keeps its actual full-vector rerun and c=1. Neither branch is a
factorization or desired monomial assumption. No kappa-sized proof buffer
is substituted for the original rational delta. The result is uniform
for 0<=kappa<=delta/64 and the FULL original 1<=A<=N^(1/3) interval.

The delta-scale conclusion is needed before an analytic zeta is selected.
It does not supply an atomwise fixed partition, a zeta/delta hierarchy,
auxiliary SW, or a signed Medium/PP estimate.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenDeltaMonomials

noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalSixteenNearCapBoxProfiles (nu delta)
open U1011OriginalSixteenJointNearCapCompiler (rowCoefficient)
open U1011OriginalFifteenJointSelectedSupport (runLevel selectedProduct_pos)
open U1011OriginalFifteenJointSelectedCompletion

private theorem below_one_delta_monomials {x d theta alpha A a b : ℝ}
    (hx : 1 < x) (hd : d ≤ 3 / 4096) (htheta : theta ≤ 153 / 256)
    (hA : 0 < A) (ha : 0 < a) (hb : 0 < b)
    (hAupper : A ≤ x ^ (1 / 3 : ℝ)) (haa : a ≤ A)
    (hcap : A * b ≤ x ^ (theta - 2 * d))
    (hbupper : b ≤ x ^ actualSelectedSubproductUpper alpha theta) :
    A ^ 2 * b ≤ x ^ (1 - 3 * d) ∧
      x ^ (7 * alpha / 32) * A * a * b ^ 5 ≤ x ^ (2 - 4 * d) ∧
      (A / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 ≤ x ^ (2 - 39 * d / 8) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hlogcap := (Real.le_rpow_iff_log_le (mul_pos hA hb) hx0).mp hcap
  rw [Real.log_mul hA.ne' hb.ne'] at hlogcap
  have hlogA := (Real.le_rpow_iff_log_le hA hx0).mp hAupper
  have hloga := (Real.log_le_log_iff ha hA).mpr haa
  have hlogb := (Real.le_rpow_iff_log_le hb hx0).mp hbupper
  have hb1 : Real.log b ≤ ((32 - 39 * theta) / 34) * Real.log x :=
    hlogb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le)
  have hb2 : Real.log b ≤ ((2 - 2 * theta - 7 * alpha / 32) / 3) * Real.log x :=
    hlogb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le)
  have hbudget : theta + d ≤ 2 / 3 := by linarith
  have hbudgetL := mul_le_mul_of_nonneg_right hbudget hL.le
  refine ⟨?_, ?_, ?_⟩
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (pow_ne_zero 2 hA.ne') hb.ne', Real.log_pow]
    nlinarith
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow hx0, Real.log_pow]
    nlinarith
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow (div_pos hA hb), Real.log_div hA.ne' hb.ne', Real.log_pow]
    nlinarith

/-- The literal nu and delta, rather than a kappa-reparameterized level,
already meet both critical selected-product bounds. -/
theorem original_delta_selected_critical {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (p : Policy) (hp : p.val < 15) (B : Box) (eta : ℚ) (heta : 0 < eta)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (hb : coordinates N t ∈ B.region) {kappa : ℝ}
    (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta p B eta : ℝ) / 64) :
    (nu p B eta : ℝ) ≤ 153 / 256 ∧
      (N : ℝ) ^ (2 * (nu p B eta : ℝ) - 1) ≤ (selectedProduct p t : ℝ) ∧
      (selectedProduct p t : ℝ) ≤ (N : ℝ) ^
        actualSelectedSubproductUpper (1 + 3 * kappa) (nu p B eta : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hm := U1011OriginalSixteenNearCapBoxProfiles.whole_box_nearcap_margins
    p B eta hv hw hc heta (coordinates N t) hb
  have hd : (0 : ℝ) < (delta p B eta : ℝ) := by
    exact_mod_cast (U1011OriginalSixteenNearCapBoxProfiles.rational_parameters
      p B eta hv hw hc heta).2.2.1
  have hcap : cap p (coordinates N t) ≤ (153 / 256 : ℝ) := by
    unfold cap
    rw [if_pos hp]
    by_cases hs : selectedMass p (coordinates N t) ≤ (25 / 128 : ℝ)
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have hnu : (nu p B eta : ℝ) + 64 * (delta p B eta : ℝ) ≤ 153 / 256 :=
    hm.2.2.1.trans hcap
  have hc' : (nu p B eta : ℝ) + 64 * (delta p B eta : ℝ) ≤
      min ((1 + selectedMass p (coordinates N t)) / 2)
        ((57 / 64 : ℝ) - (3 / 2 : ℝ) * selectedMass p (coordinates N t)) := by
    simpa only [cap, if_pos hp] using hm.2.2.1
  have hlo := hc'.trans (min_le_left _ _)
  have hhi := hc'.trans (min_le_right _ _)
  have hl : 2 * (nu p B eta : ℝ) - 1 ≤ selectedMass p (coordinates N t) := by linarith
  have hu : selectedMass p (coordinates N t) ≤
      actualSelectedSubproductUpper (1 + 3 * kappa) (nu p B eta : ℝ) := by
    unfold actualSelectedSubproductUpper
    apply le_min <;> linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [← selectedProduct_rpow hN ht p]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hl
  · rw [← selectedProduct_rpow hN ht p]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hu

/-- SAME constructed natural factors, with original physical delta-scale
reserves in BOTH capacity branches. All original A queries are admitted.
No hFactor/hMonomial/whole-atom license is an input. -/
theorem actual_fixed_factors_delta_monomials {N d : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (p : Policy) (hp : p.val < 15) (B : Box) (eta : ℚ) (heta : 0 < eta)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (hb : coordinates N t ∈ B.region) (hd : rowCoefficient p B eta N d ≠ 0)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta p B eta : ℝ) / 64) :
    let abc := factors p B eta N A t d
    abc.1 * abc.2.1 * abc.2.2 = fullPrefix t * d ∧
      0 < abc.1 ∧ 0 < abc.2.1 ∧ 0 < abc.2.2 ∧ (abc.1 : ℝ) ≤ A ∧
      A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤
        (N : ℝ) ^ (1 - 3 * (delta p B eta : ℝ)) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
        (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
          (N : ℝ) ^ (2 - 4 * (delta p B eta : ℝ)) ∧
      (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A *
        (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
          (N : ℝ) ^ (2 - 39 * (delta p B eta : ℝ) / 8) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hcomp := native_completion hN ht p hp B eta heta hv hw hc hb hd A hA hAupper
  obtain ⟨haN, hbN, hcN⟩ := completed_factors_positive hN ht p hp B eta heta hv hw hc hb hd A hA hAupper
  let abc := factors p B eta N A t d
  have ha : (0 : ℝ) < abc.1 := by exact_mod_cast haN
  have hb' : (0 : ℝ) < abc.2.1 := by exact_mod_cast hbN
  have hc' : (0 : ℝ) < abc.2.2 := by exact_mod_cast hcN
  have hd0 : (0 : ℝ) < (delta p B eta : ℝ) := by
    exact_mod_cast (U1011OriginalSixteenNearCapBoxProfiles.rational_parameters
      p B eta hv hw hc heta).2.2.1
  have hdc : (delta p B eta : ℝ) ≤ 3 / 4096 := by
    exact_mod_cast (NearCapRationalParameters.delta_le_cap
      (U1011OriginalSixteenNearCapBoxProfiles.G p B) (capLower p B) eta)
  obtain ⟨hnu, hlo, hhi⟩ := original_delta_selected_critical hN ht p hp B eta heta hv hw hc hb hk0 hk
  have hcap : A * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ≤
      (N : ℝ) ^ ((nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) := hcomp.2.2.1
  refine ⟨hcomp.1, haN, hbN, hcN, hcomp.2.1, ?_⟩
  by_cases hC : 1 ≤ runLevel p B eta N / (A * (selectedProduct p t : ℝ))
  · have hmiddle : abc.2.1 = selectedProduct p t := by
      simpa only [if_pos hC] using hcomp.2.2.2
    have hl : (N : ℝ) ^ (2 * (nu p B eta : ℝ) - 1) ≤ (abc.2.1 : ℝ) := by
      simpa only [hmiddle] using hlo
    have hu : (abc.2.1 : ℝ) ≤ (N : ℝ) ^
        actualSelectedSubproductUpper (1 + 3 * kappa) (nu p B eta : ℝ) := by
      simpa only [hmiddle] using hhi
    obtain ⟨h1, h2, h3⟩ := selectedPair_monomials hn hApos ha hb' hc' hcap hl hu hcomp.2.1
    exact ⟨h1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)), h2, h3⟩
  · have hrepair : abc.2.2 = 1 ∧ (abc.2.1 : ℝ) ≤ runLevel p B eta N / A ∧
        runLevel p B eta N / A < (selectedProduct p t : ℝ) := by
      simpa only [if_neg hC] using hcomp.2.2.2
    have hcap' : A * (abc.2.1 : ℝ) ≤
        (N : ℝ) ^ ((nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) := by
      simpa only [hrepair.1, Nat.cast_one, mul_one] using hcap
    have hu : (abc.2.1 : ℝ) ≤ (N : ℝ) ^
        actualSelectedSubproductUpper (1 + 3 * kappa) (nu p B eta : ℝ) :=
      (hrepair.2.1.trans hrepair.2.2.le).trans hhi
    have hr := below_one_delta_monomials hn hdc hnu hApos ha hb'
      hAupper hcomp.2.1 hcap' hu
    simpa only [hrepair.1, Nat.cast_one, one_pow, mul_one] using hr

end
end ImbalancedChen.P5Z.U1011OriginalFifteenDeltaMonomials
