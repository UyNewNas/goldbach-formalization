import ImbalancedChen.P5ZU1011SameRhoCompleteScaleSupport
import ImbalancedChen.P5ZU1011OriginalFifteenJointKappaMonomials

/-!
# Original native factors pay complete-product monomials

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This advances beyond a modulus-support bound. Every active ORIGINAL15 mark
of the SAME all16 eta-native sigma has its existing deterministic natural
three-factor decomposition, with its product equal to the original physical
modulus. The three physical reserves pay three complete-local inequalities
at x >= c*N^(1-kappa0). The middle residue factor remains N^(7/32), not
x^(7/32). All original buffered trims kappa0<kappa/(4*(1+kappa)) are kept.

The original A range is retained literally. This does not assert that an
arbitrary HB block supplies such an A, that this tuple allocation is constant
on a whole atom, or that the W branch has these ORIGINAL15 factors. Those
are distinct eligibility/tensor tasks. No signed PP estimate is a premise.
-/

namespace ImbalancedChen.P5Z.U1011SameRhoCompleteScaleFactors

noncomputable section
open Classical Filter
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells P5U1011JointOverlap
open U1011OriginalSixteenStaticNativeCompiler (ownerBox selectedPolicy boxPolicy_certificate)
open U1011OriginalSixteenNearCapCommonSmallParameters (kappaMax)
open U1011OriginalSixteenJointNearCapCompiler
open U1011OriginalSixteenJointNearCapModulusConvolution
open U1011OriginalFifteenJointSelectedCompletion (factors)
open U1011OriginalFifteenJointKappaMonomials

/-- These strict gaps pay FIXED chart constants. They cover the full
original trim interval, rather than selecting one convenient trim. -/
theorem original_trim_three_gaps {kappa kappa0 : ℝ}
    (hk : 0 < kappa) (ht0 : 0 < kappa0)
    (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    1 - 3 * kappa / 2 < (1 - kappa0) * (1 - kappa) ∧
      2 - 3 * kappa / 2 < (1 - kappa0) * (2 - kappa) ∧
      2 - kappa < (1 - kappa0) * (2 - kappa / 2) := by
  have hfrac : kappa / (4 * (1 + kappa)) ≤ kappa / 4 :=
    div_le_div_of_nonneg_left hk.le (by norm_num) (by linarith)
  have hsmall := ht.trans_le hfrac
  have hprod := mul_pos hk ht0
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem eventually_power_le_completeScale {a b c kappa0 : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (hgap : a < (1 - kappa0) * b) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → (N : ℝ) ^ a ≤ x ^ b := by
  have hcpow : 0 < c ^ b := Real.rpow_pos_of_pos hc _
  filter_upwards [eventually_const_mul_rpow_le_rpow (c ^ b)⁻¹ hgap] with N hN
  intro x hlow
  have hpaid : (N : ℝ) ^ a ≤ c ^ b * (N : ℝ) ^ ((1 - kappa0) * b) := by
    have hm := mul_le_mul_of_nonneg_left hN hcpow.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hcpow.ne', one_mul] using hm
  calc
    _ ≤ c ^ b * (N : ℝ) ^ ((1 - kappa0) * b) := hpaid
    _ = (c * (N : ℝ) ^ (1 - kappa0)) ^ b := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _),
        ← Real.rpow_mul (Nat.cast_nonneg N)]
    _ ≤ x ^ b := Real.rpow_le_rpow
      (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hlow hb

/-- One threshold pays all three numerical conditions, before any target
or complete-product scale is inspected. -/
theorem exists_three_monomial_threshold {c kappa kappa0 : ℝ}
    (hc : 0 < c) (hk0 : 0 < kappa) (hk : kappa ≤ 1 / 8)
    (ht0 : 0 < kappa0) (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x →
      (N : ℝ) ^ (1 - 3 * kappa / 2) ≤ x ^ (1 - kappa) ∧
        (N : ℝ) ^ (2 - 3 * kappa / 2) ≤ x ^ (2 - kappa) ∧
        (N : ℝ) ^ (2 - kappa) ≤ x ^ (2 - kappa / 2) := by
  obtain ⟨hg1, hg2, hg3⟩ := original_trim_three_gaps hk0 ht0 ht
  have h1 := eventually_power_le_completeScale hc (by linarith : 0 ≤ 1 - kappa) hg1
  have h2 := eventually_power_le_completeScale hc (by linarith : 0 ≤ 2 - kappa) hg2
  have h3 := eventually_power_le_completeScale hc (by linarith : 0 ≤ 2 - kappa / 2) hg3
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (h1.and (h2.and h3))
  refine ⟨max 2 N0, le_max_left _ _, ?_⟩
  intro N hN x hlow
  have h := hN0 N ((le_max_right _ _).trans hN)
  exact ⟨h.1 x hlow, h.2.1 x hlow, h.2.2 x hlow⟩

/-- A real native-mark eligibility conclusion, beyond q-support.
The threshold precedes every original low/high mask, active physical mark,
complete local product x, and factorization query A. The same original15
factors supply all three local numerical inequalities simultaneously. -/
theorem exists_sameSigma_original15_local_factors_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    {c kappa kappa0 : ℝ} (hc : 0 < c) (hk0 : 0 < kappa)
    (hk : kappa ≤ (kappaMax n eta : ℝ)) (ht0 : 0 < kappa0)
    (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ (E : ℕ × ℕ → Prop) (m : Mark), m ∈ marks n N eta E →
      (selectedPolicy n N m.1).val < 15 → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → ∀ A : ℝ,
      (N : ℝ) ^ kappa ≤ A → A ≤ (N : ℝ) ^ (1 / 3 - kappa / 2) →
      let abc := factors (selectedPolicy n N m.1) (ownerBox n N m.1) eta N A m.1 m.2
      abc.1 * abc.2.1 * abc.2.2 = modulus m ∧ (abc.1 : ℝ) ≤ A ∧
        A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (1 - kappa) ∧
        (N : ℝ) ^ (7 / 32 : ℝ) * A * (abc.1 : ℝ) *
          (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - kappa) ∧
        (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A *
          (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
            x ^ (2 - kappa / 2) := by
  have hmax : (kappaMax n eta : ℝ) ≤ 1 / 8 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_eighth n eta
  obtain ⟨N0, hN0, hpay⟩ := exists_three_monomial_threshold hc hk0 (hk.trans hmax) ht0 ht
  refine ⟨N0, hN0, ?_⟩
  intro N hN E m hm hp x hlow A hAlo hAhi
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N0) hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNN
  obtain ⟨htuple, hrow⟩ := Finset.mem_sigma.mp hm
  obtain ⟨_, hd⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hsource, htag⟩ := Finset.mem_filter.mp htuple
  let p := selectedPolicy n N m.1
  let B := ownerBox n N m.1
  have hcert := (boxPolicy_certificate B htag).2
  have hgeometry := owner_mem n
    (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hNN hsource)
  have hbox : coordinates N m.1 ∈ B.region := cell_subset_closed_box n _ hgeometry
  have hkcell :=
    (U1011OriginalSixteenNearCapCommonSmallParameters.actual_selected_common_bounds
      eta htag hk0 hk).2.1
  have hdata := actual_completed_kappa_monomials hNN hsource p hp B eta heta
    (gridBox_valid n _) (gridBox_lower_positive n _ 3) hcert hbox hd hk0 hkcell hAlo hAhi
  obtain ⟨hpay1, hpay2, hpay3⟩ := hpay N hN x hlow
  let abc := factors p B eta N A m.1 m.2
  have hApos : 0 < A :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) kappa).trans_le hAlo
  have hspectral : (N : ℝ) ^ (7 / 32 : ℝ) ≤ (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) :=
    Real.rpow_le_rpow_of_exponent_le hNr.le (by nlinarith)
  have hcommon : 0 ≤ A * (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 := by
    positivity
  have hsecond : (N : ℝ) ^ (7 / 32 : ℝ) * A * (abc.1 : ℝ) *
      (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
        (N : ℝ) ^ (2 - 3 * kappa / 2) := by
    have hh := mul_le_mul_of_nonneg_right hspectral hcommon
    have hh' : (N : ℝ) ^ (7 / 32 : ℝ) * A * (abc.1 : ℝ) *
        (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
        (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
          (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 := by
      simpa only [mul_assoc] using hh
    exact hh'.trans hdata.2.2.2.1
  exact ⟨hdata.1, hdata.2.1, hdata.2.2.1.trans hpay1,
    hsecond.trans hpay2, hdata.2.2.2.2.trans hpay3⟩

end
end ImbalancedChen.P5Z.U1011SameRhoCompleteScaleFactors
