import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapModulusConvolution
import ImbalancedChen.P5ZU1011OriginalSixteenNearCapCommonSmallParameters
import ImbalancedChen.RestrictedResidueScale

/-!
# Original near-cap native sigma at the complete prime-product scale

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original native bank already proves q < N^(153/256). This module pays
the additional complete-product scale conversion required by original PP.
It keeps EVERY original trim 0 < kappa0 < kappa/(4*(1+kappa)), rather than
choosing a smaller trim. The existing common native kappa maximum pays
the conversion, because every nonempty selected bank has delta <= 3/4096.
The local ceiling is 1199/2000 < 3/5, as in the prior scalar PP frontier.

Eta, the geometric bank, kappa, kappa0, and chart constants all precede the
threshold; EVERY target, original outer mask E, complete local product x,
and nonzero SAME native sigma coefficient follow it. The empty selected
bank is handled directly, without imposing a false bound on its 1/8 default.
Strict integer support uses ceil, so an integral power wall is excluded.

This supplies a physical support precondition only. Tensor factorization,
smooth mixed Euler bounds, and the original signed PP estimate are separate.
-/

namespace ImbalancedChen.P5Z.U1011SameRhoCompleteScaleSupport

noncomputable section
open Classical Filter
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells owner_mem_selected)
open U1011OriginalSixteenNearCapCommonSmallParameters (kappaMax cellDelta)
open U1011OriginalSixteenJointNearCapModulusConvolution

def localCeiling : ℝ := 1199 / 2000

/-- The numerical local ceiling is strictly below the original long-branch
endpoint. It does not replace the original physical cap 153/256. -/
theorem localCeiling_range : 0 < localCeiling ∧ localCeiling < 3 / 5 := by
  norm_num [localCeiling]

/-- This bound is obtained from the actual finite bank, not added to the
permitted common kappa interval. The empty-bank default is excluded here. -/
theorem common_kappa_bound {n : ℕ} (eta : ℚ)
    (hbank : (selectedCells n).Nonempty) {kappa : ℝ}
    (hk : kappa ≤ (kappaMax n eta : ℝ)) : kappa ≤ 3 / 262144 := by
  obtain ⟨j, hj⟩ := hbank
  have hcell : (kappaMax n eta : ℝ) ≤ (cellDelta n eta j : ℝ) / 64 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_cell eta j hj
  have hdelta : cellDelta n eta j ≤ (3 / 4096 : ℚ) :=
    NearCapRationalParameters.delta_le_cap _ _ _
  have hdeltaR : (cellDelta n eta j : ℝ) ≤ 3 / 4096 := by exact_mod_cast hdelta
  linarith

/-- All original buffered trims fit the local ceiling. No particular trim
such as kappa/(8*(1+kappa)) is selected here. -/
theorem original_trim_power_gap {kappa kappa0 : ℝ}
    (hk0 : 0 < kappa) (hk : kappa ≤ 3 / 262144)
    (htrim : kappa0 < kappa / (4 * (1 + kappa))) :
    (153 / 256 : ℝ) < (1 - kappa0) * localCeiling := by
  have hden : 0 < 1 + kappa := by linarith
  have hfrac : kappa / (4 * (1 + kappa)) ≤ kappa / 4 :=
    div_le_div_of_nonneg_left hk0.le (by norm_num) (by linarith)
  have hsmall : kappa0 < 1 / 10000 := by linarith [htrim.trans_le hfrac]
  dsimp [localCeiling]
  linarith

/-- A single threshold covers the whole original complete-scale strip.
The fixed lower chart constant is absorbed using the strict exponent gap. -/
theorem exists_original_completeScale_threshold
    {c C kappa kappa0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hk0 : 0 < kappa) (hk : kappa ≤ 3 / 262144)
    (htrim : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      1 < x ∧ C⁻¹ * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
        (N : ℝ) ^ (153 / 256 : ℝ) ≤ x ^ localCeiling := by
  obtain ⟨_, N1, hN1, hscale⟩ :=
    exists_manuscript_restrictedResidueScale_threshold hc hC hk0 htrim
  have hgap := original_trim_power_gap hk0 hk htrim
  have hcpow : 0 < c ^ localCeiling := Real.rpow_pos_of_pos hc _
  obtain ⟨N2, hpower⟩ := Filter.eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (c ^ localCeiling)⁻¹ hgap)
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN x hlow hupp
  obtain ⟨hx, hresLo, hresHi⟩ :=
    hscale N ((le_max_left _ _).trans hN) x hlow hupp
  refine ⟨hx, hresLo, hresHi, ?_⟩
  have hpaid : (N : ℝ) ^ (153 / 256 : ℝ) ≤
      c ^ localCeiling * (N : ℝ) ^ ((1 - kappa0) * localCeiling) := by
    have hm := mul_le_mul_of_nonneg_left
      (hpower N ((le_max_right _ _).trans hN)) hcpow.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hcpow.ne', one_mul] using hm
  calc
    _ ≤ c ^ localCeiling * (N : ℝ) ^ ((1 - kappa0) * localCeiling) := hpaid
    _ = (c * (N : ℝ) ^ (1 - kappa0)) ^ localCeiling := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _),
        ← Real.rpow_mul (Nat.cast_nonneg N)]
    _ ≤ x ^ localCeiling := Real.rpow_le_rpow
      (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hlow localCeiling_range.1.le

private theorem selected_bank_nonempty_of_sigma_ne_zero
    {n N q : ℕ} {eta : ℚ} {E : ℕ × ℕ → Prop}
    (hq : sigma n N eta E q ≠ 0) : (selectedCells n).Nonempty := by
  have hmem : q ∈ modulusSupport n N eta E := by
    by_contra hnot
    exact hq (sigma_zero_off_support hnot)
  obtain ⟨m, hm, _⟩ := Finset.mem_image.mp hmem
  have ht := (Finset.mem_sigma.mp hm).1
  have htag := (Finset.mem_filter.mp ht).2
  exact ⟨_, owner_mem_selected htag⟩

/-- Literal original supplier support, with the original common kappa and
all original buffered trims. The same eta-native sigma is used, and no
support licence is a caller premise. Uniformity includes EVERY outer mask.
The strict ceil bound excludes equality at integral power endpoints. -/
theorem exists_sameSigma_completeScale_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    {c C kappa kappa0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hk0 : 0 < kappa) (hk : kappa ≤ (kappaMax n eta : ℝ))
    (htrim0 : 0 < kappa0) (htrim : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      1 < x ∧ C⁻¹ * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
        ∀ (E : ℕ × ℕ → Prop) (q : ℕ), sigma n N eta E q ≠ 0 →
          (q : ℝ) < x ^ localCeiling ∧ q < Nat.ceil (x ^ localCeiling) := by
  by_cases hbank : (selectedCells n).Nonempty
  · obtain ⟨N0, hN0, hscale⟩ := exists_original_completeScale_threshold
      hc hC hk0 (common_kappa_bound eta hbank hk) htrim
    refine ⟨N0, hN0, ?_⟩
    intro N hN x hlow hupp
    obtain ⟨hx, hlo, hhi, hcap⟩ := hscale N hN x hlow hupp
    refine ⟨hx, hlo, hhi, ?_⟩
    intro E q hq
    have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N0) hN
    have hphysical := (sigma_nonzero_profile hNN heta hq).2.2.2.2
    have hlocal := hphysical.trans_le hcap
    exact ⟨hlocal, Nat.lt_ceil.mpr hlocal⟩
  · obtain ⟨_, N0, hN0, hscale⟩ :=
      exists_manuscript_restrictedResidueScale_threshold hc hC hk0 htrim
    refine ⟨N0, hN0, ?_⟩
    intro N hN x hlow hupp
    obtain ⟨hx, hlo, hhi⟩ := hscale N hN x hlow hupp
    exact ⟨hx, hlo, hhi, fun E q hq =>
      (hbank (selected_bank_nonempty_of_sigma_ne_zero hq)).elim⟩

end
end ImbalancedChen.P5Z.U1011SameRhoCompleteScaleSupport
