import ImbalancedChen.Part3CleanBetaLargeGCDMajorant
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual large-beta-gcd raw payment at polynomially moving residues

Pure divisor-moment/subpower proofs extracted into an isolated namespace
from fixed goldbach 09b97db5764ade1246bfb77206baa1b124760958:
* WeilBridge.lean:69-77, source SHA256
  96022af91efc4467a5776267f068e08d6b8b462f0886e33568033993b649d87f;
* TauPointwise.lean:17-76, source SHA256
  ab97eb2c5a7b4e1b2dc349ce1daff46eebcc0988a52aca1f3ddfc86df0899333.
Both blobs match the fixed commit. No conditional Weil theorem, WeilBridge
module or unbuilt raw-estimate chain is imported.

For fixed kappa and epsilon, constants precede every admissible atom,
beta pair, common-smoothing point and large-gcd threshold. The actual
bound |a|<=scale^(1+kappa) is retained. Choosing K=max(1,1+kappa) and
subpower epsilon/(2*K) pays each tau_4 difference at scale^(epsilon/2).
Neither the common U/support nor the large-gcd threshold is rescaled.
The signed-divisor beta exception remains explicit and unestimated.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace PolynomialResidueDivisorBound

theorem fouvryTau_pow_pointwise (k r : ℕ) (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n) :
    (fouvryTau k n : ℝ) ^ r ≤
      (n : ℝ) * (1 + Real.log n) ^ (k ^ r - 1) := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 n, (fouvryTau k m : ℝ) ^ r :=
      single_le_sum (fun _ _ ↦ by positivity) (mem_Ioc.mpr ⟨hn, le_rfl⟩)
    _ ≤ _ := by
      simpa only [Nat.floor_natCast] using
        sum_fouvryTau_pow_le_real (r := r) hk (show (1 : ℝ) ≤ n by exact_mod_cast hn)

theorem eventually_fouvryTau_le_rpow {k : ℕ} (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (fouvryTau k n : ℝ) ≤ (n : ℝ) ^ ε := by
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / ε)
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    simp only [Nat.cast_zero] at hr
    have := one_div_pos.mpr hε
    linarith
  have hgap : 0 < ε * r - 1 := by
    have := (div_lt_iff₀ hε).mp hr
    nlinarith
  let K := k ^ r - 1
  have hs : (fun x : ℝ ↦ Real.log x ^ K) =o[atTop]
      (fun x ↦ x ^ (ε * r - 1)) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (K : ℕ) hgap
  have hb := (hs.const_mul_left ((2 : ℝ) ^ K)).bound (by norm_num : (0 : ℝ) < 1)
  have hevent : ∀ᶠ x : ℝ in atTop,
      1 ≤ Real.log x ∧ 1 ≤ x ∧ 2 ^ K * Real.log x ^ K ≤ x ^ (ε * r - 1) := by
    filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℝ)] with x hx hl hx1
    refine ⟨hl, hx1, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (2 : ℝ) ^ K * Real.log x ^ K),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _), one_mul] using hx
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hevent,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  rcases hn with ⟨hlog, hnR, hpay⟩
  have hn0 : (0 : ℝ) < n := by positivity
  apply le_of_pow_le_pow_left₀ hr0 (Real.rpow_nonneg hn0.le ε)
  calc
    (fouvryTau k n : ℝ) ^ r ≤ (n : ℝ) * (1 + Real.log n) ^ K :=
      fouvryTau_pow_pointwise k r hk (by omega)
    _ ≤ (n : ℝ) * (2 * Real.log n) ^ K := by gcongr; linarith
    _ = (n : ℝ) * (2 ^ K * Real.log n ^ K) := by rw [mul_pow]
    _ ≤ (n : ℝ) * (n : ℝ) ^ (ε * r - 1) :=
      mul_le_mul_of_nonneg_left hpay hn0.le
    _ = ((n : ℝ) ^ ε) ^ r := by
      rw [← Real.rpow_mul_natCast hn0.le, mul_comm (n : ℝ),
        ← Real.rpow_add_one hn0.ne', sub_add_cancel]

/-- The constant depends only on the fixed order and exponent. -/
theorem fouvryTau_le_const_rpow {k : ℕ} (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (fouvryTau k n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_fouvryTau_le_rpow hk hε)
  let C : ℝ := 1 + ∑ n ∈ range N, (fouvryTau k n : ℝ)
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C, zero_lt_one.trans_le hC, fun n hn ↦ ?_⟩
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hsmall : (fouvryTau k n : ℝ) ≤ C := by
      have := single_le_sum (f := fun n ↦ (fouvryTau k n : ℝ))
        (s := range N) (fun _ _ ↦ by positivity) (mem_range.mpr (by omega : n < N))
      dsimp [C]
      linarith
    exact hsmall.trans (le_mul_of_one_le_right (by linarith)
      (Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n) hε.le))


end PolynomialResidueDivisorBound

private theorem admissible_one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

/-- A fixed power of the original scale controls the actual signed differences. -/
private theorem actual_difference_le_polynomial
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {m n : ℕ}
    (hn : n ∈ d.betaCarrier) (hm : d.commonSmoothWeight m ≠ 0) :
    ((((m : ℤ) * n - d.residue).natAbs : ℕ) : ℝ) ≤
      7 * d.scale ^ (max 1 (1 + kappa)) := by
  obtain ⟨hU, _, _, _, _, _, _, ha, _⟩ := hd
  have hx := admissible_one_le_scale hd
  have hxK : d.scale ≤ d.scale ^ (max 1 (1 + kappa)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (le_max_left (1 : ℝ) (1 + kappa))
  have haK : |(d.residue : ℝ)| ≤ d.scale ^ (max 1 (1 + kappa)) := by
    have ha' : |(d.residue : ℝ)| ≤ d.scale ^ (1 + kappa) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using ha
    exact ha'.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  have hms : (m : ℝ) ∈ tsupport (CommonSmoothCutoff.scaledDyadicCutoff d.U) :=
    subset_closure hm
  have hmhi := (CommonSmoothCutoff.scaledDyadicCutoff_tsupport_subset
    (lt_of_lt_of_le zero_lt_one hU) hms).2
  have hnhi : (n : ℝ) ≤ 2 * d.V :=
    (show (n : ℝ) ≤ (Nat.floor (2 * d.V) : ℝ) by
      exact_mod_cast (Finset.mem_Icc.mp hn).2).trans
        (Nat.floor_le (by linarith [hd.2.1] : 0 ≤ 2 * d.V))
  have hmn : (m : ℝ) * n ≤ 6 * d.scale := by
    calc
      _ ≤ (3 * d.U) * (2 * d.V) :=
        mul_le_mul hmhi hnhi (Nat.cast_nonneg _) (by linarith)
      _ = _ := by unfold MediumAtom.scale; ring
  calc
    _ = |(m : ℝ) * n - d.residue| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      rfl
    _ ≤ |(m : ℝ) * n| + |(d.residue : ℝ)| := abs_sub _ _
    _ ≤ 6 * d.scale + d.scale ^ (max 1 (1 + kappa)) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) * n)]
      exact add_le_add hmn haK
    _ ≤ _ := by linarith

/-- Uniform subpower payment for the actual good-beta difference, with the
original polynomial residue range and original common smoothing unchanged. -/
theorem actual_tauFour_difference_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ m n : ℕ,
        n ∈ d.betaCarrier → d.commonSmoothWeight m ≠ 0 → d.cleanedBeta n ≠ 0 →
          (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) ≤
            C * d.scale ^ (epsilon / 2) := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let eta : ℝ := epsilon / (2 * K)
  have heta : 0 < eta := div_pos hepsilon (mul_pos (by norm_num) hKpos)
  have hKeta : K * eta = epsilon / 2 := by dsimp [eta]; field_simp [hKpos.ne']; ring
  obtain ⟨D, hD, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 4) (by norm_num) heta
  refine ⟨D * (7 : ℝ) ^ eta, by positivity, fun B sigma c0 d hd m n hn hm hb ↦ ?_⟩
  have hne : (m : ℤ) * n - d.residue ≠ 0 := by
    intro h
    exact (d.cleanedBeta_ne_zero_not_dvd hb) ⟨m, by nlinarith⟩
  have hx := admissible_one_le_scale hd
  calc
    _ ≤ D * (((m : ℤ) * n - d.residue).natAbs : ℝ) ^ eta :=
      hbound _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
    _ ≤ D * (7 * d.scale ^ K) ^ eta :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (actual_difference_le_polynomial hd hn hm) heta.le)
        hD.le
    _ = (D * (7 : ℝ) ^ eta) * d.scale ^ (epsilon / 2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7) (Real.rpow_nonneg (by linarith) _),
        ← Real.rpow_mul (by linarith : 0 ≤ d.scale), hKeta]
      ring

private theorem commonSmoothWeight_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ m ∈ d.commonSmoothCarrier, d.commonSmoothWeight m) ≤ 5 * d.U := by
  calc
    _ ≤ ∑ _m ∈ d.commonSmoothCarrier, (1 : ℝ) :=
      Finset.sum_le_sum (fun _ _ ↦ CommonSmoothCutoff.scaledDyadicCutoff_le_one _ _)
    _ = (Nat.ceil (3 * d.U) : ℝ) + 1 := by simp [MediumAtom.commonSmoothCarrier]
    _ ≤ _ := by
      have := Nat.ceil_lt_add_one (by linarith [hd.1] : 0 ≤ 3 * d.U)
      linarith [hd.1]

def MediumAtom.commonLargeBetaGCDCleanMass (d : MediumAtom) (Y : ℝ) : ℝ :=
  ∑ n₁ ∈ d.betaCarrier, ∑ n₂ ∈ d.betaCarrier,
    if Y < (n₁.gcd n₂ : ℝ) then ‖d.cleanedBeta n₁‖ * ‖d.cleanedBeta n₂‖ else 0

/-- Actual finite-majorant payment at the ORIGINAL scale, before any large-gcd
pair-mass bound or estimate of the removed signed-divisor exception. -/
theorem commonLargeBetaGCDDivisorMajorant_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ,
        d.commonLargeBetaGCDDivisorMajorant Y ≤
          C * d.U * d.scale ^ epsilon * d.commonLargeBetaGCDCleanMass Y := by
  obtain ⟨C, hC, hbound⟩ := actual_tauFour_difference_subpower kappa hepsilon
  refine ⟨5 * C ^ 2, by positivity, fun B sigma c0 d hd Y ↦ ?_⟩
  have hx := admissible_one_le_scale hd
  unfold MediumAtom.commonLargeBetaGCDDivisorMajorant MediumAtom.commonLargeBetaGCDCleanMass
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n₁ hn₁
  apply Finset.sum_le_sum
  intro n₂ hn₂
  by_cases hy : Y < (n₁.gcd n₂ : ℝ)
  · simp only [if_pos hy]
    by_cases hb₁ : d.cleanedBeta n₁ = 0
    · simp only [hb₁, norm_zero, zero_mul, mul_zero]
    by_cases hb₂ : d.cleanedBeta n₂ = 0
    · simp only [hb₂, norm_zero, mul_zero, zero_mul]
    have hinner :
        (∑ m ∈ d.commonSmoothCarrier, d.commonSmoothWeight m *
          (fouvryTau 4 (((m : ℤ) * n₁ - d.residue).natAbs) : ℝ) *
            (fouvryTau 4 (((m : ℤ) * n₂ - d.residue).natAbs) : ℝ)) ≤
              (∑ m ∈ d.commonSmoothCarrier, d.commonSmoothWeight m) * C ^ 2 *
                d.scale ^ epsilon := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro m _
      by_cases hm : d.commonSmoothWeight m = 0
      · simp only [hm, zero_mul]
      have hp :
          (fouvryTau 4 (((m : ℤ) * n₁ - d.residue).natAbs) : ℝ) *
            (fouvryTau 4 (((m : ℤ) * n₂ - d.residue).natAbs) : ℝ) ≤
              C ^ 2 * d.scale ^ epsilon := by
        calc
          _ ≤ (C * d.scale ^ (epsilon / 2)) * (C * d.scale ^ (epsilon / 2)) :=
            mul_le_mul (hbound B sigma c0 d hd m n₁ hn₁ hm hb₁)
              (hbound B sigma c0 d hd m n₂ hn₂ hm hb₂)
              (Nat.cast_nonneg _) (by positivity)
          _ = _ := by
            rw [mul_mul_mul_comm, ← Real.rpow_add (by linarith : 0 < d.scale),
              show epsilon / 2 + epsilon / 2 = epsilon by ring, pow_two]
      calc
        _ = d.commonSmoothWeight m *
            ((fouvryTau 4 (((m : ℤ) * n₁ - d.residue).natAbs) : ℝ) *
              (fouvryTau 4 (((m : ℤ) * n₂ - d.residue).natAbs) : ℝ)) := by ring
        _ ≤ d.commonSmoothWeight m * (C ^ 2 * d.scale ^ epsilon) :=
          mul_le_mul_of_nonneg_left hp (d.commonSmoothWeight_nonneg m)
        _ = _ := by ring
    calc
      _ ≤ (‖d.cleanedBeta n₁‖ * ‖d.cleanedBeta n₂‖) *
          ((∑ m ∈ d.commonSmoothCarrier, d.commonSmoothWeight m) * C ^ 2 *
            d.scale ^ epsilon) :=
        mul_le_mul_of_nonneg_left hinner (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ (‖d.cleanedBeta n₁‖ * ‖d.cleanedBeta n₂‖) *
          ((5 * d.U) * C ^ 2 * d.scale ^ epsilon) := by
        gcongr
        exact commonSmoothWeight_sum_le hd
      _ = _ := by ring
  · simp only [if_neg hy, mul_zero, le_refl]

/-- The original beta is retained, and its remaining exception is visible. -/
theorem commonLargeBetaGCDW_polynomial_residue_raw_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ,
        ‖d.commonLargeBetaGCDW Y‖ ≤
          C * d.U * d.scale ^ epsilon * d.commonLargeBetaGCDCleanMass Y +
            ‖d.commonLargeBetaGCDException Y‖ := by
  obtain ⟨C, hC, hbound⟩ := commonLargeBetaGCDDivisorMajorant_subpower kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y ↦ ?_⟩
  exact (d.commonLargeBetaGCDW_norm_le_majorant_add_exception hd Y).trans
    (add_le_add_right (hbound B sigma c0 d hd Y) _)

end

end ImbalancedChen.Part3
