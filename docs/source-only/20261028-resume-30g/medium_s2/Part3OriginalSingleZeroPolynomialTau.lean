import ImbalancedChen.Part3OriginalActualSingleZeroSource
import ImbalancedChen.Part3OriginalS2RoughScalePayment
import Mathlib.Tactic

/-! Uniform classical subpower payment for the actual single-zero
factor/shift divisors. Zero shifts are dealt with separately, never
fed to the positive-integer divisor theorem. SOURCE ONLY / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalSingleZeroPolynomialTau

open ImbalancedChen.Part3
open ImbalancedChen.Part3.PolynomialResidueDivisorBound
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumSingleZeroFiber20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Classical Finset

noncomputable section

/-- The fixed polynomial exponent includes the moving residue. C is
chosen before every actual atom, key, n,m and nonzero signed shift. -/
theorem exists_uniform_polynomial_tau (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : ℝ) (n : ℕ), 1 ≤ x → 0 < n →
      (n : ℝ) ≤ 8 * x ^ (max 1 (1 + kappa)) →
      (n.divisors.card : ℝ) ≤ C * x ^ epsilon := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let eta := epsilon / K
  have heta : 0 < eta := div_pos hepsilon hK
  obtain ⟨C0, hC0, hbound⟩ := fouvryTau_le_const_rpow (k := 2) (by norm_num) heta
  let C := 1 + C0 * (8 : ℝ) ^ eta
  refine ⟨C, by
    dsimp [C]
    exact le_add_of_nonneg_right (mul_nonneg hC0.le (Real.rpow_nonneg (by norm_num) eta)), ?_⟩
  intro x n hx hn hpoly
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpower : (8 * x ^ K) ^ eta = (8 : ℝ) ^ eta * x ^ epsilon := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (Real.rpow_nonneg hxpos.le _),
      ← Real.rpow_mul hxpos.le]
    congr 1
    dsimp [eta]
    field_simp [hK.ne']
  calc
    (n.divisors.card : ℝ) = (fouvryTau 2 n : ℝ) := by rw [fouvryTau_two]
    _ ≤ C0 * (n : ℝ) ^ eta := hbound n hn
    _ ≤ C0 * (8 * x ^ K) ^ eta :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hpoly heta.le) hC0.le
    _ = (C0 * (8 : ℝ) ^ eta) * x ^ epsilon := by rw [hpower]; ring
    _ ≤ C * x ^ epsilon := by
      dsimp [C]
      nlinarith [Real.rpow_nonneg hxpos.le epsilon]

theorem actual_smooth_m_bound {d : MediumAtom} (hM : 0 < d.V) {m : ℕ}
    (hm : m ∈ paperPsiNaturalCarrier d.V) : (m : ℝ) ≤ 5 * d.V / 2 :=
  (show (m : ℝ) ≤ (Nat.floor (5 * d.V / 2) : ℝ) by
    exact_mod_cast (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by positivity))

/-- This covers all n in the literal original alpha interval used in
the progression fibre, including points at which alpha itself vanishes. -/
theorem actual_single_zero_shift_polynomial_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (m n : ℕ)
    (hm : m ∈ paperPsiNaturalCarrier d.V)
    (hn : n ∈ Finset.Ico (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1)) :
    (otherShiftAbs m n d.residue.natAbs : ℝ) ≤
      8 * d.scale ^ (max 1 (1 + kappa)) := by
  have hM : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hN : 0 < d.U := zero_lt_one.trans_le hd.1
  have hx : 1 ≤ d.scale := by
    dsimp [MediumAtom.scale]
    nlinarith [hd.1, hd.2.1]
  have hmhi := actual_smooth_m_bound hM hm
  have hnhi : (n : ℝ) ≤ 2 * d.U := by
    have hnN : n ≤ Nat.floor (2 * d.U) := by have hh := (Finset.mem_Ico.mp hn).2; omega
    exact (show (n : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by exact_mod_cast hnN).trans
      (Nat.floor_le (by positivity))
  have hmn : (m : ℝ) * n ≤ 5 * d.scale := by
    have h := mul_le_mul hmhi hnhi (Nat.cast_nonneg _) (by positivity : 0 ≤ 5 * d.V / 2)
    dsimp [MediumAtom.scale]
    nlinarith
  have hxK : d.scale ≤ d.scale ^ (max 1 (1 + kappa)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (le_max_left 1 (1 + kappa))
  have haK : (d.residue.natAbs : ℝ) ≤ d.scale ^ (max 1 (1 + kappa)) :=
    hd.2.2.2.2.2.2.2.1.trans
      (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  calc
    _ = |(m : ℝ) * n - (d.residue.natAbs : ℝ)| := by
      rw [otherShiftAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Nat.cast_mul,
        Int.cast_natCast]
    _ ≤ |(m : ℝ) * n| + |(d.residue.natAbs : ℝ)| := abs_sub _ _
    _ ≤ 5 * d.scale + d.scale ^ (max 1 (1 + kappa)) := by
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      exact add_le_add hmn (by simpa only [abs_of_nonneg (Nat.cast_nonneg _)] using haK)
    _ ≤ _ := by nlinarith

end
end ImbalancedChen.Part3OriginalSingleZeroPolynomialTau
