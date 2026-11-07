import ImbalancedChen.Part3OriginalS2ActualTailTransfer
import Mathlib.Tactic

/-! The original three medium inequalities imply manuscript (7), with
the exact native paperPsi cap ten retained. No new analytic primitive is
used. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalS2NativePhysicalRange

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2NativeKeyTail
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2ActualTailTransfer
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open Classical

noncomputable section

/-- The paper's u<(2-15sigma)/5 follows by discarding factors >=1,
including |a|^(7/32). Nonzero moving residue is explicit. -/
theorem Q2_lt_scale_two_fifths
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (ha : d.residue ≠ 0) : d.Q2 < d.scale ^ ((2 : ℝ) / 5) := by
  rcases hd with ⟨hN, hM, hQ1, hQ2, hQ3, hx, _, _, _, _, hA, _⟩
  have hx1 : 1 ≤ d.scale := by
    have he : 1 < Real.exp (Real.exp 1) := Real.one_lt_exp.mpr (Real.exp_pos 1)
    linarith
  have hx0 : 0 ≤ d.scale := by linarith
  have ha1 : (1 : ℝ) ≤ d.residue.natAbs := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ha)
  have hpowA : 1 ≤ (d.residue.natAbs : ℝ) ^ (7 / 32 : ℝ) :=
    Real.one_le_rpow ha1 (by norm_num)
  have hother : 1 ≤ (d.residue.natAbs : ℝ) ^ (7 / 32 : ℝ) *
      d.U * d.Q1 * d.Q3 ^ 2 := by
    have hQ3sq : 1 ≤ d.Q3 ^ 2 := by nlinarith
    have hp := mul_le_mul hpowA hN zero_le_one (by positivity)
    have hp' := mul_le_mul hp hQ1 zero_le_one (by positivity)
    simpa only [one_mul] using mul_le_mul hp' hQ3sq zero_le_one (by positivity)
  have hQ2pow : d.Q2 ^ 5 < d.scale ^ (2 : ℝ) := by
    calc
      _ ≤ ((d.residue.natAbs : ℝ) ^ (7 / 32 : ℝ) * d.U * d.Q1 * d.Q3 ^ 2) * d.Q2 ^ 5 := by
        nlinarith [mul_le_mul_of_nonneg_right hother (pow_nonneg (by linarith : 0 ≤ d.Q2) 5)]
      _ = (d.residue.natAbs : ℝ) ^ (7 / 32 : ℝ) * d.U * d.Q1 * d.Q2 ^ 5 * d.Q3 ^ 2 := by ring
      _ < d.scale ^ (2 - 15 * sigma) := hA
      _ ≤ d.scale ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hroot : (d.scale ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) = d.scale ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  by_contra h
  have hle : d.scale ^ ((2 : ℝ) / 5) ≤ d.Q2 := le_of_not_gt h
  have hp : (d.scale ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) ≤ d.Q2 ^ (5 : ℕ) := by
    gcongr
  rw [hroot] at hp
  exact (not_le_of_gt hQ2pow) hp

/-- A weak form of (7), already leaving the fixed 1/10 cap gap. It is
uniform over all nonzero residues and all nonnegative sigma. -/
theorem Q1Q2Q3_lt_scale_seven_tenths
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (ha : d.residue ≠ 0) : d.Q1 * d.Q2 * d.Q3 < d.scale ^ ((7 : ℝ) / 10) := by
  have hQ2 := Q2_lt_scale_two_fifths hd hsigma ha
  rcases hd with ⟨hN, hM, hQ1, hQ2one, hQ3, hx, _, _, hqn, hN2, _⟩
  have hx1 : 1 ≤ d.scale := by
    have he : 1 < Real.exp (Real.exp 1) := Real.one_lt_exp.mpr (Real.exp_pos 1)
    linarith
  have hx0 : 0 ≤ d.scale := by linarith
  have hneg : d.scale ^ (-sigma) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show -sigma ≤ (0 : ℝ) by linarith)
  have hqN : d.Q1 < d.U := hqn.trans_le (by nlinarith)
  have hN2' : d.U ^ 2 * d.Q2 * d.Q3 ^ 2 < d.scale :=
    hN2.trans_le (by simpa using Real.rpow_le_rpow_of_exponent_le hx1
      (show 1 - 8 * sigma ≤ (1 : ℝ) by linarith))
  have hP2 : (d.Q1 * d.Q2 * d.Q3) ^ 2 < d.scale * d.scale ^ ((2 : ℝ) / 5) := by
    have hq2 : d.Q1 ^ 2 < d.U ^ 2 := by nlinarith
    calc
      _ = d.Q1 ^ 2 * d.Q2 ^ 2 * d.Q3 ^ 2 := by ring
      _ < d.U ^ 2 * d.Q2 ^ 2 * d.Q3 ^ 2 := by
        nlinarith [mul_lt_mul_of_pos_right hq2 (show 0 < d.Q2 ^ 2 * d.Q3 ^ 2 by positivity)]
      _ = (d.U ^ 2 * d.Q2 * d.Q3 ^ 2) * d.Q2 := by ring
      _ < d.scale * d.Q2 := mul_lt_mul_of_pos_right hN2' (by linarith)
      _ < d.scale * d.scale ^ ((2 : ℝ) / 5) := mul_lt_mul_of_pos_left hQ2 (by linarith)
  have hroot : (d.scale ^ ((7 : ℝ) / 10)) ^ (2 : ℕ) =
      d.scale * d.scale ^ ((2 : ℝ) / 5) := by
    calc
      _ = d.scale ^ (((7 : ℝ) / 10) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
      _ = d.scale ^ ((1 : ℝ) + 2 / 5) := by norm_num
      _ = d.scale ^ (1 : ℝ) * d.scale ^ ((2 : ℝ) / 5) :=
        Real.rpow_add (by linarith : 0 < d.scale) _ _
      _ = _ := by rw [Real.rpow_one]
  by_contra h
  have hle : d.scale ^ ((7 : ℝ) / 10) ≤ d.Q1 * d.Q2 * d.Q3 := le_of_not_gt h
  have hp : (d.scale ^ ((7 : ℝ) / 10)) ^ (2 : ℕ) ≤ (d.Q1 * d.Q2 * d.Q3) ^ (2 : ℕ) := by
    gcongr
  rw [hroot] at hp
  exact (not_le_of_gt hP2) hp

theorem nativePhysicalCap_le_original_range
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    (ha : d.residue ≠ 0) (hx : (10 : ℝ) ^ (10 : ℕ) ≤ d.scale) :
    nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)) := by
  have hx0 : 0 ≤ d.scale := by linarith [show (0 : ℝ) ≤ 10 ^ (10 : ℕ) by positivity]
  have hxpos : 0 < d.scale := by linarith [show (0 : ℝ) < 10 ^ (10 : ℕ) by positivity]
  have hten : (10 : ℝ) ≤ d.scale ^ ((1 : ℝ) / 10) := by
    calc
      10 = ((10 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  apply Nat.floor_mono
  calc
    10 * d.Q1 * d.Q2 * d.Q3 ≤ 10 * d.scale ^ ((7 : ℝ) / 10) := by
      have h := Q1Q2Q3_lt_scale_seven_tenths hd hsigma ha
      nlinarith
    _ ≤ d.scale ^ ((1 : ℝ) / 10) * d.scale ^ ((7 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_right hten (Real.rpow_nonneg hx0 _)
    _ = _ := by rw [← Real.rpow_add hxpos]; norm_num

theorem residue_ne_zero_of_original_c0
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hc0 : 0 < c0) : d.residue ≠ 0 := by
  rcases hd with ⟨hN, hM, hQ1, hQ2, hQ3, hx, ha, _⟩
  have hxpos : 0 < d.scale := by
    dsimp [MediumAtom.scale]
    positivity
  have hapos : (0 : ℝ) < d.residue.natAbs := (mul_pos hc0 hxpos).trans_le ha
  intro hz
  simp [hz] at hapos

/-- The E actual mixed-tail payment now has its physical cap discharged
from the original medium inequalities; no cap premise remains. -/
theorem exists_actual_mixedTail_payment_original_range
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → X ≤ d.scale →
        ‖keyMixedTailSum d d.scale (roughZ d.scale) k‖ ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨C, X, hC, hX, hbound⟩ := exists_actual_keyMixedTail_arbitrary_log hShiu A hA
  refine ⟨C, max X ((10 : ℝ) ^ (10 : ℕ)), hC,
    hX.trans_le (le_max_left _ _), ?_⟩
  intro B sigma kappa c0 d k hd hsigma hc0 hx
  exact hbound B sigma kappa c0 d k hd ((le_max_left _ _).trans hx)
    (nativePhysicalCap_le_original_range hd hsigma (residue_ne_zero_of_original_c0 hd hc0)
      ((le_max_right _ _).trans hx))

end
end ImbalancedChen.Part3OriginalS2NativePhysicalRange
