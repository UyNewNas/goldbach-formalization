import ImbalancedChen.P2EnhancedSwitchedTrueNormalization
import ImbalancedChen.Part5OriginalH430W1PhysicalRoughDictionary
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal local conversion price dominates the physical-N base price.
The second statement keeps the actual ordered-triple rough integer mass,
including its unit and repeated-factor terms. No density, PP, or signed
discrepancy assertion is made. Here li means the literal logarithmicIntegral
in thetaConversion, not trueLogarithmicIntegral with an added constant.
-/

namespace ImbalancedChen.Part5OriginalH430W1PriceLower

noncomputable section

open Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open Part5OriginalH430W1PhysicalRoughDictionary (integerMass)
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418 (logarithmicIntegral)

/-- The original d-dependent price is at least its physical-N base price. -/
theorem thetaConversion_lower {N d : ℕ} (hN : 4 ≤ N) (hd : 0 < d) :
    4 * logarithmicIntegral N * wuSingularSeries N / (N : ℝ) ≤
      thetaConversion N d := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hliLower : (0 : ℝ) ≤ (N : ℝ) / (2 * Real.log N) :=
    div_nonneg (Nat.cast_nonneg N) (mul_nonneg (by norm_num) hlog.le)
  have hli : 0 ≤ logarithmicIntegral N := hliLower.trans (box_trueLi_lower hN)
  have hC0 : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N hN0).le
  have hC : wuSingularSeries N ≤ wuSingularSeries (d * N) :=
    wuSingularSeries_le_mul hN0 hd
  have hphi : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr hd
  have ht : (Nat.totient d : ℝ) ≤ d := by
    exact_mod_cast Nat.totient_le d
  have hratio : wuSingularSeries N ≤
      (d : ℝ) * wuSingularSeries (d * N) / (Nat.totient d : ℝ) := by
    apply (le_div_iff₀ hphi).mpr
    calc
      wuSingularSeries N * (Nat.totient d : ℝ) ≤
          wuSingularSeries N * (d : ℝ) := mul_le_mul_of_nonneg_left ht hC0
      _ ≤ wuSingularSeries (d * N) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg d)
      _ = (d : ℝ) * wuSingularSeries (d * N) := mul_comm _ _
  have hfactor : 0 ≤ 4 * logarithmicIntegral N / (N : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hli) hNr.le
  calc
    4 * logarithmicIntegral N * wuSingularSeries N / (N : ℝ) =
        (4 * logarithmicIntegral N / (N : ℝ)) * wuSingularSeries N := by ring
    _ ≤ (4 * logarithmicIntegral N / (N : ℝ)) *
        ((d : ℝ) * wuSingularSeries (d * N) / (Nat.totient d : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio hfactor
    _ = thetaConversion N d := by
      unfold thetaConversion
      rw [div_mul_div_comm]
      ring

/-- The comparison multiplied by the unchanged actual W1 integer mass. -/
theorem integerMass_price_lower {N d : ℕ} (hN : 4 ≤ N) (hd : 0 < d)
    (Q : ℝ) (i : Fin 7) (j : Fin 10) :
    (4 * logarithmicIntegral N * wuSingularSeries N / (N : ℝ)) *
        integerMass N Q d i j ≤
      thetaConversion N d * integerMass N Q d i j := by
  have hmass : 0 ≤ integerMass N Q d i j := by
    unfold integerMass
    exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (thetaConversion_lower hN hd) hmass

end
end ImbalancedChen.Part5OriginalH430W1PriceLower
