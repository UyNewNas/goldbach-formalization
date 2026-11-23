import ImbalancedChen.P6OriginalLiteralMeshPrices
import ImbalancedChen.P2U8QuadratureTendsto
import ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral

namespace ImbalancedChen.P6OriginalEighthMeshPrice

noncomputable section
open MeasureTheory Set
open P6OriginalLiteralMeshPrices P6OriginalLiteralLogIntegralPrices

theorem actual_eighth_log_integral :
    currentChenUpsilon8HarmonicIntegral =
      ∫ t in (417/5000:ℝ)..(1/3:ℝ), Real.log (2-3*t)/(t*(1-t)) := by
  rw [P2NegativeDomainCover.eighthHarmonicIntegral_eq_nested,
    intervalIntegral.integral_of_le (by norm_num : (417/5000:ℝ) ≤ 1/3),
    ← integral_Ico_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0:ℝ) < 417/5000) ht.1
  rw [currentChenUpsilon9Harmonic_inner_integral ht0 (by linarith [ht.2]) (by norm_num : (0:ℝ)<1/3)
    (by linarith [ht.2]), show (1-t-1/3)/(1/3) = 2-3*t by ring]

theorem actual_eighth_integral :
    currentChenUpsilon8HarmonicIntegral ≤ 5999905266705567/10000000000000000 := by
  rw [actual_eighth_log_integral]
  simpa only [div_one] using eighth_literal_integral

theorem eighth_mesh_passes :
    P2U8UniformRationalCover.uniformUpper 1000000000000000000 ≤
      (4904703865205402441361491 / 1208925819614629174706176 : ℚ)/(67619/10000) := by
  have hm := (P2U8QuadratureTendsto.uniformUpper_error 1000000000000000000 (by decide)).2
  have hs : 5999905266705567/10000000000000000+
      P2U8QuadratureTendsto.errorNumerator/1000000000000000000 ≤
      (4904703865205402441361491/1208925819614629174706176 : ℚ)/(67619/10000) := by
    change _ + rate8 ≤ price8
    exact eighth_budget.le
  have hh : (P2U8UniformRationalCover.uniformUpper 1000000000000000000 : ℝ) ≤
      (5999905266705567/10000000000000000 : ℝ) +
      (P2U8QuadratureTendsto.errorNumerator : ℝ)/1000000000000000000 := by
    linarith only [hm, actual_eighth_integral]
  apply (Rat.cast_le (K:=ℝ)).mp
  have hsR := (Rat.cast_le (K:=ℝ)).mpr hs
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_add] at hsR ⊢
  exact hh.trans hsR

end
end ImbalancedChen.P6OriginalEighthMeshPrice
