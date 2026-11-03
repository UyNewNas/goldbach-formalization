import ImbalancedChen.P2HistoricalBankLogWeights
import ImbalancedChen.P2Selected430LiteralActionData
import ImbalancedChen.Part5OriginalUpsilon5FloorKernel

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Bind the 200 literal seed-only430 logarithmic coefficients to the original
rounded point -> rounded quotient -> atanh32 producer. The closed finite
proof below is deliberately UNEVALUATED in this delivery. It is not a
hypothesis, native oracle, or equality to an unrounded real logarithm.
-/
namespace ImbalancedChen.Part5OriginalH430LiteralLogBinding

noncomputable section
open P2Selected430LiteralActionData (logWeights q)
open P2TableActionSourceOnly
open Part5OriginalUpsilon5CausalDictionary

/-- This computes only 200 logarithmic coefficients if Lean checks it;
no seed-only table iteration or saved endpoint array is evaluated. -/
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem literal_logWeight_eq_producer (i : Fin 200) :
    logWeights i = P2HistoricalBankLogWeights.logWeight i.val := by
  fin_cases i <;> decide

theorem literal_logWeight_nonneg (i : Fin 200) : 0 ≤ logWeights i := by
  rw [literal_logWeight_eq_producer]
  exact P2HistoricalBankLogWeights.logWeight_nonnegative i.val

theorem literal_logWeight_le_log (i : Fin 200) :
    (logWeights i : ℝ)/(2:ℝ)^80 ≤
      Real.log (floorGrid (i.val+1)/floorGrid i.val) := by
  rw [literal_logWeight_eq_producer]
  simpa [tableQ, tableGrid, floorGrid] using
    P2HistoricalBankLogWeights.logWeight_le_log i.val

/-- Keep the actual integer product floor before the unique final Q80
normalization. Only the OLD numerator is required to be nonnegative. -/
theorem literal_product_le_log {v : ℤ} (hv : 0 ≤ v) (i : Fin 200) :
    (((v*logWeights i/q : ℤ) : ℝ)/(2:ℝ)^80) ≤
      ((v:ℝ)/(2:ℝ)^80) * Real.log (floorGrid (i.val+1)/floorGrid i.val) := by
  have hqZ : (tableQ : ℤ) = q := by norm_num [tableQ, q]
  have hqR : (tableQ : ℝ) = (2:ℝ)^80 := by norm_num [tableQ]
  have hr := roundedProduct_le tableQ tableQ_pos v (logWeights i)
  rw [roundedProduct_eq_ediv, hqZ, hqR] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left (literal_logWeight_le_log i)
    (div_nonneg (by exact_mod_cast hv) (by positivity)))

end
end ImbalancedChen.Part5OriginalH430LiteralLogBinding
