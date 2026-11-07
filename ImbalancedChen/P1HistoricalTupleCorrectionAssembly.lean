import ImbalancedChen.P1HistoricalFixedCoefficientAssembly
import ImbalancedChen.ActualHistoricalFourthResidualDictionaryP1

/-!
Staging imports are recorded separately. This is a finite assembly of the
actual fourth admitted-tuple correction and the actual fifth candidate
correction on one T3 tree. No limiting coefficient is postulated.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
namespace HistoricalPrefixCapData

theorem p1FifthRoughDensity_normalized_eq_third_sub_tupleCorrections
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    physicalDensitySum
        (D.p1FifthRoughSupport N cap ((N : ℝ) ^ (D.b : ℝ)))
        (D.p1FifthRoughCoefficient N cap ((N : ℝ) ^ (D.b : ℝ))) *
        Real.log (N : ℝ) / singularSeries N =
      firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) *
          Real.log (N : ℝ) / singularSeries N -
        D.fourthPrimeCorrectionP1 N cap - D.fifthPrimeCorrection N cap := by
  rw [D.p1FifthRoughDensity_eq_third_sub_savings hab hcheck N cap hN]
  rw [sub_mul, sub_div, add_mul, add_div,
    D.actualHistoricalFourthSaving_eq_fourthPrimeCorrectionP1,
    D.actualHistoricalFifthSaving_eq_fifthPrimeCorrection]
  ring

/-- Both distinct finite tuple carriers reduce to their owned cells.
The inherited old cap and every original signed term are unchanged. -/
theorem p1FifthRoughDensity_normalized_eq_third_sub_jointCells
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    physicalDensitySum
        (D.p1FifthRoughSupport N cap ((N : ℝ) ^ (D.b : ℝ)))
        (D.p1FifthRoughCoefficient N cap ((N : ℝ) ^ (D.b : ℝ))) *
        Real.log (N : ℝ) / singularSeries N =
      firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) *
          Real.log (N : ℝ) / singularSeries N -
        (∑ j ∈ D.cells4, D.fourthCellPrimeCorrectionP1 N cap j) -
        (∑ j ∈ D.cells5, D.fifthCellPrimeCorrection N cap j) := by
  rw [D.p1FifthRoughDensity_normalized_eq_third_sub_tupleCorrections
    hab hcheck N cap hN, D.fourthPrimeCorrection_eq_cellsP1 hab,
    D.fifthPrimeCorrection_eq_cells hab]

end HistoricalPrefixCapData
end
end ImbalancedChen
