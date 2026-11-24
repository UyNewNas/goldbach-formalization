import ImbalancedChen.P2OriginalPhysicalSimplexMomentRow

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual radial panel is floored only ONCE. Its staircase pieces use
the unrounded classical Jensen value, so no extra eight floor losses
are silently introduced. The physical row/mass/mean APIs are reused.
-/
namespace ImbalancedChen.P2OriginalPhysicalSimplexJensenRow
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalPhysicalSimplexMomentRow
open P2OriginalLogMomentQ96CheckerSourceOnly (oldEvaluator)
open P2PositiveAffineSimplexLogJensenSourceOnly
open P2OriginalSaving16JensenFloor (weighted_log_le_log_mean)

def rowJensenQ (r : Row) : ℚ := oldEvaluator (rowMassQ r) (rowMeansQ r)

theorem row_unrounded_jensen_sound (r : Row) :
    (rowJensenQ r : ℝ) ≤ ∫ t in rowSupport r, rowDensity r t := by
  have hbound (j : Fin 10) :
      (∫ t, rowGap r t * Real.log (rowFactors r t j) ∂rowMeasure r) /
        mass (rowMeasure r) (rowGap r) ≤ Real.log (rowMeansQ r j : ℝ) := by
    exact weighted_log_le_log_mean (rowMeasure r) (rowGap r) (fun t => rowFactors r t j)
      (rowMeansQ r j : ℝ) (row_gap_integrable r) (row_factor_integrable r j)
      (row_log_integrable r j) (row_gap_nonneg_ae r)
      ((row_factors_pos_ae r).mono fun t ht => ht j) (row_mass_pos r)
      (by exact_mod_cast row_means_pos r j) (row_means_semantics r j).symm
  have h := weighted_log_gap_cubic_lower_four (rowMeasure r) (rowGap r)
    (fun j t => rowFactors r t j) (fun j => (rowMeansQ r j : ℝ)) (fun _ => (0 : ℝ))
    (continuous_rowGap r).measurable (row_gap_integrable r) (row_gap_nonneg_ae r)
    (row_mass_pos r) (row_factors_pos_ae r) (row_log_integrable r) (row_reciprocal_integrable r)
    (fun j => by exact_mod_cast row_means_pos r j) (fun _ => le_rfl)
    (fun j => by simpa only [sub_zero] using hbound j)
  have hs : (4 * mass (rowMeasure r) (rowGap r) / ∏ j, (rowMeansQ r j : ℝ)) ≤
      ∫ t in rowSupport r, rowDensity r t := by
    simpa [cubicCorrection,rowMeasure,rowDensity] using h
  unfold rowJensenQ oldEvaluator
  push_cast
  rw [row_mass_semantics]
  exact hs

end
end ImbalancedChen.P2OriginalPhysicalSimplexJensenRow
