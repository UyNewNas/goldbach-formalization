import ImbalancedChen.HistoricalFifthCutoffInvariance
set_option warningAsError true

/-! A strict integer enumeration bound for the genuine inherited fifth
saving. A bare floor can discard an integer prime below a nonintegral
real wall; floor plus one covers every such prime and both cutoffs. -/

namespace ImbalancedChen
noncomputable section
open Filter Topology
open scoped Classical BigOperators

def historicalIntegerCutoff (N : ℕ) (b : ℚ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (b : ℝ)) + 1

theorem historicalIntegerCutoff_covers (N : ℕ) (b : ℚ) :
    (N : ℝ) ^ (b : ℝ) ≤ (historicalIntegerCutoff N b : ℝ) := by
  unfold historicalIntegerCutoff
  exact le_of_lt (by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((N : ℝ) ^ (b : ℝ))))

theorem historicalIntegerCutoff_contains
    (N p : ℕ) (b : ℚ) (hp : (p : ℝ) < (N : ℝ) ^ (b : ℝ)) :
    p < historicalIntegerCutoff N b := by
  exact_mod_cast hp.trans_le (historicalIntegerCutoff_covers N b)

namespace HistoricalPrefixCapData

theorem actualHistoricalFifthSaving_integerCutoff_eq
    (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (N cap : ℕ) (hN : 1 < N) :
    actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
        N cap (historicalIntegerCutoff N D.b : ℝ) *
      Real.log (N : ℝ) / singularSeries N = D.fifthPrimeCorrection N cap := by
  exact D.actualHistoricalFifthSaving_eq_fifthPrimeCorrection_of_cutoff_ge
    hab N cap hN _ (historicalIntegerCutoff_covers N D.b)

theorem upperFourthToFifthSaving_integerCutoff_eq
    (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < N) :
    (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 (historicalIntegerCutoff N D.b : ℝ)) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 (historicalIntegerCutoff N D.b : ℝ))) *
      Real.log (N : ℝ) / singularSeries N = D.fifthPrimeCorrection N cap := by
  exact D.upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection_of_cutoff_ge
    hab hcheck N cap hN _ (historicalIntegerCutoff_covers N D.b)

theorem tendsto_actualHistoricalFifthSaving_integerCutoff
    (D : HistoricalPrefixCapData) (ha : 0 < D.a)
    (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
          N (historicalIntegerCutoff N D.b)
          (historicalIntegerCutoff N D.b : ℝ) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) := by
  exact D.tendsto_actualHistoricalFifthSaving_of_cutoff_ge ha hab hold hcheck
    (fun N => historicalIntegerCutoff N D.b)
    (fun N => (historicalIntegerCutoff N D.b : ℝ))
    (Eventually.of_forall (fun N => historicalIntegerCutoff_covers N D.b))
    (Eventually.of_forall (fun N => historicalIntegerCutoff_covers N D.b))

theorem tendsto_upperFourthToFifthSaving_integerCutoff
    (D : HistoricalPrefixCapData) (ha : 0 < D.a)
    (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (historicalIntegerCutoff N D.b) 0
            (historicalIntegerCutoff N D.b : ℝ)) -
        firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (historicalIntegerCutoff N D.b) 0
            (historicalIntegerCutoff N D.b : ℝ))) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral) := by
  exact D.tendsto_upperFourthToFifthSaving_of_cutoff_ge ha hab hold hcheck
    (fun N => historicalIntegerCutoff N D.b)
    (fun N => (historicalIntegerCutoff N D.b : ℝ))
    (Eventually.of_forall (fun N => historicalIntegerCutoff_covers N D.b))
    (Eventually.of_forall (fun N => historicalIntegerCutoff_covers N D.b))

end HistoricalPrefixCapData
end
end ImbalancedChen
