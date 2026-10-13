import ImbalancedChen.HistoricalThreeStageTelescope
set_option warningAsError true

/-!
# Finite weighted transport of the genuine three-stage historical correction

The existing pointwise 3/4/5 telescope is transported over a finite
family of actual five-prime tuples, without deleting rejected last
candidates, replacing inherited caps, or merging the two own-cube tests.
Weights may be signed; no positivity is assumed. This is a finite identity,
not a bound for the adopted global policy.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators

namespace HistoricalPrefixCapData

/-- Third ancestor cell, including an unselected-cell zero fallback. -/
def threeStageOwnCubeCell3 (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ)
    (j : Fin 3 → Fin (D.m + 1)) : ℝ :=
  if historicalPrefixProject (by omega : 3 ≤ 5) (actualPrimeTupleLog N p) ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
    actualPrimeTupleOwnCubeMinus N cap (D.cap3 j : ℝ) p -
      actualPrimeTupleOwnCubeMinus N cap (D.old : ℝ) p
  else 0

/-- Fourth correction subtracts the effective third-level ancestor old4. -/
def threeStageOwnCubeCell4 (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ)
    (j : Fin 4 → Fin (D.m + 1)) : ℝ :=
  if historicalPrefixProject (by omega : 4 ≤ 5) (actualPrimeTupleLog N p) ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
    actualPrimeTupleOwnCubeMinus N cap (D.cap4 j : ℝ) p -
      actualPrimeTupleOwnCubeMinus N cap (D.old4 j : ℝ) p
  else 0

/-- Fifth correction subtracts the literal fourth-level inherited old5. -/
def threeStageOwnCubeCell5 (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ)
    (j : Fin 5 → Fin (D.m + 1)) : ℝ :=
  if actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
    actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
      actualPrimeTupleOwnCubeMinus N cap (D.old5 j : ℝ) p
  else 0

private theorem weighted_finite_swap {ι : Type*}
    (S : Finset (Fin 5 → ℕ)) (J : Finset ι)
    (w : (Fin 5 → ℕ) → ℝ)
    (g : (Fin 5 → ℕ) → ι → ℝ) :
    (∑ p ∈ S, w p * (∑ j ∈ J, g p j)) =
      ∑ j ∈ J, ∑ p ∈ S, w p * g p j := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- Finite Fubini for the actual 3/4/5 own-cube telescope. The source
carrier and real weights remain arbitrary, so actual frontier tuples and
reciprocal-prime masses can be substituted without losing rejected tuples. -/
theorem threeStageOwnCube_weighted_finite_sum
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N cap : ℕ) (S : Finset (Fin 5 → ℕ))
    (w : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ S, w p *
      (actualPrimeTupleOwnCubeMinus N cap
        (D.exponent5 (actualPrimeTupleLog N p) : ℝ) p -
       actualPrimeTupleOwnCubeMinus N cap (D.old : ℝ) p)) =
      (∑ j ∈ D.cells3, ∑ p ∈ S, w p * D.threeStageOwnCubeCell3 N cap p j) +
      (∑ j ∈ D.cells4, ∑ p ∈ S, w p * D.threeStageOwnCubeCell4 N cap p j) +
      (∑ j ∈ D.cells5, ∑ p ∈ S, w p * D.threeStageOwnCubeCell5 N cap p j) := by
  have hpoint (p : Fin 5 → ℕ) :
      actualPrimeTupleOwnCubeMinus N cap
          (D.exponent5 (actualPrimeTupleLog N p) : ℝ) p -
        actualPrimeTupleOwnCubeMinus N cap (D.old : ℝ) p =
        (∑ j ∈ D.cells3, D.threeStageOwnCubeCell3 N cap p j) +
        (∑ j ∈ D.cells4, D.threeStageOwnCubeCell4 N cap p j) +
        (∑ j ∈ D.cells5, D.threeStageOwnCubeCell5 N cap p j) := by
    simpa only [threeStageOwnCubeCell3, threeStageOwnCubeCell4,
      threeStageOwnCubeCell5] using
        (D.actualPrimeTupleOwnCube_threeStage_apply_sub hab N cap p)
  calc
    (∑ p ∈ S, w p *
      (actualPrimeTupleOwnCubeMinus N cap
        (D.exponent5 (actualPrimeTupleLog N p) : ℝ) p -
       actualPrimeTupleOwnCubeMinus N cap (D.old : ℝ) p)) =
        ∑ p ∈ S, w p *
          ((∑ j ∈ D.cells3, D.threeStageOwnCubeCell3 N cap p j) +
           (∑ j ∈ D.cells4, D.threeStageOwnCubeCell4 N cap p j) +
           (∑ j ∈ D.cells5, D.threeStageOwnCubeCell5 N cap p j)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hpoint p]
    _ =
        (∑ p ∈ S, w p * (∑ j ∈ D.cells3, D.threeStageOwnCubeCell3 N cap p j)) +
        (∑ p ∈ S, w p * (∑ j ∈ D.cells4, D.threeStageOwnCubeCell4 N cap p j)) +
        (∑ p ∈ S, w p * (∑ j ∈ D.cells5, D.threeStageOwnCubeCell5 N cap p j)) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = _ := by
      rw [weighted_finite_swap S D.cells3 w (D.threeStageOwnCubeCell3 N cap),
          weighted_finite_swap S D.cells4 w (D.threeStageOwnCubeCell4 N cap),
          weighted_finite_swap S D.cells5 w (D.threeStageOwnCubeCell5 N cap)]

end HistoricalPrefixCapData
end
end ImbalancedChen
