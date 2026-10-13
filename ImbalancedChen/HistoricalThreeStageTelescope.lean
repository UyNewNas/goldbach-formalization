import ImbalancedChen.ActualHistoricalFifthCellIntegral
set_option warningAsError true

/-! Exact rank-three/four/five historical correction on the same literal
prime tuple; inherited caps and independent own-cube tests are preserved. -/
namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
namespace HistoricalPrefixCapData

theorem exponent3_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 3 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent3 t) - f D.old =
      ∑ j ∈ D.cells3,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap3 j) - f D.old else 0 := by
  exact historicalPrefixLookup_apply_sub D.a D.b hab D.m D.cells3
    D.cap3 D.old t f

theorem exponent5_threeStage_apply_sub (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent5 t) - f D.old =
      (∑ j ∈ D.cells3,
        if historicalPrefixProject (by omega : 3 ≤ 5) t ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap3 j) - f D.old else 0) +
      (∑ j ∈ D.cells4,
        if historicalPrefixProject (by omega : 4 ≤ 5) t ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap4 j) - f (D.old4 j) else 0) +
      (∑ j ∈ D.cells5,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap5 j) - f (D.old5 j) else 0) := by
  let t3 : Fin 3 → ℝ := historicalPrefixProject (by omega : 3 ≤ 5) t
  let t4 : Fin 4 → ℝ := historicalPrefixProject (by omega : 4 ≤ 5) t
  have hcoord : historicalPrefixProject (by omega : 3 ≤ 4) t4 = t3 :=
    historicalPrefixProject_comp (by omega : 3 ≤ 4) (by omega : 4 ≤ 5) t
  have h3 := D.exponent3_apply_sub hab t3 f
  have h4 := D.exponent4_apply_sub hab t4 f
  rw [hcoord] at h4
  have h5 := D.exponent5_apply_sub hab t f
  change f (D.exponent5 t) - f D.old =
    (∑ j ∈ D.cells3,
      if t3 ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
        f (D.cap3 j) - f D.old else 0) +
    (∑ j ∈ D.cells4,
      if t4 ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
        f (D.cap4 j) - f (D.old4 j) else 0) +
    (∑ j ∈ D.cells5,
      if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
        f (D.cap5 j) - f (D.old5 j) else 0)
  calc
    f (D.exponent5 t) - f D.old =
        (f (D.exponent3 t3) - f D.old) +
        (f (D.exponent4 t4) - f (D.exponent3 t3)) +
        (f (D.exponent5 t) - f (D.exponent4 t4)) := by ring
    _ = _ := by rw [h3, h4, h5]

theorem actualPrimeTupleOwnCube_threeStage_apply_sub
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N cap : ℕ) (p : Fin 5 → ℕ) :
    actualPrimeTupleOwnCubeMinus N cap
        (D.exponent5 (actualPrimeTupleLog N p) : ℝ) p -
      actualPrimeTupleOwnCubeMinus N cap (D.old : ℝ) p =
      (∑ j ∈ D.cells3,
        if historicalPrefixProject (by omega : 3 ≤ 5)
            (actualPrimeTupleLog N p) ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          actualPrimeTupleOwnCubeMinus N cap (D.cap3 j : ℝ) p -
            actualPrimeTupleOwnCubeMinus N cap (D.old : ℝ) p else 0) +
      (∑ j ∈ D.cells4,
        if historicalPrefixProject (by omega : 4 ≤ 5)
            (actualPrimeTupleLog N p) ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          actualPrimeTupleOwnCubeMinus N cap (D.cap4 j : ℝ) p -
            actualPrimeTupleOwnCubeMinus N cap (D.old4 j : ℝ) p else 0) +
      (∑ j ∈ D.cells5,
        if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
            actualPrimeTupleOwnCubeMinus N cap (D.old5 j : ℝ) p else 0) := by
  exact D.exponent5_threeStage_apply_sub hab (actualPrimeTupleLog N p)
    (fun q : ℚ => actualPrimeTupleOwnCubeMinus N cap (q : ℝ) p)

end HistoricalPrefixCapData
end
end ImbalancedChen
