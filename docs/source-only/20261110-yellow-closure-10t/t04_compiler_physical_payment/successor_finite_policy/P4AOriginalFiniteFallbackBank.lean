import ImbalancedChen.P4AOrderedThirdBufferedFallbackBoxes

namespace ImbalancedChen.P4AOriginalFiniteFallbackBank
noncomputable section
open scoped Classical
open Set

/-- Common pre-rough mesh and the two tables of licensed rational levels. -/
structure Bank where
  mesh : ℕ
  second : (Fin 2 → Fin (mesh+1)) → Option ℚ
  third : (Fin 3 → Fin (mesh+1)) → Option ℚ

def read {k : ℕ} (m : ℕ) (rows : (Fin k → Fin (m+1)) → Option ℚ)
    (t : Fin k → ℝ) : Option ℚ :=
  if h : ∃ j, t ∈ logPrimeMeshCell 0 (19/96) m j then rows h.choose else none

theorem read_on_cell {k m : ℕ} {rows : (Fin k → Fin (m+1)) → Option ℚ}
    {t : Fin k → ℝ} {j : Fin k → Fin (m+1)} (ht : t ∈ logPrimeMeshCell 0 (19/96) m j) :
    read m rows t=rows j := by
  have h : ∃ i, t ∈ logPrimeMeshCell 0 (19/96) m i := ⟨j,ht⟩
  rw [read,dif_pos h,logPrimeMeshCell_unique (by norm_num) h.choose_spec ht]

theorem read_some_iff {k m : ℕ} {rows : (Fin k → Fin (m+1)) → Option ℚ}
    {t : Fin k → ℝ} {c : ℚ} : read m rows t=some c ↔
      ∃ j, t ∈ logPrimeMeshCell 0 (19/96) m j ∧ rows j=some c := by
  constructor
  · unfold read
    split_ifs with h
    · intro hc
      exact ⟨h.choose,h.choose_spec,hc⟩
    · simp
  · rintro ⟨j,hj,hc⟩
    exact (read_on_cell hj).trans hc

end
end ImbalancedChen.P4AOriginalFiniteFallbackBank
