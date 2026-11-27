import ImbalancedChen.HistoricalThirdFallbackSupportP1
import Mathlib.Topology.Order.Compact

/-!
Finite actual historical coarse levels and their correct global ceiling.

For e >= 0 each selected exponent is at most Lambda-2e < Theta-2e.
The GLOBAL ceiling is initial e = Theta-2e because inactive and unselected
histories keep Theta, not Lambda. Exponent monotonicity for the corresponding
level ceiling requires N >= 1; strict selected-level separation uses N > 1.
All finite-range statements are independent of these sign/base hypotheses.

No Gamma, rescue, pair gate or transition-strip definition is replaced.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical
open HistoricalThirdCoarse P1ThirdFallbackSupport VariableEnvelope

namespace P1ActualCoarseLevelCeiling

theorem selected_levelExponent_le_lambda (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (j : Cell m) (hj : j ∈ cells e chi m) :
    levelExponent e (box m j) ≤ VariableEnvelope.cap - 2 * e := by
  have hc := (mem_cells e chi m j).mp hj
  exact sub_le_sub_right (gamma_le_cap e (box m j) he hc.1 hc.2.1) (2 * e)

theorem selected_levelExponent_lt_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (j : Cell m) (hj : j ∈ cells e chi m) :
    levelExponent e (box m j) < initial e := by
  have hc := (mem_cells e chi m j).mp hj
  exact levelExponent_lt_initial e (box m j) he hc.1 hc.2.1

/-- Lookup values are actual stored cell exponents or the exact Theta fallback. -/
theorem exponent_eq_initial_or_cell (e chi : ℝ) (m : ℕ) (t : Fin 3 → ℝ) :
    exponent e chi m t = initial e ∨
      ∃ j ∈ cells e chi m, exponent e chi m t = levelExponent e (box m j) := by
  by_cases ht : ∃ j ∈ cells e chi m, t ∈ logPrimeMeshCell 0 (19 / 96) m j
  · obtain ⟨j, hj, hjt⟩ := ht
    exact Or.inr ⟨j, hj, exponent_on_cell e chi m t j hj hjt⟩
  · apply Or.inl
    apply exponent_outside
    intro j hj hjt
    exact ht ⟨j, hj, hjt⟩

theorem exponent_le_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (t : Fin 3 → ℝ) : exponent e chi m t ≤ initial e := by
  rcases exponent_eq_initial_or_cell e chi m t with h | ⟨j, hj, h⟩
  · exact h.le
  · rw [h]
    exact (selected_levelExponent_lt_initial e chi he m j hj).le

theorem exponent_on_selected_le_lambda (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (t : Fin 3 → ℝ)
    (ht : ∃ j ∈ cells e chi m, t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    exponent e chi m t ≤ VariableEnvelope.cap - 2 * e := by
  obtain ⟨j, hj, hjt⟩ := ht
  rw [exponent_on_cell e chi m t j hj hjt]
  exact selected_levelExponent_le_lambda e chi he m j hj

theorem rawLevel_eq_initial_or_cell (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    rawLevel e chi m omega N history = N ^ initial e ∨
      ∃ j ∈ cells e chi m,
        rawLevel e chi m omega N history = N ^ levelExponent e (box m j) := by
  by_cases hs : supported e chi m omega N history
  · obtain ⟨j, hj, ht⟩ := hs.2
    exact Or.inr ⟨j, hj, rawLevel_on_cell e chi m omega N history hs.1 j hj ht⟩
  · exact Or.inl (rawLevel_fallback e chi m omega N history hs)

theorem frozenLevel_eq_initial_or_cell (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    frozenLevel e chi m omega N history = N ^ initial e ∨
      ∃ j ∈ cells e chi m,
        frozenLevel e chi m omega N history = N ^ levelExponent e (box m j) := by
  exact rawLevel_eq_initial_or_cell e chi m omega N (rosserAncestor 3 history)

theorem rawLevel_le_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (hN : 1 ≤ N) (history : List ℕ) :
    rawLevel e chi m omega N history ≤ N ^ initial e := by
  unfold rawLevel
  split_ifs
  · exact Real.rpow_le_rpow_of_exponent_le hN (exponent_le_initial e chi he m _)
  · exact le_rfl

theorem frozenLevel_le_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (hN : 1 ≤ N) (history : List ℕ) :
    frozenLevel e chi m omega N history ≤ N ^ initial e := by
  exact rawLevel_le_initial e chi he m omega N hN (rosserAncestor 3 history)

/-- The sharper Lambda ceiling is asserted ONLY on active selected support. -/
theorem rawLevel_supported_le_lambda (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (hN : 1 ≤ N) (history : List ℕ)
    (hs : supported e chi m omega N history) :
    rawLevel e chi m omega N history ≤ N ^ (VariableEnvelope.cap - 2 * e) := by
  obtain ⟨j, hj, ht⟩ := hs.2
  rw [rawLevel_on_cell e chi m omega N history hs.1 j hj ht]
  exact Real.rpow_le_rpow_of_exponent_le hN
    (selected_levelExponent_le_lambda e chi he m j hj)

theorem rawLevel_supported_lt_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hs : supported e chi m omega N history) :
    rawLevel e chi m omega N history < N ^ initial e := by
  obtain ⟨j, hj, ht⟩ := hs.2
  rw [rawLevel_on_cell e chi m omega N history hs.1 j hj ht]
  exact Real.rpow_lt_rpow_of_exponent_lt hN
    (selected_levelExponent_lt_initial e chi he m j hj)

theorem frozenLevel_supported_lt_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hs : frozenSupported e chi m omega N history) :
    frozenLevel e chi m omega N history < N ^ initial e := by
  exact rawLevel_supported_lt_initial e chi he m omega N hN (rosserAncestor 3 history) hs

theorem rawLevel_eq_initial_iff_not_supported (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (hN : 1 < N) (history : List ℕ) :
    rawLevel e chi m omega N history = N ^ initial e ↔
      ¬ supported e chi m omega N history := by
  constructor
  · intro h hs
    have hlt := rawLevel_supported_lt_initial e chi he m omega N hN history hs
    rw [h] at hlt
    exact (lt_irrefl _ hlt)
  · exact rawLevel_fallback e chi m omega N history

theorem rawLevel_nonneg (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (hN : 0 ≤ N) (history : List ℕ) : 0 ≤ rawLevel e chi m omega N history := by
  unfold rawLevel
  split_ifs <;> exact Real.rpow_nonneg hN _

theorem rawLevel_pos (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (hN : 0 < N) (history : List ℕ) : 0 < rawLevel e chi m omega N history := by
  unfold rawLevel
  split_ifs <;> exact Real.rpow_pos_of_pos hN _

theorem frozenLevel_nonneg (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (hN : 0 ≤ N) (history : List ℕ) : 0 ≤ frozenLevel e chi m omega N history := by
  exact rawLevel_nonneg e chi m omega N hN (rosserAncestor 3 history)

theorem frozenLevel_pos (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (hN : 0 < N) (history : List ℕ) : 0 < frozenLevel e chi m omega N history := by
  exact rawLevel_pos e chi m omega N hN (rosserAncestor 3 history)

/-- A literal source witness rules out replacing the global Theta ceiling by Lambda. -/
theorem lambda_ceiling_fails_at_empty (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (hN : 1 < N) :
    N ^ (VariableEnvelope.cap - 2 * e) < rawLevel e chi m omega N [] := by
  have hfall : rawLevel e chi m omega N [] = N ^ initial e := by
    apply rawLevel_inactive
    simp [active]
  rw [hfall]
  apply Real.rpow_lt_rpow_of_exponent_lt hN
  dsimp [VariableEnvelope.cap, initial, extendedDistributionCap]
  linarith

/-- A finite exponent table independent of target, rough cutoff and history. -/
def exponentValues (e chi : ℝ) (m : ℕ) : Finset ℝ :=
  insert (initial e) ((cells e chi m).image (fun j => levelExponent e (box m j)))

theorem exponent_mem_values (e chi : ℝ) (m : ℕ) (t : Fin 3 → ℝ) :
    exponent e chi m t ∈ exponentValues e chi m := by
  rcases exponent_eq_initial_or_cell e chi m t with h | ⟨j, hj, h⟩
  · simp [exponentValues, h]
  · rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

theorem exponentValues_isCompact (e chi : ℝ) (m : ℕ) :
    IsCompact (exponentValues e chi m : Set ℝ) := by
  exact (exponentValues e chi m).finite_toSet.isCompact

theorem exponentValues_subset_initial (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) :
    (exponentValues e chi m : Set ℝ) ⊆ Set.Iic (initial e) := by
  intro value hvalue
  have hv : value ∈ exponentValues e chi m := hvalue
  rcases Finset.mem_insert.mp hv with h | h
  · exact h.le
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    exact (selected_levelExponent_lt_initial e chi he m j hj).le

theorem exponent_range_finite (e chi : ℝ) (m : ℕ) :
    (Set.range (exponent e chi m)).Finite := by
  apply (exponentValues e chi m).finite_toSet.subset
  rintro _ ⟨t, rfl⟩
  exact exponent_mem_values e chi m t

theorem exponent_range_isCompact (e chi : ℝ) (m : ℕ) :
    IsCompact (Set.range (exponent e chi m)) := by
  exact (exponent_range_finite e chi m).isCompact

/-- A bounded exponent window exists BEFORE choosing N or omega. -/
theorem exists_uniform_exponent_lower_bound (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) :
    ∃ L : ℝ, ∀ t : Fin 3 → ℝ, L ≤ exponent e chi m t ∧ exponent e chi m t ≤ initial e := by
  obtain ⟨L, hL⟩ := (exponentValues_isCompact e chi m).bddBelow
  exact ⟨L, fun t => ⟨hL (exponent_mem_values e chi m t), exponent_le_initial e chi he m t⟩⟩

theorem rawLevel_eq_rpow_mem_exponentValues (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    ∃ a ∈ exponentValues e chi m, rawLevel e chi m omega N history = N ^ a := by
  rcases rawLevel_eq_initial_or_cell e chi m omega N history with h | ⟨j, hj, h⟩
  · exact ⟨initial e, by simp [exponentValues], h⟩
  · exact ⟨levelExponent e (box m j),
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩), h⟩

theorem frozenLevel_eq_rpow_mem_exponentValues (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    ∃ a ∈ exponentValues e chi m, frozenLevel e chi m omega N history = N ^ a := by
  exact rawLevel_eq_rpow_mem_exponentValues e chi m omega N (rosserAncestor 3 history)

/-- Actual raw/frozen exponents stay in one window before either target parameter.
No assertion about monotonicity in the base is needed for this representation. -/
theorem exists_uniform_actual_exponent_window (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) :
    ∃ L : ℝ, ∀ omega N : ℝ, ∀ history : List ℕ,
      ∃ a b : ℝ, a ∈ Set.Icc L (initial e) ∧ b ∈ Set.Icc L (initial e) ∧
        rawLevel e chi m omega N history = N ^ a ∧
          frozenLevel e chi m omega N history = N ^ b := by
  obtain ⟨L, hL⟩ := (exponentValues_isCompact e chi m).bddBelow
  refine ⟨L, ?_⟩
  intro omega N history
  obtain ⟨a, ha, hra⟩ := rawLevel_eq_rpow_mem_exponentValues e chi m omega N history
  obtain ⟨b, hb, hrb⟩ := frozenLevel_eq_rpow_mem_exponentValues e chi m omega N history
  exact ⟨a, b, ⟨hL ha, exponentValues_subset_initial e chi he m ha⟩,
    ⟨hL hb, exponentValues_subset_initial e chi he m hb⟩, hra, hrb⟩

/-- The actual level table depends on N, but remains independent of omega/history. -/
def levelValues (e chi : ℝ) (m : ℕ) (N : ℝ) : Finset ℝ :=
  insert (N ^ initial e) ((cells e chi m).image (fun j => N ^ levelExponent e (box m j)))

theorem rawLevel_mem_values (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) :
    rawLevel e chi m omega N history ∈ levelValues e chi m N := by
  rcases rawLevel_eq_initial_or_cell e chi m omega N history with h | ⟨j, hj, h⟩
  · simp [levelValues, h]
  · rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

theorem frozenLevel_mem_values (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) :
    frozenLevel e chi m omega N history ∈ levelValues e chi m N := by
  exact rawLevel_mem_values e chi m omega N (rosserAncestor 3 history)

theorem levelValues_isCompact (e chi : ℝ) (m : ℕ) (N : ℝ) :
    IsCompact (levelValues e chi m N : Set ℝ) := by
  exact (levelValues e chi m N).finite_toSet.isCompact

theorem rawLevel_range_finite (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    (Set.range (rawLevel e chi m omega N)).Finite := by
  apply (levelValues e chi m N).finite_toSet.subset
  rintro _ ⟨history, rfl⟩
  exact rawLevel_mem_values e chi m omega N history

theorem frozenLevel_range_finite (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    (Set.range (frozenLevel e chi m omega N)).Finite := by
  apply (levelValues e chi m N).finite_toSet.subset
  rintro _ ⟨history, rfl⟩
  exact frozenLevel_mem_values e chi m omega N history

theorem rawLevel_range_isCompact (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    IsCompact (Set.range (rawLevel e chi m omega N)) := by
  exact (rawLevel_range_finite e chi m omega N).isCompact

theorem frozenLevel_range_isCompact (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    IsCompact (Set.range (frozenLevel e chi m omega N)) := by
  exact (frozenLevel_range_finite e chi m omega N).isCompact

/-- The entire finite table lies in a positive interval at every target N >= 1. -/
theorem levelValues_subset_positive_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    (levelValues e chi m N : Set ℝ) ⊆ Set.Ioc 0 (N ^ initial e) := by
  intro value hvalue
  have hv : value ∈ levelValues e chi m N := hvalue
  rcases Finset.mem_insert.mp hv with h | h
  · subst value
    exact ⟨Real.rpow_pos_of_pos (by linarith) _, le_rfl⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    exact ⟨Real.rpow_pos_of_pos (by linarith) _,
      Real.rpow_le_rpow_of_exponent_le hN
        (selected_levelExponent_lt_initial e chi he m j hj).le⟩

/-- One positive compact set works for ALL rough cutoffs and ALL histories. -/
theorem exists_compact_uniform_level_carrier (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Set.Ioc 0 (N ^ initial e) ∧
      ∀ omega : ℝ, ∀ history : List ℕ,
        rawLevel e chi m omega N history ∈ K ∧
          frozenLevel e chi m omega N history ∈ K := by
  exact ⟨(levelValues e chi m N : Set ℝ), levelValues_isCompact e chi m N,
    levelValues_subset_positive_initial e chi he m N hN,
    fun omega history => ⟨rawLevel_mem_values e chi m omega N history,
      frozenLevel_mem_values e chi m omega N history⟩⟩

end P1ActualCoarseLevelCeiling
end
end ImbalancedChen
