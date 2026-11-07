import ImbalancedChen.P1HistoricalLevelCheckPreservation

/-!
# An independent finite upper check for historical cap tables

The check traverses only the three actual selected finsets, together with
the original fallback. It does not change `HistoricalPrefixCapData.levelCheck`.
The latter checks inherited lower comparisons; this check controls upper
ceilings. Explicit counterexamples below show that neither implies the other.

The global lookup bounds include all nested outside fallbacks. They bound
cap levels only. They do not bound complete physical moduli, extra selected
prime products, small weights, or any factorization/distribution licence.
The sibling first draft supplies the planned integration import above.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- A selected-cell upper bound also controls the exact lookup outside
the selected union. Ownership is the existing half-open mesh ownership. -/
theorem p1HistoricalPrefixLookup_le_of_bounds {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback theta : ℚ)
    (hfallback : fallback ≤ theta) (hcap : ∀ j ∈ J, cap j ≤ theta)
    (t : Fin d → ℝ) :
    historicalPrefixLookup a b m J cap fallback t ≤ theta := by
  by_cases hex : ∃ j ∈ J, t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [historicalPrefixLookup_on_cell a b hab m J cap fallback t j hj ht]
    exact hcap j hj
  · have hout : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j := by
      intro j hj ht
      exact hex ⟨j, hj, ht⟩
    rw [historicalPrefixLookup_outside a b m J cap fallback t hout]
    exact hfallback

namespace HistoricalPrefixCapData

/-- A finite rational upper check, independent of inherited monotonicity.
The explicit bounded deciders traverse selected cells rather than the
full finite function types. -/
def p1CapCeilingCheck (D : HistoricalPrefixCapData) (theta : ℚ) : Bool :=
  decide (D.old ≤ theta) &&
    (@decide _ (Finset.decidableDforallFinset (s := D.cells3)
      (p := fun j _ => D.cap3 j ≤ theta)) &&
    (@decide _ (Finset.decidableDforallFinset (s := D.cells4)
      (p := fun j _ => D.cap4 j ≤ theta)) &&
    @decide _ (Finset.decidableDforallFinset (s := D.cells5)
      (p := fun j _ => D.cap5 j ≤ theta))))

theorem p1CapCeilingCheck_iff (D : HistoricalPrefixCapData) (theta : ℚ) :
    D.p1CapCeilingCheck theta = true ↔
      D.old ≤ theta ∧ (∀ j ∈ D.cells3, D.cap3 j ≤ theta) ∧
        (∀ j ∈ D.cells4, D.cap4 j ≤ theta) ∧
        (∀ j ∈ D.cells5, D.cap5 j ≤ theta) := by
  simp only [p1CapCeilingCheck, Bool.and_eq_true, decide_eq_true_eq]

theorem p1CapCeilingCheck_sound (D : HistoricalPrefixCapData) (theta : ℚ)
    (hcheck : D.p1CapCeilingCheck theta = true) :
    D.old ≤ theta ∧ (∀ j ∈ D.cells3, D.cap3 j ≤ theta) ∧
      (∀ j ∈ D.cells4, D.cap4 j ≤ theta) ∧
      (∀ j ∈ D.cells5, D.cap5 j ≤ theta) := by
  exact (D.p1CapCeilingCheck_iff theta).mp hcheck

theorem p1CapCeilingCheck_of_bounds (D : HistoricalPrefixCapData) (theta : ℚ)
    (hold : D.old ≤ theta) (h3 : ∀ j ∈ D.cells3, D.cap3 j ≤ theta)
    (h4 : ∀ j ∈ D.cells4, D.cap4 j ≤ theta)
    (h5 : ∀ j ∈ D.cells5, D.cap5 j ≤ theta) :
    D.p1CapCeilingCheck theta = true := by
  exact (D.p1CapCeilingCheck_iff theta).mpr ⟨hold, h3, h4, h5⟩

theorem p1CapCeilingCheck_mono (D : HistoricalPrefixCapData) {theta theta' : ℚ}
    (hcheck : D.p1CapCeilingCheck theta = true) (hle : theta ≤ theta') :
    D.p1CapCeilingCheck theta' = true := by
  obtain ⟨hold, h3, h4, h5⟩ := D.p1CapCeilingCheck_sound theta hcheck
  apply D.p1CapCeilingCheck_of_bounds theta' (hold.trans hle)
  · exact fun j hj => (h3 j hj).trans hle
  · exact fun j hj => (h4 j hj).trans hle
  · exact fun j hj => (h5 j hj).trans hle

theorem p1Cell3_le_ceiling (D : HistoricalPrefixCapData) (theta : ℚ)
    (hcheck : D.p1CapCeilingCheck theta = true) (j : Fin 3 → Fin (D.m + 1)) :
    D.cell3 j ≤ theta := by
  obtain ⟨hold, h3, _h4, _h5⟩ := D.p1CapCeilingCheck_sound theta hcheck
  unfold cell3
  split_ifs with hj
  · exact h3 j hj
  · exact hold

theorem p1Old4_le_ceiling (D : HistoricalPrefixCapData) (theta : ℚ)
    (hcheck : D.p1CapCeilingCheck theta = true) (j : Fin 4 → Fin (D.m + 1)) :
    D.old4 j ≤ theta := by
  exact D.p1Cell3_le_ceiling theta hcheck (historicalPrefixProject (by omega : 3 ≤ 4) j)

theorem p1Cell4_le_ceiling (D : HistoricalPrefixCapData) (theta : ℚ)
    (hcheck : D.p1CapCeilingCheck theta = true) (j : Fin 4 → Fin (D.m + 1)) :
    D.cell4 j ≤ theta := by
  unfold cell4
  split_ifs with hj
  · exact (D.p1CapCeilingCheck_sound theta hcheck).2.2.1 j hj
  · exact D.p1Old4_le_ceiling theta hcheck j

theorem p1Old5_le_ceiling (D : HistoricalPrefixCapData) (theta : ℚ)
    (hcheck : D.p1CapCeilingCheck theta = true) (j : Fin 5 → Fin (D.m + 1)) :
    D.old5 j ≤ theta := by
  exact D.p1Cell4_le_ceiling theta hcheck (historicalPrefixProject (by omega : 4 ≤ 5) j)

theorem p1Cell5_le_ceiling (D : HistoricalPrefixCapData) (theta : ℚ)
    (hcheck : D.p1CapCeilingCheck theta = true) (j : Fin 5 → Fin (D.m + 1)) :
    D.cell5 j ≤ theta := by
  unfold cell5
  split_ifs with hj
  · exact (D.p1CapCeilingCheck_sound theta hcheck).2.2.2 j hj
  · exact D.p1Old5_le_ceiling theta hcheck j

theorem p1Exponent3_le_ceiling (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (theta : ℚ) (hcheck : D.p1CapCeilingCheck theta = true) (t : Fin 3 → ℝ) :
    D.exponent3 t ≤ theta := by
  obtain ⟨hold, h3, _h4, _h5⟩ := D.p1CapCeilingCheck_sound theta hcheck
  exact p1HistoricalPrefixLookup_le_of_bounds D.a D.b hab D.m D.cells3 D.cap3
    D.old theta hold h3 t

/-- The fourth fallback is the full third lookup at the projected point,
so this bound is global rather than restricted to selected fourth cells. -/
theorem p1Exponent4_le_ceiling (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (theta : ℚ) (hcheck : D.p1CapCeilingCheck theta = true) (t : Fin 4 → ℝ) :
    D.exponent4 t ≤ theta := by
  exact p1HistoricalPrefixLookup_le_of_bounds D.a D.b hab D.m D.cells4 D.cap4
    (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t)) theta
    (D.p1Exponent3_le_ceiling hab theta hcheck _)
    (D.p1CapCeilingCheck_sound theta hcheck).2.2.1 t

/-- The fifth fallback includes the actual fourth and third selections,
even at points outside all adopted cells or the ambient mesh. -/
theorem p1Exponent5_le_ceiling (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (theta : ℚ) (hcheck : D.p1CapCeilingCheck theta = true) (t : Fin 5 → ℝ) :
    D.exponent5 t ≤ theta := by
  exact p1HistoricalPrefixLookup_le_of_bounds D.a D.b hab D.m D.cells5 D.cap5
    (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) theta
    (D.p1Exponent4_le_ceiling hab theta hcheck _)
    (D.p1CapCeilingCheck_sound theta hcheck).2.2.2 t

theorem p1Level3_le_power_ceiling (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (theta : ℚ) (hcheck : D.p1CapCeilingCheck theta = true)
    (N : ℝ) (hN : 1 ≤ N) (history : List ℕ) :
    D.level3 N history ≤ N ^ (theta : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  exact_mod_cast D.p1Exponent3_le_ceiling hab theta hcheck
    (primeHistoryLogCoordinates N 3 history)

theorem p1Level4_le_power_ceiling (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (theta : ℚ) (hcheck : D.p1CapCeilingCheck theta = true)
    (N : ℝ) (hN : 1 ≤ N) (history : List ℕ) :
    D.level4 N history ≤ N ^ (theta : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  exact_mod_cast D.p1Exponent4_le_ceiling hab theta hcheck
    (primeHistoryLogCoordinates N 4 history)

theorem p1Level5_le_power_ceiling (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (theta : ℚ) (hcheck : D.p1CapCeilingCheck theta = true)
    (N : ℝ) (hN : 1 ≤ N) (history : List ℕ) :
    D.level5 N history ≤ N ^ (theta : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  exact_mod_cast D.p1Exponent5_le_ceiling hab theta hcheck
    (primeHistoryLogCoordinates N 5 history)

/-- Cell restriction preserves the upper check without assuming that
the separate inherited-comparison check succeeds. -/
theorem p1RestrictSelections_capCeilingCheck (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (theta : ℚ) (hcheck : D.p1CapCeilingCheck theta = true) :
    (D.p1RestrictSelections J3 J4 J5).p1CapCeilingCheck theta = true := by
  obtain ⟨hold, h3, h4, h5⟩ := D.p1CapCeilingCheck_sound theta hcheck
  apply (D.p1RestrictSelections J3 J4 J5).p1CapCeilingCheck_of_bounds theta hold
  · intro j hj
    exact h3 j (Finset.mem_inter.mp hj).1
  · intro j hj
    exact h4 j (Finset.mem_inter.mp hj).1
  · intro j hj
    exact h5 j (Finset.mem_inter.mp hj).1

theorem p1RestrictFifth_capCeilingCheck (D : HistoricalPrefixCapData)
    (J5 : Finset (Fin 5 → Fin (D.m + 1)))
    (theta : ℚ) (hcheck : D.p1CapCeilingCheck theta = true) :
    (D.p1RestrictFifth J5).p1CapCeilingCheck theta = true := by
  have h := D.p1RestrictSelections_capCeilingCheck D.cells3 D.cells4 J5 theta hcheck
  simpa only [p1RestrictSelections, p1RestrictFifth, Finset.inter_self] using h

/-- Simultaneous preservation keeps the two original checks separate. -/
theorem p1RestrictSelections_bothChecks (D : HistoricalPrefixCapData)
    (J3 : Finset (Fin 3 → Fin (D.m + 1)))
    (J4 : Finset (Fin 4 → Fin (D.m + 1)))
    (J5 : Finset (Fin 5 → Fin (D.m + 1))) (theta : ℚ)
    (hlevel : D.levelCheck = true) (hceil : D.p1CapCeilingCheck theta = true) :
    (D.p1RestrictSelections J3 J4 J5).levelCheck = true ∧
      (D.p1RestrictSelections J3 J4 J5).p1CapCeilingCheck theta = true := by
  exact ⟨D.p1RestrictSelections_levelCheck J3 J4 J5 hlevel,
    D.p1RestrictSelections_capCeilingCheck J3 J4 J5 theta hceil⟩

/-- With no selected cells the original level check places no upper
bound on the original fallback. This witness uses ceiling one. -/
def p1CeilingIndependenceHighFallback : HistoricalPrefixCapData where
  a := 0
  b := 1
  m := 0
  old := 2
  cells3 := ∅
  cap3 := fun _ => 0
  cells4 := ∅
  cap4 := fun _ => 0
  cells5 := ∅
  cap5 := fun _ => 0

/-- All stored values meet ceiling one, but the selected third cap
strictly decreases from the original fallback. -/
def p1CeilingIndependenceDecreasingThird : HistoricalPrefixCapData where
  a := 0
  b := 1
  m := 0
  old := 1
  cells3 := {fun _ => 0}
  cap3 := fun _ => 0
  cells4 := ∅
  cap4 := fun _ => 0
  cells5 := ∅
  cap5 := fun _ => 0

theorem p1LevelCheck_does_not_imply_ceiling :
    ∃ D : HistoricalPrefixCapData,
      D.levelCheck = true ∧ D.p1CapCeilingCheck 1 = false := by
  refine ⟨p1CeilingIndependenceHighFallback, ?_, ?_⟩
  · simp [levelCheck, p1CeilingIndependenceHighFallback]
  · norm_num [p1CapCeilingCheck, p1CeilingIndependenceHighFallback]

theorem p1CeilingCheck_does_not_imply_levelCheck :
    ∃ D : HistoricalPrefixCapData,
      D.p1CapCeilingCheck 1 = true ∧ D.levelCheck = false := by
  refine ⟨p1CeilingIndependenceDecreasingThird, ?_, ?_⟩
  · norm_num [p1CapCeilingCheck, p1CeilingIndependenceDecreasingThird]
  · norm_num [levelCheck, p1CeilingIndependenceDecreasingThird]

end HistoricalPrefixCapData

end

end ImbalancedChen
