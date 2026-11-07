import ImbalancedChen.P1ActualHistoricalThirdCellPartition

/-!
# Locality of a change to the actual historical third rough threshold

The cells, Gamma table, initial firstStop policy and actual carrier are fixed.
Increasing the activation threshold from omega to omega' only interchanges
selected rawLevel and initial fallback on omega <= t2 < omega'. The formula
keeps the sign of that interchange; no monotonicity of retained policies or
tuple counts is asserted. All results are finite, source-only candidates.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical List BigOperators
open Set

namespace HistoricalThirdCoarse.P1ActualThreshold
open P1ActualTuple P1ActualPartition P1ThirdFallbackSupport

def thresholdStrip (omega omega' : ℝ) : Set (Fin 3 → ℝ) :=
  {t | omega ≤ t 2 ∧ t 2 < omega'}

/-- The common parent keeps the original initial firstStop and all prime/cap
conditions. Neither rough activation threshold is used through rank two. -/
def parents (e : ℝ) (m : ℕ) (N cap : ℕ) : Finset (Fin 3 → ℕ) :=
  firstExitFrontierTuples 2 (initialPolicy e m (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))

theorem parent_frontier_eq_initial (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    firstExitFrontierTuples 2 (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) = parents e m N cap := by
  ext p
  simp only [parents, mem_firstExitFrontierTuples_iff]
  have hdrop : (List.ofFn p).dropLast = [p 0, p 1] := by simp [List.ofFn_succ]
  simp [hdrop, FirstExitValidSelection, policy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy]

theorem full_eq_parent_filter (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    full e chi m omega N cap = (parents e m N cap).filter
      (fun p => policy e chi m omega (N : ℝ) false (history p) = true) := by
  unfold full retainedTuples
  rw [parent_frontier_eq_initial]

theorem mem_parents (e : ℝ) (m : ℕ) (N cap : ℕ) (p : Fin 3 → ℕ) :
    p ∈ parents e m N cap ↔
      StrictAnti p ∧
        (∀ i, p i < cap ∧ Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          0 ≤ (p i : ℝ) ∧ (p i : ℝ) < (N : ℝ) ^ (19 / 96 : ℝ)) ∧
        (p 0 : ℝ) ^ 3 < (N : ℝ) ^ initial e ∧ firstStop e m (N : ℝ) [p 0] := by
  rw [← parent_frontier_eq_initial e 0 m 0 N cap,
    mem_actualPrimeFrontierTuples_iff]
  apply and_congr_right
  intro hsort
  apply and_congr_right
  intro hprime
  exact parent_two_iff e 0 m 0 (N : ℝ) p (hprime 0).2.1.pos

private theorem parents_positive (e : ℝ) (m : ℕ) (N cap : ℕ)
    {p : Fin 3 → ℕ} (hp : p ∈ parents e m N cap) : ∀ i, 0 < p i := by
  have hh := (mem_actualPrimeFrontierTuples_iff 2 (initialPolicy e m (N : ℝ))
    N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) p).mp hp
  exact fun i => (hh.2.1 i).2.1.pos

/-- Exact actual third test, before simplifying the provider's strict cubes. -/
theorem third_policy_eq_raw (e chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ)
    (p : Fin 3 → ℕ) :
    policy e chi m omega (N : ℝ) false (history p) =
      decide (ordinaryRosserPrefixAdmissible false
        (rawLevel e chi m omega (N : ℝ) (history p)) (history p)) := by
  simp [policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy, rosserAncestor, history]

theorem rawLevel_eq_off_strip (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i)
    (hs : actualPrimeTupleLog N p ∉ thresholdStrip omega omega') :
    rawLevel e chi m omega (N : ℝ) (history p) =
      rawLevel e chi m omega' (N : ℝ) (history p) := by
  by_cases hl : omega ≤ actualPrimeTupleLog N p 2
  · have hh : omega' ≤ actualPrimeTupleLog N p 2 :=
      le_of_not_gt (fun h => hs ⟨hl, h⟩)
    have hal := (active_iff_log hN omega p hpos).mpr hl
    have hah := (active_iff_log hN omega' p hpos).mpr hh
    simp only [rawLevel, if_pos hal, if_pos hah]
  · have hh : ¬omega' ≤ actualPrimeTupleLog N p 2 := fun h => hl (horder.trans h)
    have hal : ¬active omega (N : ℝ) (history p) :=
      fun h => hl ((active_iff_log hN omega p hpos).mp h)
    have hah : ¬active omega' (N : ℝ) (history p) :=
      fun h => hh ((active_iff_log hN omega' p hpos).mp h)
    simp only [rawLevel, if_neg hal, if_neg hah]

theorem rawLevel_eq_outside_cells (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N : ℕ) (p : Fin 3 → ℕ)
    (ho : actualPrimeTupleLog N p ∉ jointCells e chi m) :
    rawLevel e chi m omega (N : ℝ) (history p) =
      rawLevel e chi m omega' (N : ℝ) (history p) := by
  have hs (w : ℝ) : ¬supported e chi m w (N : ℝ) (history p) := by
    rintro ⟨_, hu⟩
    rw [history_log] at hu
    exact ho hu
  rw [rawLevel_fallback e chi m omega (N : ℝ) (history p) (hs omega),
    rawLevel_fallback e chi m omega' (N : ℝ) (history p) (hs omega')]

/-- On the strip, the lower threshold activates the common selector and the
higher threshold uses the initial fallback. The difference has its literal sign. -/
theorem rawLevel_sub_on_strip (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N : ℕ) (hN : 1 < N) (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i)
    (hs : actualPrimeTupleLog N p ∈ thresholdStrip omega omega') :
    rawLevel e chi m omega (N : ℝ) (history p) -
        rawLevel e chi m omega' (N : ℝ) (history p) =
      (N : ℝ) ^ exponent e chi m (actualPrimeTupleLog N p) - (N : ℝ) ^ initial e := by
  have hal := (active_iff_log hN omega p hpos).mpr hs.1
  have hah : ¬active omega' (N : ℝ) (history p) :=
    fun h => (not_le_of_gt hs.2) ((active_iff_log hN omega' p hpos).mp h)
  simp only [rawLevel, if_pos hal, if_neg hah, history_log]

theorem rawLevel_sub_on_selected_cell (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N : ℕ) (hN : 1 < N) (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i)
    (hs : actualPrimeTupleLog N p ∈ thresholdStrip omega omega')
    (j : Cell m) (hj : j ∈ cells e chi m)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    rawLevel e chi m omega (N : ℝ) (history p) -
        rawLevel e chi m omega' (N : ℝ) (history p) =
      (N : ℝ) ^ levelExponent e (box m j) - (N : ℝ) ^ initial e := by
  rw [rawLevel_sub_on_strip e chi m omega omega' N hN p hpos hs,
    exponent_on_cell e chi m (actualPrimeTupleLog N p) j hj ht]

theorem third_policy_eq_off_strip (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i)
    (hs : actualPrimeTupleLog N p ∉ thresholdStrip omega omega') :
    policy e chi m omega (N : ℝ) false (history p) =
      policy e chi m omega' (N : ℝ) false (history p) := by
  rw [third_policy_eq_raw, third_policy_eq_raw,
    rawLevel_eq_off_strip e chi m omega omega' horder N hN p hpos hs]

theorem rawLevel_sub_zero_off_strip (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i)
    (hs : actualPrimeTupleLog N p ∉ thresholdStrip omega omega') :
    rawLevel e chi m omega (N : ℝ) (history p) -
      rawLevel e chi m omega' (N : ℝ) (history p) = 0 := by
  rw [rawLevel_eq_off_strip e chi m omega omega' horder N hN p hpos hs, sub_self]

theorem full_mem_iff_off_strip (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i)
    (hs : actualPrimeTupleLog N p ∉ thresholdStrip omega omega') :
    p ∈ full e chi m omega N cap ↔ p ∈ full e chi m omega' N cap := by
  rw [full_eq_parent_filter, full_eq_parent_filter]
  simp only [Finset.mem_filter,
    third_policy_eq_off_strip e chi m omega omega' horder N hN p hpos hs]

def admissionDifference (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N : ℕ) (p : Fin 3 → ℕ) : ℝ :=
  (if policy e chi m omega (N : ℝ) false (history p) = true then 1 else 0) -
    (if policy e chi m omega' (N : ℝ) false (history p) = true then 1 else 0)

theorem admissionDifference_zero_off_strip (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i)
    (hs : actualPrimeTupleLog N p ∉ thresholdStrip omega omega') :
    admissionDifference e chi m omega omega' N p = 0 := by
  rw [admissionDifference,
    third_policy_eq_off_strip e chi m omega omega' horder N hN p hpos hs, sub_self]

theorem admissionDifference_zero_outside_cells (e chi : ℝ) (m : ℕ)
    (omega omega' : ℝ) (N : ℕ) (p : Fin 3 → ℕ)
    (ho : actualPrimeTupleLog N p ∉ jointCells e chi m) :
    admissionDifference e chi m omega omega' N p = 0 := by
  have hpolicy : policy e chi m omega (N : ℝ) false (history p) =
      policy e chi m omega' (N : ℝ) false (history p) := by
    rw [third_policy_eq_raw, third_policy_eq_raw,
      rawLevel_eq_outside_cells e chi m omega omega' N p ho]
  rw [admissionDifference, hpolicy, sub_self]

theorem admissionDifference_ne_zero_support (e chi : ℝ) (m : ℕ)
    (omega omega' : ℝ) (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i)
    (hne : admissionDifference e chi m omega omega' N p ≠ 0) :
    actualPrimeTupleLog N p ∈ thresholdStrip omega omega' ∩ jointCells e chi m := by
  constructor
  · by_contra hs
    exact hne (admissionDifference_zero_off_strip e chi m omega omega' horder N hN p hpos hs)
  · by_contra ho
    exact hne (admissionDifference_zero_outside_cells e chi m omega omega' N p ho)

private theorem two_cube_tests_iff_log {N : ℕ} (hN : 1 < N) (level : ℝ)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ level ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ level) ↔
      3 * actualPrimeTupleLog N p 0 < level ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < level := by
  have h := cube_tests_iff_log hN level level p hpos
  tauto

/-- The strip's actual third admission difference retains both strict cubes
at each level. This expression is deliberately a signed difference. -/
theorem admissionDifference_on_selected_cell
    (e chi : ℝ) (m : ℕ) (omega omega' : ℝ) (N : ℕ) (hN : 1 < N)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i) (hsort : StrictAnti p)
    (hs : actualPrimeTupleLog N p ∈ thresholdStrip omega omega')
    (j : Cell m) (hj : j ∈ cells e chi m)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    admissionDifference e chi m omega omega' N p =
      (if 3 * actualPrimeTupleLog N p 0 < levelExponent e (box m j) ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < levelExponent e (box m j) then 1 else 0) -
      (if 3 * actualPrimeTupleLog N p 0 < initial e ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < initial e then 1 else 0) := by
  have hal := (active_iff_log hN omega p hpos).mpr hs.1
  have hah : ¬active omega' (N : ℝ) (history p) :=
    fun h => (not_le_of_gt hs.2) ((active_iff_log hN omega' p hpos).mp h)
  have ht' : primeHistoryLogCoordinates (N : ℝ) 3 (history p) ∈
      logPrimeMeshCell 0 (19 / 96) m j := by rw [history_log]; exact ht
  have hl := rawLevel_on_cell e chi m omega (N : ℝ) (history p) hal j hj ht'
  have hh := rawLevel_inactive e chi m omega' (N : ℝ) (history p) hah
  have htest (w : ℝ) := policy_third_iff e chi m w (N : ℝ)
    (p 0) (p 1) (p 2) (hpos 2)
    (hsort (by decide : (1 : Fin 3) < 2))
    (hsort (by decide : (0 : Fin 3) < 1))
  unfold admissionDifference
  rw [htest omega, htest omega', hl, hh,
    two_cube_tests_iff_log hN _ p hpos, two_cube_tests_iff_log hN _ p hpos]

/-- Both actual full tuple counts are evaluated on their common firstStop parent. -/
theorem full_sum_sub_eq_parent_admission_sum
    (e chi : ℝ) (m : ℕ) (omega omega' : ℝ) (N cap : ℕ)
    (F : (Fin 3 → ℕ) → ℝ) :
    (∑ p ∈ full e chi m omega N cap, F p) -
      (∑ p ∈ full e chi m omega' N cap, F p) =
      ∑ p ∈ parents e m N cap, admissionDifference e chi m omega omega' N p * F p := by
  rw [full_eq_parent_filter, full_eq_parent_filter,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hl : policy e chi m omega (N : ℝ) false (history p) = true <;>
    by_cases hh : policy e chi m omega' (N : ℝ) false (history p) = true <;>
    simp [admissionDifference, hl, hh]

/-- Actual signed tuple-count difference is supported on the rough strip;
the selected joint union is also retained, and may further reduce that support. -/
theorem full_sum_sub_eq_selected_strip
    (e chi : ℝ) (m : ℕ) (omega omega' : ℝ) (horder : omega ≤ omega')
    (N cap : ℕ) (hN : 1 < N) (F : (Fin 3 → ℕ) → ℝ) :
    (∑ p ∈ full e chi m omega N cap, F p) -
      (∑ p ∈ full e chi m omega' N cap, F p) =
      ∑ p ∈ (parents e m N cap).filter (fun p =>
        actualPrimeTupleLog N p ∈ thresholdStrip omega omega' ∧
          actualPrimeTupleLog N p ∈ jointCells e chi m),
        admissionDifference e chi m omega omega' N p * F p := by
  rw [full_sum_sub_eq_parent_admission_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hs : actualPrimeTupleLog N p ∈ thresholdStrip omega omega' ∧
      actualPrimeTupleLog N p ∈ jointCells e chi m
  · rw [if_pos hs]
  · rw [if_neg hs]
    by_cases ht : actualPrimeTupleLog N p ∈ thresholdStrip omega omega'
    · have ho : actualPrimeTupleLog N p ∉ jointCells e chi m := fun h => hs ⟨ht, h⟩
      rw [admissionDifference_zero_outside_cells e chi m omega omega' N p ho, zero_mul]
    · rw [admissionDifference_zero_off_strip e chi m omega omega' horder N hN p
        (parents_positive e m N cap hp) ht, zero_mul]

/-- The same localization for the literal reciprocal-prime mass and an arbitrary
signed test function, with no nonnegative-difference premise. -/
theorem full_weighted_sum_sub_eq_selected_strip
    (e chi : ℝ) (m : ℕ) (omega omega' : ℝ) (horder : omega ≤ omega')
    (N cap : ℕ) (hN : 1 < N) (F : (Fin 3 → ℕ) → ℝ) :
    (∑ p ∈ full e chi m omega N cap, tupleWeight p * F p) -
      (∑ p ∈ full e chi m omega' N cap, tupleWeight p * F p) =
      ∑ p ∈ (parents e m N cap).filter (fun p =>
        actualPrimeTupleLog N p ∈ thresholdStrip omega omega' ∧
          actualPrimeTupleLog N p ∈ jointCells e chi m),
        admissionDifference e chi m omega omega' N p * (tupleWeight p * F p) := by
  exact full_sum_sub_eq_selected_strip e chi m omega omega' horder N cap hN
    (fun p => tupleWeight p * F p)

end HistoricalThirdCoarse.P1ActualThreshold
end
end ImbalancedChen
