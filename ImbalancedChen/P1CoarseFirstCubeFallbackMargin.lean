import ImbalancedChen.HistoricalThirdFallbackSupportP1
import ImbalancedChen.P1OriginalFirstStopInheritance
import ImbalancedChen.PrimeHistoryLogCoordinates

/-!
The literal original firstStop pays the Theta fallback first cube, including
the ACTIVE but unselected joint-cell branch. A selected cell instead pays
the first cube using its actual Gamma lower bound. These two branches are
assembled for the actual raw/frozen historical coarse levels.

Frontier and next-candidate results obtain firstStop from the real selected
tree through P1OriginalFirstStopInheritance; no admissibility is a premise.
Candidate admission at its own old/new gate is not required.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical
open HistoricalThirdCoarse P1ThirdFallbackSupport VariableEnvelope

namespace P1CoarseFirstCubeFallbackMargin

/-- The rank in this total dictionary does not change its first entry. -/
theorem first_coordinate_ancestor_one (N : ℝ) (history : List ℕ)
    (hlen : 1 ≤ history.length) :
    primeHistoryLogCoordinates N 1 (rosserAncestor 1 history) 0 =
      primeHistoryLogCoordinates N 3 history 0 := by
  exact primeHistoryLogCoordinates_ancestor N
    (rfl : history.length = history.length) hlen (0 : Fin 1)

theorem firstStop_first_coordinate_bound (e : ℝ) (m : ℕ) (N : ℝ)
    (history : List ℕ) (hlen : 1 ≤ history.length)
    (hstop : firstStop e m N (rosserAncestor 1 history)) :
    primeHistoryLogCoordinates N 3 history 0 ≤ extendedFirstStop - 4 * e := by
  obtain ⟨_i, _hlo, hhi, hbound⟩ := hstop
  rw [first_coordinate_ancestor_one N history hlen] at hhi
  exact hhi.le.trans hbound

/-- An explicit positive reserve at the ORIGINAL Theta initial exponent. -/
theorem initial_first_exponent_reserve (e : ℝ) (m : ℕ) (N : ℝ)
    (history : List ℕ) (hlen : 1 ≤ history.length)
    (hstop : firstStop e m N (rosserAncestor 1 history)) :
    17 / 4000 + 10 * e ≤ initial e -
      3 * primeHistoryLogCoordinates N 3 history 0 := by
  exact buffered_distribution_margin
    (firstStop_first_coordinate_bound e m N history hlen hstop)

theorem initial_first_exponent_strict (e : ℝ) (he : 0 < e) (m : ℕ) (N : ℝ)
    (history : List ℕ) (hlen : 1 ≤ history.length)
    (hstop : firstStop e m N (rosserAncestor 1 history)) :
    3 * primeHistoryLogCoordinates N 3 history 0 < initial e := by
  have hm := initial_first_exponent_reserve e m N history hlen hstop
  linarith

/-- This exponent is extracted from the ACTUAL rawLevel fallback split. -/
def effectiveExponent (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) : ℝ :=
  if supported e chi m omega N history then
    exponent e chi m (primeHistoryLogCoordinates N 3 history)
  else initial e

theorem rawLevel_eq_rpow_effectiveExponent (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    rawLevel e chi m omega N history = N ^ effectiveExponent e chi m omega N history := by
  rw [rawLevel_eq_ite_supported]
  by_cases hs : supported e chi m omega N history <;> simp [effectiveExponent, hs]

/-- Literal selected-cell Gamma provides the other branch of the strict margin. -/
theorem selected_first_exponent_strict (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (N : ℝ) (history : List ℕ) (j : Cell m)
    (hj : j ∈ cells e chi m)
    (ht : primeHistoryLogCoordinates N 3 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    3 * primeHistoryLogCoordinates N 3 history 0 <
      exponent e chi m (primeHistoryLogCoordinates N 3 history) := by
  rw [exponent_on_cell e chi m _ j hj ht]
  have hc := (mem_cells e chi m j).mp hj
  exact first_cube_margin e chi (box m j) he hesmall hchi hc.2.2.2.2.2
    (inBox_of_cell ht) hc.2.2.2.2.1

/-- Both active-selected and original fallback branches pay the same first cube.
In particular, active points outside the selected joint union use Theta. -/
theorem effective_first_exponent_strict (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (omega N : ℝ) (history : List ℕ) (hlen : 1 ≤ history.length)
    (hstop : firstStop e m N (rosserAncestor 1 history)) :
    3 * primeHistoryLogCoordinates N 3 history 0 <
      effectiveExponent e chi m omega N history := by
  by_cases hs : supported e chi m omega N history
  · rw [effectiveExponent, if_pos hs]
    obtain ⟨j, hj, ht⟩ := hs.2
    exact selected_first_exponent_strict e chi he hesmall hchi m N history j hj ht
  · rw [effectiveExponent, if_neg hs]
    exact initial_first_exponent_strict e he m N history hlen hstop

/-- Only positivity of the first actual integer is needed for this inverse. -/
theorem rpow_first_coordinate (N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hp : 0 < primeHistoryTuple 1 history 0) :
    N ^ primeHistoryLogCoordinates N 3 history 0 =
      (primeHistoryTuple 1 history 0 : ℝ) := by
  have hpR : (0 : ℝ) < primeHistoryTuple 1 history 0 := by exact_mod_cast hp
  change N ^ (Real.log (primeHistoryTuple 1 history 0 : ℝ) / Real.log N) = _
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hN),
    mul_div_cancel₀ _ (Real.log_pos hN).ne', Real.exp_log hpR]

theorem rawLevel_first_prime_cube (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (omega N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hlen : 1 ≤ history.length) (hp : 0 < primeHistoryTuple 1 history 0)
    (hstop : firstStop e m N (rosserAncestor 1 history)) :
    (primeHistoryTuple 1 history 0 : ℝ) ^ 3 < rawLevel e chi m omega N history := by
  rw [rawLevel_eq_rpow_effectiveExponent]
  apply first_cube_lt_level_of_exponent (primeHistoryTuple 1 history 0) hN
  · exact (rpow_first_coordinate N hN history hp).ge
  · exact effective_first_exponent_strict e chi he hesmall hchi
      m omega N history hlen hstop

/-- Fallback needs no selected-cell small-mesh hypotheses. This covers active
histories outside the selected union, as well as inactive histories. -/
theorem fallback_first_prime_cube (e chi : ℝ) (he : 0 < e)
    (m : ℕ) (omega N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hlen : 1 ≤ history.length) (hp : 0 < primeHistoryTuple 1 history 0)
    (hstop : firstStop e m N (rosserAncestor 1 history))
    (hs : ¬ supported e chi m omega N history) :
    (primeHistoryTuple 1 history 0 : ℝ) ^ 3 < rawLevel e chi m omega N history := by
  rw [rawLevel_fallback e chi m omega N history hs]
  apply first_cube_lt_level_of_exponent (primeHistoryTuple 1 history 0) hN
  · exact (rpow_first_coordinate N hN history hp).ge
  · exact initial_first_exponent_strict e he m N history hlen hstop

theorem outside_first_prime_cube (e chi : ℝ) (he : 0 < e)
    (m : ℕ) (omega N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hlen : 1 ≤ history.length) (hp : 0 < primeHistoryTuple 1 history 0)
    (hstop : firstStop e m N (rosserAncestor 1 history))
    (hout : ∀ j ∈ cells e chi m,
      primeHistoryLogCoordinates N 3 history ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    (primeHistoryTuple 1 history 0 : ℝ) ^ 3 < rawLevel e chi m omega N history := by
  apply fallback_first_prime_cube e chi he m omega N hN history hlen hp hstop
  rintro ⟨_ha, j, hj, ht⟩
  exact hout j hj ht

theorem first_coordinate_ancestor_three (N : ℝ) (history : List ℕ)
    (hlen : 3 ≤ history.length) :
    primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) 0 =
      primeHistoryLogCoordinates N 3 history 0 := by
  exact primeHistoryLogCoordinates_ancestor N
    (rfl : history.length = history.length) hlen (0 : Fin 3)

theorem first_integer_ancestor_three (history : List ℕ) (hlen : 3 ≤ history.length) :
    primeHistoryTuple 1 (rosserAncestor 3 history) 0 = primeHistoryTuple 1 history 0 := by
  exact primeHistoryTuple_ancestor
    (rfl : history.length = history.length) hlen (0 : Fin 3)

/-- The third-ancestor exponent margin applies to the original first coordinate. -/
theorem frozen_first_exponent_strict (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (omega N : ℝ) (history : List ℕ) (hlen : 3 ≤ history.length)
    (hstop : firstStop e m N (rosserAncestor 1 history)) :
    3 * primeHistoryLogCoordinates N 3 history 0 <
      effectiveExponent e chi m omega N (rosserAncestor 3 history) := by
  have ha : 1 ≤ (rosserAncestor 3 history).length := by
    rw [rosserAncestor_length]
    omega
  have hs : firstStop e m N (rosserAncestor 1 (rosserAncestor 3 history)) := by
    rw [rosserAncestor_nested 1 3 (by omega)]
    exact hstop
  have hm := effective_first_exponent_strict e chi he hesmall hchi
    m omega N (rosserAncestor 3 history) ha hs
  rw [first_coordinate_ancestor_three N history hlen] at hm
  exact hm

/-- The same actual first prime pays the current frozen level at all later ranks. -/
theorem frozenLevel_first_prime_cube (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (omega N : ℝ) (hN : 1 < N) (history : List ℕ)
    (hlen : 3 ≤ history.length) (hp : 0 < primeHistoryTuple 1 history 0)
    (hstop : firstStop e m N (rosserAncestor 1 history)) :
    (primeHistoryTuple 1 history 0 : ℝ) ^ 3 < frozenLevel e chi m omega N history := by
  have ha : 1 ≤ (rosserAncestor 3 history).length := by
    rw [rosserAncestor_length]
    omega
  have hpA : 0 < primeHistoryTuple 1 (rosserAncestor 3 history) 0 := by
    rw [first_integer_ancestor_three history hlen]
    exact hp
  have hs : firstStop e m N (rosserAncestor 1 (rosserAncestor 3 history)) := by
    rw [rosserAncestor_nested 1 3 (by omega)]
    exact hstop
  have hc := rawLevel_first_prime_cube e chi he hesmall hchi m omega N hN
    (rosserAncestor 3 history) ha hpA hs
  rw [first_integer_ancestor_three history hlen] at hc
  exact hc

/-- The actual tree supplies BOTH exponent margins, even at even frontier rank. -/
theorem actual_frontier_first_exponent_margins (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (omega N : ℝ) (weight : ℕ → ℝ) (carrier : List ℕ)
    (k : ℕ) (hk : 3 ≤ k) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (policy e chi m omega N)
      weight [] true 1 carrier) :
    (17 / 4000 + 10 * e ≤ initial e -
      3 * primeHistoryLogCoordinates N 3 state.selectedPrefix 0) ∧
    (3 * primeHistoryLogCoordinates N 3 state.selectedPrefix 0 <
      effectiveExponent e chi m omega N (rosserAncestor 3 state.selectedPrefix)) := by
  have hlen := firstExitDepthFrontier_selected_length k (policy e chi m omega N)
    weight [] carrier true 1 (by simp) state hstate
  have hstop := (P1OriginalFirstStopInheritance.frontier_original_first_tests
    e chi m omega N weight carrier k (by omega) state hstate).1
  exact ⟨initial_first_exponent_reserve e m N state.selectedPrefix (by omega) hstop,
    frozen_first_exponent_strict e chi he hesmall hchi m omega N
      state.selectedPrefix (by omega) hstop⟩

/-- No firstStop/admissibility input: both cubes come from real T3 membership. -/
theorem actual_frontier_initial_and_frozen_first_cube (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ)
    (weight : ℕ → ℝ) (k : ℕ) (hk : 3 ≤ k) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (policy e chi m omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    firstStop e m (N : ℝ) (rosserAncestor 1 state.selectedPrefix) ∧
      (primeHistoryTuple 1 state.selectedPrefix 0 : ℝ) ^ 3 < (N : ℝ) ^ initial e ∧
      (primeHistoryTuple 1 state.selectedPrefix 0 : ℝ) ^ 3 <
        frozenLevel e chi m omega (N : ℝ) state.selectedPrefix := by
  have hkpos : 0 < k := by omega
  have hlen := firstExitDepthFrontier_selected_length k
    (policy e chi m omega (N : ℝ)) weight [] (roughPrimeUniverse N cap w z)
    true 1 (by simp) state hstate
  have htests := P1OriginalFirstStopInheritance.frontier_original_first_tests
    e chi m omega (N : ℝ) weight (roughPrimeUniverse N cap w z) k hkpos state hstate
  have hp := (mem_roughPrimeUniverse_prime
    (primeHistoryTuple_frontier_mem k (policy e chi m omega (N : ℝ)) weight
      N cap w z state hstate ⟨0, hkpos⟩)).pos
  change 0 < primeHistoryTuple 1 state.selectedPrefix 0 at hp
  exact ⟨htests.1, htests.2,
    frozenLevel_first_prime_cube e chi he hesmall hchi m omega (N : ℝ) hN
      state.selectedPrefix (by omega) hp htests.1⟩

/-- The strict current-level first cube also holds BEFORE the next own admission. -/
theorem actual_next_candidate_initial_and_frozen_first_cube (e chi : ℝ)
    (he : 0 < e) (hesmall : e < (3 / 256 : ℝ) / 100) (hchi : chi < e / 10)
    (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ)
    (k : ℕ) (hk : 3 ≤ k) (frontier candidate : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k (policy e chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining) :
    firstStop e m (N : ℝ) (rosserAncestor 1 candidate.selectedPrefix) ∧
      (primeHistoryTuple 1 candidate.selectedPrefix 0 : ℝ) ^ 3 < (N : ℝ) ^ initial e ∧
      (primeHistoryTuple 1 candidate.selectedPrefix 0 : ℝ) ^ 3 <
        frozenLevel e chi m omega (N : ℝ) candidate.selectedPrefix := by
  have htests := P1OriginalFirstStopInheritance.next_candidate_original_first_tests
    e chi m omega (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z) k (by omega) frontier hfrontier candidate hcandidate
  obtain ⟨hlen, _hsort, _hprod, _hcut, _hremaining, _hsign, _hmass, hprime⟩ :=
    actualPrimeNextSelection_geometry k (policy e chi m omega (N : ℝ))
      N cap z frontier hfrontier candidate hcandidate
  have hp := (primeHistoryTuple_prime hlen hprime ⟨0, by omega⟩).pos
  change 0 < primeHistoryTuple 1 candidate.selectedPrefix 0 at hp
  have hc : primeHistoryTuple 1 (rosserAncestor 1 candidate.selectedPrefix) 0 =
      primeHistoryTuple 1 candidate.selectedPrefix 0 := by
    exact primeHistoryTuple_ancestor hlen (by omega : 1 ≤ k + 1) (0 : Fin 1)
  have hinitial := htests.2
  rw [hc] at hinitial
  exact ⟨htests.1, hinitial,
    frozenLevel_first_prime_cube e chi he hesmall hchi m omega (N : ℝ) hN
      candidate.selectedPrefix (by omega) hp htests.1⟩

end P1CoarseFirstCubeFallbackMargin
end
end ImbalancedChen
