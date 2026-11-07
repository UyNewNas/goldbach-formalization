import ImbalancedChen.ActualHistoricalThirdTupleDictionary

/-!
# Fifth candidates of the original first-stop coarse third policy

The carrier is literally `HistoricalThirdCoarse.policy`, including its
original first-label stop. Rank four is even, so proper-parent validity
retains precisely the first and third odd tests. The initial first cube
and the raw third level's first cube remain different conditions.

The original third mesh owner is the first-three-coordinate projection
of the same actual fifth owner. Rough activation is inclusive. The
selected, active outside and inactive branches are identified without
assuming a comparison between initial and third levels. No fifth own-cube
condition is imposed on enumeration of these next candidates.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators
open Set

namespace HistoricalThirdCoarse.P1OriginalCoarseFifth

def thirdHistory (p : Fin 5 → ℕ) : List ℕ := [p 2, p 1, p 0]

def thirdOwner {m : ℕ} (j : Fin 5 → Fin (m + 1)) : Cell m :=
  historicalPrefixProject (by omega : 3 ≤ 5) j

def thirdCoordinates (t : Fin 5 → ℝ) : Fin 3 → ℝ :=
  historicalPrefixProject (by omega : 3 ≤ 5) t

theorem thirdHistory_log (N : ℕ) (p : Fin 5 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 3 (thirdHistory p) =
      thirdCoordinates (actualPrimeTupleLog N p) := by
  funext i
  fin_cases i <;> simp [thirdHistory, thirdCoordinates, historicalPrefixProject,
    primeHistoryLogCoordinates, primeHistoryTuple, actualPrimeTupleLog]

theorem thirdHistory_active_iff_log {N : ℕ} (hN : 1 < N)
    (omega : ℝ) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i) :
    active omega (N : ℝ) (thirdHistory p) ↔ omega ≤ actualPrimeTupleLog N p 2 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  rw [thirdHistory, active_triple, ← actualPrimeTupleLog_rpow hN p hpos 2,
    Real.rpow_le_rpow_left_iff hNr]

/-- The fourth selection is even and always retained by the ORIGINAL
policy. The singleton still includes firstStop at the initial level. -/
theorem original_parent_valid_iff (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p : Fin 5 → ℕ) (hprime : ∀ i, Nat.Prime (p i)) (hsort : StrictAnti p) :
    FirstExitValidSelection (policy e chi m omega N) [] true (List.ofFn p).dropLast ↔
      firstStop e m N [p 0] ∧
        (p 0 : ℝ) ^ 3 < N ^ initial e ∧
        (p 0 : ℝ) ^ 3 < rawLevel e chi m omega N (thirdHistory p) ∧
        (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < rawLevel e chi m omega N (thirdHistory p) := by
  have hdrop : (List.ofFn p).dropLast = [p 0, p 1, p 2, p 3] := by
    simp [List.ofFn_succ]
  have hv : FirstExitValidSelection (policy e chi m omega N)
        [] true (List.ofFn p).dropLast ↔
      FirstExitValidSelection (policy e chi m omega N) [] true [p 0, p 1] ∧
        policy e chi m omega N false (thirdHistory p) = true := by
    rw [hdrop]
    simp [FirstExitValidSelection, policy_even, thirdHistory, and_assoc]
  let q : Fin 3 → ℕ := ![p 0, p 1, p 2]
  have hf : FirstExitValidSelection (policy e chi m omega N) [] true [p 0, p 1] ↔
      (p 0 : ℝ) ^ 3 < N ^ initial e ∧ firstStop e m N [p 0] := by
    simpa [q, List.ofFn_succ] using
      P1ActualTuple.parent_two_iff e chi m omega N q (hprime 0).pos
  rw [hv, hf]
  have ht := policy_third_iff e chi m omega N (p 0) (p 1) (p 2) (hprime 2).pos
    (hsort (by decide : (1 : Fin 5) < 2)) (hsort (by decide : (0 : Fin 5) < 1))
  change (policy e chi m omega N false (thirdHistory p) = true) ↔
    ((p 0 : ℝ) ^ 3 < rawLevel e chi m omega N (thirdHistory p) ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < rawLevel e chi m omega N (thirdHistory p)) at ht
  rw [ht]
  tauto

def firstLabelRegion (e : ℝ) (m : ℕ) : Set (Fin 5 → ℝ) :=
  {t | ∃ i : Fin (m + 1),
    logPrimeMeshPoint 0 (19 / 96) m i.val ≤ t 0 ∧
    t 0 < logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ∧
    logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤ VariableEnvelope.extendedFirstStop - 4 * e}

theorem firstStop_iff_log (e : ℝ) (m N : ℕ) (p : Fin 5 → ℕ) :
    firstStop e m (N : ℝ) [p 0] ↔ actualPrimeTupleLog N p ∈ firstLabelRegion e m := by
  simp [firstStop, firstLabelRegion, primeHistoryLogCoordinates,
    primeHistoryTuple, actualPrimeTupleLog]

def thirdCellExponent (e chi : ℝ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) : ℝ :=
  if thirdOwner j ∈ cells e chi m then levelExponent e (box m (thirdOwner j)) else initial e

def currentExponent (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) (t : Fin 5 → ℝ) : ℝ :=
  if omega ≤ t 2 then thirdCellExponent e chi m j else initial e

theorem thirdHistory_on_projected_cell (m N : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : Fin 5 → ℕ)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    primeHistoryLogCoordinates (N : ℝ) 3 (thirdHistory p) ∈
      logPrimeMeshCell 0 (19 / 96) m (thirdOwner j) := by
  rw [thirdHistory_log]
  exact mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht

/-- An unselected projected owner is outside ALL selected third cells,
including at internal half-open mesh boundaries. -/
theorem thirdHistory_outside_selected_cells (e chi : ℝ) (m N : ℕ)
    (j : Fin 5 → Fin (m + 1)) (hj : thirdOwner j ∉ cells e chi m)
    (p : Fin 5 → ℕ)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    ∀ q ∈ cells e chi m, primeHistoryLogCoordinates (N : ℝ) 3 (thirdHistory p) ∉
      logPrimeMeshCell 0 (19 / 96) m q := by
  intro q hq hmem
  have heq := logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
    hmem (thirdHistory_on_projected_cell m N j p ht)
  exact hj (heq ▸ hq)

/-- The actual raw level is computed on this same fifth owner, with an
inclusive rough activation and the original initial fallback. -/
theorem rawLevel_on_fifth_cell (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i)
    (j : Fin 5 → Fin (m + 1))
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    rawLevel e chi m omega (N : ℝ) (thirdHistory p) =
      (N : ℝ) ^ currentExponent e chi m omega j (actualPrimeTupleLog N p) := by
  have ha := thirdHistory_active_iff_log hN omega p hpos
  by_cases hr : omega ≤ actualPrimeTupleLog N p 2
  · by_cases hj : thirdOwner j ∈ cells e chi m
    · rw [rawLevel_on_cell e chi m omega (N : ℝ) (thirdHistory p) (ha.mpr hr)
        (thirdOwner j) hj (thirdHistory_on_projected_cell m N j p ht)]
      simp only [currentExponent, if_pos hr, thirdCellExponent, if_pos hj]
    · rw [rawLevel_outside e chi m omega (N : ℝ) (thirdHistory p)
        (thirdHistory_outside_selected_cells e chi m N j hj p ht)]
      simp only [currentExponent, if_pos hr, thirdCellExponent, if_neg hj]
  · rw [rawLevel_inactive e chi m omega (N : ℝ) (thirdHistory p) (fun h => hr (ha.mp h))]
    simp only [currentExponent, if_neg hr]

/-- Seven parent rows retain BOTH first cubes and the raw third cube.
The first-label stop is an additional original policy condition. -/
def jointRegion (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) : Set (Fin 5 → ℝ) :=
  {t | t ∈ firstLabelRegion e m ∧ t ∈ primeAffineGateRegion historicalUnorderedThirdGateForms
    (historicalUnorderedThirdGateBounds (initial e) (currentExponent e chi m omega j t))}

theorem mem_jointRegion (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) (t : Fin 5 → ℝ) :
    t ∈ jointRegion e chi m omega j ↔
      t ∈ firstLabelRegion e m ∧ StrictAnti t ∧ 3 * t 0 < initial e ∧
        3 * t 0 < currentExponent e chi m omega j t ∧
        t 0 + t 1 + 3 * t 2 < currentExponent e chi m omega j t := by
  simp only [jointRegion, Set.mem_setOf_eq, mem_historicalUnorderedThirdGateRegion]

def candidates (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) : Finset (Fin 5 → ℕ) :=
  firstExitFrontierTuples 4 (policy e chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))

/-- This is the original first-stop tree, not D.upperThirdPolicy. There
is NO fifth own-cube admission premise in this candidate dictionary. -/
theorem mem_candidates_iff_log_on_cell (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (j : Fin 5 → Fin (m + 1))
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    p ∈ candidates e chi m omega N cap ↔
      (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧ 0 ≤ (p i : ℝ) ∧
        (p i : ℝ) < (N : ℝ) ^ (19 / 96 : ℝ)) ∧
      actualPrimeTupleLog N p ∈ jointRegion e chi m omega j := by
  rw [candidates, mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 4 _ N cap 0 _ hcap]
  constructor
  · rintro ⟨hsort, hp, hv⟩
    have hpos : ∀ i, 0 < p i := fun i => (hp i).1.pos
    have hc := (original_parent_valid_iff e chi m omega (N : ℝ) p
      (fun i => (hp i).1) hsort).mp hv
    rw [rawLevel_on_fifth_cell e chi m omega N hN p hpos j ht] at hc
    have hlog := (historicalUnorderedThird_cube_tests_iff_log hN (initial e)
      (currentExponent e chi m omega j (actualPrimeTupleLog N p)) p hpos).mp hc.2
    exact ⟨hp, (mem_jointRegion e chi m omega j _).mpr
      ⟨(firstStop_iff_log e m N p).mp hc.1,
        (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hsort, hlog⟩⟩
  · rintro ⟨hp, hg⟩
    have hpos : ∀ i, 0 < p i := fun i => (hp i).1.pos
    have hh := (mem_jointRegion e chi m omega j _).mp hg
    have hsort := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp hh.2.1
    refine ⟨hsort, hp, (original_parent_valid_iff e chi m omega (N : ℝ) p
      (fun i => (hp i).1) hsort).mpr ⟨(firstStop_iff_log e m N p).mpr hh.1, ?_⟩⟩
    rw [rawLevel_on_fifth_cell e chi m omega N hN p hpos j ht]
    exact (historicalUnorderedThird_cube_tests_iff_log hN (initial e)
      (currentExponent e chi m omega j (actualPrimeTupleLog N p)) p hpos).mpr hh.2.2

def primeBox (N : ℕ) : Finset (Fin 5 → ℕ) :=
  actualPrimeBoxTuples N (fun _ => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))

/-- Exact original carrier/filter dictionary on a genuine fifth joint
mesh cell, retaining the strict cutoff and deletion of target divisors. -/
theorem candidates_cell_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (m + 1)) :
    (candidates e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈
        logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e chi m omega j) := by
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hf, ht⟩
    have hh := (mem_candidates_iff_log_on_cell e chi m omega N cap hN hcap p j ht).mp hf
    refine ⟨(mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
      ⟨fun i => ⟨(hh.1 i).1, (hh.1 i).2.1⟩,
        logPrimeMeshCell_subset_box (by norm_num) m j ht⟩, ht, hh.2⟩
  · rintro ⟨hp, ht, hg⟩
    have hi := mem_actualPrimeBoxTuples_iff.mp hp
    refine ⟨(mem_candidates_iff_log_on_cell e chi m omega N cap hN hcap p j ht).mpr
      ⟨fun i => ⟨(hi i).1, (hi i).2.1, Nat.cast_nonneg _, (hi i).2.2.2⟩, hg⟩, ht⟩

def activeRegion (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) : Set (Fin 5 → ℝ) :=
  firstLabelRegion e m ∩
    (primeAffineGateRegion historicalUnorderedThirdGateForms
      (historicalUnorderedThirdGateBounds (initial e) (thirdCellExponent e chi m j)) ∩
        {t | omega ≤ t 2})

def selectedRegion (e : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) : Set (Fin 5 → ℝ) :=
  firstLabelRegion e m ∩
    (primeAffineGateRegion historicalUnorderedThirdGateForms
      (historicalUnorderedThirdGateBounds (initial e) (levelExponent e (box m (thirdOwner j)))) ∩
        {t | omega ≤ t 2})

def activeOutsideRegion (e : ℝ) (m : ℕ) (omega : ℝ) : Set (Fin 5 → ℝ) :=
  firstLabelRegion e m ∩
    (primeAffineGateRegion historicalUnorderedThirdGateForms
      (historicalUnorderedThirdGateBounds (initial e) (initial e)) ∩ {t | omega ≤ t 2})

def inactiveRegion (e : ℝ) (m : ℕ) (omega : ℝ) : Set (Fin 5 → ℝ) :=
  firstLabelRegion e m ∩
    (primeAffineGateRegion historicalUnorderedThirdGateForms
      (historicalUnorderedThirdGateBounds (initial e) (initial e)) ∩ {t | t 2 < omega})

theorem jointRegion_active_iff (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) (t : Fin 5 → ℝ) :
    (t ∈ jointRegion e chi m omega j ∧ omega ≤ t 2) ↔
      t ∈ activeRegion e chi m omega j := by
  by_cases hr : omega ≤ t 2 <;>
    simp [jointRegion, currentExponent, activeRegion, hr, and_assoc]

theorem activeRegion_eq_selected (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) (hj : thirdOwner j ∈ cells e chi m) :
    activeRegion e chi m omega j = selectedRegion e m omega j := by
  simp only [activeRegion, selectedRegion, thirdCellExponent, if_pos hj]

theorem activeRegion_eq_outside (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) (hj : thirdOwner j ∉ cells e chi m) :
    activeRegion e chi m omega j = activeOutsideRegion e m omega := by
  simp only [activeRegion, activeOutsideRegion, thirdCellExponent, if_neg hj]

theorem jointRegion_inactive_iff (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) (t : Fin 5 → ℝ) :
    (t ∈ jointRegion e chi m omega j ∧ ¬omega ≤ t 2) ↔ t ∈ inactiveRegion e m omega := by
  by_cases hr : omega ≤ t 2
  · have hnot : ¬t 2 < omega := not_lt.mpr hr
    simp [jointRegion, currentExponent, inactiveRegion, hr, hnot]
  · have hlt : t 2 < omega := lt_of_not_ge hr
    simp [jointRegion, currentExponent, inactiveRegion, hr, hlt, and_assoc]

/-- The inclusive activation uses the ORIGINAL raw triple history. -/
theorem candidates_active_cell_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (m + 1)) :
    ((candidates e chi m omega N cap).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
        (fun p => active omega (N : ℝ) (thirdHistory p)) =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈
        logPrimeMeshCell 0 (19 / 96) m j ∩ activeRegion e chi m omega j) := by
  rw [candidates_cell_filter e chi m omega N cap hN hcap j]
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hp, ht, hg⟩, ha⟩
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    exact ⟨hp, ht, (jointRegion_active_iff e chi m omega j _).mp
      ⟨hg, (thirdHistory_active_iff_log hN omega p hpos).mp ha⟩⟩
  · rintro ⟨hp, ht, hg⟩
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    obtain ⟨hr, ha⟩ := (jointRegion_active_iff e chi m omega j _).mpr hg
    exact ⟨⟨hp, ht, hr⟩, (thirdHistory_active_iff_log hN omega p hpos).mpr ha⟩

/-- Selected third ancestors use their stored original Gamma-2e level.
The firstStop and initial cube remain visible in this exact filter. -/
theorem candidates_selected_cell_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (m + 1)) (hj : thirdOwner j ∈ cells e chi m) :
    ((candidates e chi m omega N cap).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
        (fun p => active omega (N : ℝ) (thirdHistory p)) =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈
        logPrimeMeshCell 0 (19 / 96) m j ∩ selectedRegion e m omega j) := by
  rw [candidates_active_cell_filter e chi m omega N cap hN hcap j,
    activeRegion_eq_selected e chi m omega j hj]

/-- An unselected projected owner is the actual active OUTSIDE branch,
not a substituted cap from a D table. Both third cubes fall back to initial. -/
theorem candidates_outside_cell_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (m + 1)) (hj : thirdOwner j ∉ cells e chi m) :
    ((candidates e chi m omega N cap).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
        (fun p => active omega (N : ℝ) (thirdHistory p)) =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈
        logPrimeMeshCell 0 (19 / 96) m j ∩ activeOutsideRegion e m omega) := by
  rw [candidates_active_cell_filter e chi m omega N cap hN hcap j,
    activeRegion_eq_outside e chi m omega j hj]

/-- The inactive branch is strict t2<omega, while equality is active.
It restores the actual initial policy without forgetting firstStop. -/
theorem candidates_inactive_cell_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (m + 1)) :
    ((candidates e chi m omega N cap).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
        (fun p => ¬active omega (N : ℝ) (thirdHistory p)) =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈
        logPrimeMeshCell 0 (19 / 96) m j ∩ inactiveRegion e m omega) := by
  rw [candidates_cell_filter e chi m omega N cap hN hcap j]
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hp, ht, hg⟩, ha⟩
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    have hn : ¬omega ≤ actualPrimeTupleLog N p 2 :=
      fun h => ha ((thirdHistory_active_iff_log hN omega p hpos).mpr h)
    exact ⟨hp, ht, (jointRegion_inactive_iff e chi m omega j _).mp ⟨hg, hn⟩⟩
  · rintro ⟨hp, ht, hg⟩
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    obtain ⟨hr, ha⟩ := (jointRegion_inactive_iff e chi m omega j _).mpr hg
    exact ⟨⟨hp, ht, hr⟩, fun h => ha ((thirdHistory_active_iff_log hN omega p hpos).mp h)⟩

/-- Exhaustive partition of ALL fifth next candidates on this owner;
neither branch requires an old or a new fifth own-cube admission. -/
theorem candidates_cell_active_inactive_partition (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (j : Fin 5 → Fin (m + 1)) :
    (candidates e chi m omega N cap).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) =
      (((candidates e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
          (fun p => active omega (N : ℝ) (thirdHistory p))) ∪
      (((candidates e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
          (fun p => ¬active omega (N : ℝ) (thirdHistory p))) := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter]
  tauto

theorem candidates_cell_active_inactive_disjoint (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (j : Fin 5 → Fin (m + 1)) :
    Disjoint
      (((candidates e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
          (fun p => active omega (N : ℝ) (thirdHistory p)))
      (((candidates e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
          (fun p => ¬active omega (N : ℝ) (thirdHistory p))) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  exact (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2

/-- The original candidate mass and every signed cell summand are
preserved, ready for later old/new residuals without an own-cube filter. -/
theorem candidates_cell_weighted_sum (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (m + 1)) (F : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ candidates e chi m omega N cap, (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then F p else 0)) =
      ∑ p ∈ primeBox N, (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j ∩
          jointRegion e chi m omega j then F p else 0) := by
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter,
    candidates_cell_filter e chi m omega N cap hN hcap j]

end HistoricalThirdCoarse.P1OriginalCoarseFifth

end

end ImbalancedChen
