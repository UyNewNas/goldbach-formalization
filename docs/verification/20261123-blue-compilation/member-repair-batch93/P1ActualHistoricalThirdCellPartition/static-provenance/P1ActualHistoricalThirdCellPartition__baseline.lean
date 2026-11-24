import ImbalancedChen.ActualHistoricalThirdTupleDictionary
import ImbalancedChen.HistoricalThirdFallbackSupportP1

/-!
# Exact selected/outside/inactive partition of the actual third tuple sum

Source-only P1 continuation. The two imports are sibling candidate adoption
paths. No source is installed into the actual tree by this file.

The full carrier is the actual retained rank-three selection below N^(19/96).
Selected cells, active outside their union, and inactive rough triples are
disjoint. Both fallback pieces keep the original first-label stop and the
strict first/third cube tests at `initial e` (Theta, not the geometry ceiling).
The theorem is finite and makes no analytic mean or integral assertion.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical List BigOperators
open Set

namespace HistoricalThirdCoarse.P1ActualPartition
open P1ActualTuple P1ThirdFallbackSupport

def full (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) : Finset (Fin 3 → ℕ) :=
  retainedTuples e chi m omega N cap ((N : ℝ) ^ (19 / 96 : ℝ))

def selectedCell (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (j : Cell m) :
    Finset (Fin 3 → ℕ) :=
  (activeRetainedTuples e chi m omega N cap ((N : ℝ) ^ (19 / 96 : ℝ))).filter
    fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j

def selectedPart (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    Finset (Fin 3 → ℕ) :=
  (cells e chi m).biUnion (selectedCell e chi m omega N cap)

def activeOutside (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    Finset (Fin 3 → ℕ) :=
  (full e chi m omega N cap).filter fun p =>
    active omega (N : ℝ) (history p) ∧
      actualPrimeTupleLog N p ∉ jointCells e chi m

def inactivePart (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    Finset (Fin 3 → ℕ) :=
  (full e chi m omega N cap).filter fun p => ¬active omega (N : ℝ) (history p)

def primeBox (N : ℕ) : Finset (Fin 3 → ℕ) :=
  actualPrimeBoxTuples N (fun _ => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))

/-- The first coarse-label stop, with exactly the original half-open ownership. -/
def firstLabelRegion (e : ℝ) (m : ℕ) : Set (Fin 3 → ℝ) :=
  {t | ∃ i : Fin (m + 1),
    logPrimeMeshPoint 0 (19 / 96) m i.val ≤ t 0 ∧
    t 0 < logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ∧
    logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤ VariableEnvelope.extendedFirstStop - 4 * e}

theorem firstStop_iff_log (e : ℝ) (m N : ℕ) (p : Fin 3 → ℕ) :
    firstStop e m (N : ℝ) [p 0] ↔ actualPrimeTupleLog N p ∈ firstLabelRegion e m := by
  simp [firstStop, firstLabelRegion, primeHistoryLogCoordinates,
    primeHistoryTuple, actualPrimeTupleLog]

/-- Both cube levels here are the actual initial exponent. The duplicate first
row in the shared gate API is harmless and leaves the strict first cube intact. -/
def fallbackRegion (e : ℝ) (m : ℕ) : Set (Fin 3 → ℝ) :=
  primeAffineGateRegion gateForms (gateBounds (initial e) (initial e)) ∩
    firstLabelRegion e m

def outsideRegion (e chi : ℝ) (m : ℕ) (omega : ℝ) : Set (Fin 3 → ℝ) :=
  fallbackRegion e m ∩ {t | omega ≤ t 2 ∧ t ∉ jointCells e chi m}

def inactiveRegion (e : ℝ) (m : ℕ) (omega : ℝ) : Set (Fin 3 → ℝ) :=
  fallbackRegion e m ∩ {t | t 2 < omega}

theorem mem_fallbackRegion (e : ℝ) (m : ℕ) (t : Fin 3 → ℝ) :
    t ∈ fallbackRegion e m ↔
      StrictAnti t ∧ 3 * t 0 < initial e ∧
        t 0 + t 1 + 3 * t 2 < initial e ∧ t ∈ firstLabelRegion e m := by
  simp only [fallbackRegion, Set.mem_inter_iff, mem_gateRegion]
  tauto

theorem mem_selectedPart (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ)
    (p : Fin 3 → ℕ) :
    p ∈ selectedPart e chi m omega N cap ↔
      p ∈ full e chi m omega N cap ∧ active omega (N : ℝ) (history p) ∧
        actualPrimeTupleLog N p ∈ jointCells e chi m := by
  simp only [selectedPart, Finset.mem_biUnion, selectedCell, Finset.mem_filter,
    activeRetainedTuples, full]
  constructor
  · rintro ⟨j, hj, ⟨hp, ha⟩, ht⟩
    exact ⟨hp, ha, j, hj, ht⟩
  · rintro ⟨hp, ha, j, hj, ht⟩
    exact ⟨j, hj, ⟨hp, ha⟩, ht⟩

theorem selectedCells_disjoint (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    Set.PairwiseDisjoint (cells e chi m : Set (Cell m))
      (selectedCell e chi m omega N cap) := by
  intro j _ k _ hne
  rw [Finset.disjoint_left]
  intro p hpj hpk
  exact hne (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
    (Finset.mem_filter.mp hpj).2 (Finset.mem_filter.mp hpk).2)

theorem selected_outside_disjoint (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    Disjoint (selectedPart e chi m omega N cap) (activeOutside e chi m omega N cap) := by
  rw [Finset.disjoint_left]
  intro p hs ho
  exact (Finset.mem_filter.mp ho).2.2 ((mem_selectedPart e chi m omega N cap p).mp hs).2.2

theorem selected_inactive_disjoint (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    Disjoint (selectedPart e chi m omega N cap) (inactivePart e chi m omega N cap) := by
  rw [Finset.disjoint_left]
  intro p hs hi
  exact (Finset.mem_filter.mp hi).2 ((mem_selectedPart e chi m omega N cap p).mp hs).2.1

theorem outside_inactive_disjoint (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    Disjoint (activeOutside e chi m omega N cap) (inactivePart e chi m omega N cap) := by
  rw [Finset.disjoint_left]
  intro p ho hi
  exact (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp ho).2.1

/-- Exhaustive and mutually exclusive finite partition of the actual retained set. -/
theorem full_partition (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) :
    full e chi m omega N cap =
      (selectedPart e chi m omega N cap ∪ activeOutside e chi m omega N cap) ∪
        inactivePart e chi m omega N cap := by
  ext p
  simp only [Finset.mem_union, mem_selectedPart, activeOutside, inactivePart,
    Finset.mem_filter]
  tauto

private theorem full_mem_primeBox (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    {p : Fin 3 → ℕ} (hp : p ∈ full e chi m omega N cap) : p ∈ primeBox N := by
  have hf := (Finset.mem_filter.mp hp).1
  have hh := (mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 2
    (policy e chi m omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) hcap p).mp hf
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  refine ⟨(hh.2.1 i).1, (hh.2.1 i).2.1, ?_, (hh.2.1 i).2.2.2⟩
  simpa only [Real.rpow_zero] using
    (show (1 : ℝ) ≤ p i by exact_mod_cast (hh.2.1 i).1.one_lt.le)

/-- Off actual support, full retained admission is precisely the original
initial strict cubes together with the literal first-label stop. -/
theorem mem_full_iff_fallback (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 3 → ℕ) (hp : p ∈ primeBox N)
    (hs : ¬supported e chi m omega (N : ℝ) (history p)) :
    p ∈ full e chi m omega N cap ↔ actualPrimeTupleLog N p ∈ fallbackRegion e m := by
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have hfront := mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 2
    (policy e chi m omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) hcap p
  have hraw := rawLevel_fallback e chi m omega (N : ℝ) (history p) hs
  constructor
  · intro h
    obtain ⟨hf, ht⟩ := Finset.mem_filter.mp h
    obtain ⟨hsort, _, hparent⟩ := hfront.mp hf
    have hi := (parent_two_iff e chi m omega (N : ℝ) p (hpos 0)).mp hparent
    have hc := (policy_third_iff e chi m omega (N : ℝ)
      (p 0) (p 1) (p 2) (hpos 2)
      (hsort (by decide : (1 : Fin 3) < 2))
      (hsort (by decide : (0 : Fin 3) < 1))).mp ht
    change (p 0 : ℝ) ^ 3 < rawLevel e chi m omega (N : ℝ) (history p) ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 <
        rawLevel e chi m omega (N : ℝ) (history p) at hc
    rw [hraw] at hc
    have hlog := (cube_tests_iff_log hN (initial e) (initial e) p hpos).mp ⟨hi.1, hc⟩
    exact (mem_fallbackRegion e m _).mpr
      ⟨(actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hsort,
        hlog.1, hlog.2.2, (firstStop_iff_log e m N p).mp hi.2⟩
  · intro hg
    have hh := (mem_fallbackRegion e m _).mp hg
    have hsort := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp hh.1
    have hc := (cube_tests_iff_log hN (initial e) (initial e) p hpos).mpr
      ⟨hh.2.1, hh.2.1, hh.2.2.1⟩
    have hparent := (parent_two_iff e chi m omega (N : ℝ) p (hpos 0)).mpr
      ⟨hc.1, (firstStop_iff_log e m N p).mpr hh.2.2.2⟩
    have hthird : policy e chi m omega (N : ℝ) false (history p) = true := by
      apply (policy_third_iff e chi m omega (N : ℝ)
        (p 0) (p 1) (p 2) (hpos 2)
        (hsort (by decide : (1 : Fin 3) < 2))
        (hsort (by decide : (0 : Fin 3) < 1))).mpr
      change (p 0 : ℝ) ^ 3 < rawLevel e chi m omega (N : ℝ) (history p) ∧
        (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 <
          rawLevel e chi m omega (N : ℝ) (history p)
      rw [hraw]
      exact hc.2
    apply Finset.mem_filter.mpr
    refine ⟨hfront.mpr ⟨hsort, ?_, hparent⟩, hthird⟩
    exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

theorem activeOutside_eq_log_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) :
    activeOutside e chi m omega N cap =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈ outsideRegion e chi m omega) := by
  ext p
  constructor
  · intro h
    obtain ⟨hf, ha, ho⟩ := Finset.mem_filter.mp h
    have hp := full_mem_primeBox e chi m omega N cap hcap hf
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    have hs : ¬supported e chi m omega (N : ℝ) (history p) := by
      rintro ⟨_, hu⟩
      rw [history_log] at hu
      exact ho hu
    exact Finset.mem_filter.mpr ⟨hp,
      (mem_full_iff_fallback e chi m omega N cap hN hcap p hp hs).mp hf,
      (active_iff_log hN omega p hpos).mp ha, ho⟩
  · intro h
    obtain ⟨hp, hg, ha, ho⟩ := Finset.mem_filter.mp h
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    have hs : ¬supported e chi m omega (N : ℝ) (history p) := by
      rintro ⟨_, hu⟩
      rw [history_log] at hu
      exact ho hu
    exact Finset.mem_filter.mpr
      ⟨(mem_full_iff_fallback e chi m omega N cap hN hcap p hp hs).mpr hg,
        (active_iff_log hN omega p hpos).mpr ha, ho⟩

theorem inactivePart_eq_log_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) :
    inactivePart e chi m omega N cap =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈ inactiveRegion e m omega) := by
  ext p
  constructor
  · intro h
    obtain ⟨hf, ha⟩ := Finset.mem_filter.mp h
    have hp := full_mem_primeBox e chi m omega N cap hcap hf
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    have hs : ¬supported e chi m omega (N : ℝ) (history p) := fun h => ha h.1
    exact Finset.mem_filter.mpr
      ⟨hp, (mem_full_iff_fallback e chi m omega N cap hN hcap p hp hs).mp hf,
        lt_of_not_ge (fun h => ha ((active_iff_log hN omega p hpos).mpr h))⟩
  · intro h
    obtain ⟨hp, hg, hi⟩ := Finset.mem_filter.mp h
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    have ha : ¬active omega (N : ℝ) (history p) :=
      fun h => (not_le_of_gt hi) ((active_iff_log hN omega p hpos).mp h)
    have hs : ¬supported e chi m omega (N : ℝ) (history p) := fun h => ha h.1
    exact Finset.mem_filter.mpr
      ⟨(mem_full_iff_fallback e chi m omega N cap hN hcap p hp hs).mpr hg, ha⟩

/-- The disjoint partition is valid for every signed real tuple summand. -/
theorem full_sum_partition (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ)
    (F : (Fin 3 → ℕ) → ℝ) :
    (∑ p ∈ full e chi m omega N cap, F p) =
      (∑ j ∈ cells e chi m, ∑ p ∈ selectedCell e chi m omega N cap j, F p) +
        (∑ p ∈ activeOutside e chi m omega N cap, F p) +
          ∑ p ∈ inactivePart e chi m omega N cap, F p := by
  have hd : Disjoint
      (selectedPart e chi m omega N cap ∪ activeOutside e chi m omega N cap)
      (inactivePart e chi m omega N cap) := by
    rw [Finset.disjoint_left]
    intro p hp hi
    rcases Finset.mem_union.mp hp with hs | ho
    · exact Finset.disjoint_left.mp (selected_inactive_disjoint e chi m omega N cap) hs hi
    · exact Finset.disjoint_left.mp (outside_inactive_disjoint e chi m omega N cap) ho hi
  rw [full_partition, Finset.sum_union hd,
    Finset.sum_union (selected_outside_disjoint e chi m omega N cap)]
  rw [selectedPart, Finset.sum_biUnion (selectedCells_disjoint e chi m omega N cap)]

/-- Literal reciprocal-prime mass, with no totient distinctness shortcut. -/
def tupleWeight (p : Fin 3 → ℕ) : ℝ := ∏ i, 1 / ((p i : ℝ) - 1)

/-- Complete actual third tuple count-to-joint-cell-and-fallback dictionary.
The selected part uses each cell's actual joint gate. Outside and inactive
parts use the original initial cubes and preserve firstStop explicitly. -/
theorem full_weighted_sum_eq_joint_cells_add_fallback
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (F : (Fin 3 → ℕ) → ℝ) :
    (∑ p ∈ full e chi m omega N cap, tupleWeight p * F p) =
      (∑ j ∈ cells e chi m,
        ∑ p ∈ (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j), tupleWeight p * F p) +
      (∑ p ∈ (primeBox N).filter (fun p =>
        actualPrimeTupleLog N p ∈ outsideRegion e chi m omega), tupleWeight p * F p) +
      ∑ p ∈ (primeBox N).filter (fun p =>
        actualPrimeTupleLog N p ∈ inactiveRegion e m omega), tupleWeight p * F p := by
  have hselected :
      (∑ j ∈ cells e chi m,
        ∑ p ∈ selectedCell e chi m omega N cap j, tupleWeight p * F p) =
      ∑ j ∈ cells e chi m,
        ∑ p ∈ (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j),
            tupleWeight p * F p := by
    apply Finset.sum_congr rfl
    intro j hj
    exact activeRetainedTuples_cell_sum e chi m omega N cap hN hcap j hj
      (fun p => tupleWeight p * F p)
  rw [full_sum_partition,
    activeOutside_eq_log_filter e chi m omega N cap hN hcap,
    inactivePart_eq_log_filter e chi m omega N cap hN hcap, hselected]

end HistoricalThirdCoarse.P1ActualPartition
end
end ImbalancedChen
