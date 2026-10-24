import ImbalancedChen.HistoricalThirdCoarsePolicy

/-!
# Actual retained third tuples on an adopted historical cell

The carrier is the literal rank-two frontier of `HistoricalThirdCoarse.policy`.
The third candidate is then tested by that very policy, and the rough activation
is retained as a separate inclusive condition. The finite dictionary below keeps
the initial first cube, the third level's own first cube, and the third cube.
No comparison between these levels, integral estimate, or mean is assumed.

This file is a source-only P1 candidate; it has not been compiled or replayed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators
open Set
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

namespace HistoricalThirdCoarse.P1ActualTuple

/-- Reverse storage of a triple whose function coordinates are in processing order. -/
def history (p : Fin 3 → ℕ) : List ℕ := [p 2, p 1, p 0]

theorem history_log (N : ℕ) (p : Fin 3 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 3 (history p) = actualPrimeTupleLog N p := by
  funext i
  fin_cases i <;> simp [history, primeHistoryLogCoordinates, primeHistoryTuple,
    actualPrimeTupleLog]

/-- Test the last candidate, after enumerating every actual rank-two parent. -/
def retainedTuples (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (z : ℝ) :
    Finset (Fin 3 → ℕ) :=
  (firstExitFrontierTuples 2 (policy e chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 z)).filter fun p =>
      policy e chi m omega (N : ℝ) false (history p) = true

/-- Activation includes equality at the manuscript's rough third cutoff. -/
def activeRetainedTuples (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) : Finset (Fin 3 → ℕ) :=
  (retainedTuples e chi m omega N cap z).filter fun p =>
    active omega (N : ℝ) (history p)

private theorem valid_triple_iff (P : Bool → List ℕ → Bool) (p : Fin 3 → ℕ) :
    FirstExitValidSelection P [] true (List.ofFn p) ↔
      FirstExitValidSelection P [] true (List.ofFn p).dropLast ∧
        P false (history p) = true := by
  have hof : List.ofFn p = [p 0, p 1, p 2] := by simp [List.ofFn_succ]
  simp [hof, FirstExitValidSelection, history, and_assoc]

/-- This filter really is full retention of all three selections, rather
than an arbitrary predicate attached to an unrelated tuple box. -/
theorem mem_retainedTuples_iff (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) (p : Fin 3 → ℕ) :
    p ∈ retainedTuples e chi m omega N cap z ↔
      List.ofFn p <+ roughPrimeUniverse N cap 0 z ∧
        FirstExitValidSelection (policy e chi m omega (N : ℝ)) [] true (List.ofFn p) := by
  simp only [retainedTuples, Finset.mem_filter]
  rw [mem_firstExitFrontierTuples_iff]
  constructor
  · rintro ⟨⟨hsub, hparent⟩, hthird⟩
    exact ⟨hsub, (valid_triple_iff _ p).mpr ⟨hparent, hthird⟩⟩
  · rintro ⟨hsub, hvalid⟩
    obtain ⟨hparent, hthird⟩ := (valid_triple_iff _ p).mp hvalid
    exact ⟨⟨hsub, hparent⟩, hthird⟩

theorem mem_activeRetainedTuples_iff (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) (p : Fin 3 → ℕ) :
    p ∈ activeRetainedTuples e chi m omega N cap z ↔
      (List.ofFn p <+ roughPrimeUniverse N cap 0 z ∧
        FirstExitValidSelection (policy e chi m omega (N : ℝ)) [] true (List.ofFn p)) ∧
          active omega (N : ℝ) (history p) := by
  simp only [activeRetainedTuples, Finset.mem_filter, mem_retainedTuples_iff]

private theorem singleton_admissible_iff (Q : ℝ) (p : ℕ) (hp : 0 < p) :
    ordinaryRosserPrefixAdmissible false Q [p] ↔ (p : ℝ) ^ 3 < Q := by
  have hsq : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hprod : (p : ℝ) ≤ (p : ℝ) ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) p)
    simpa only [mul_one, pow_succ, mul_comm] using hm
  have hc : UpperAdmissibleSet Q [p].toFinset ↔ (p : ℝ) ^ 3 < Q := by
    simp [UpperAdmissibleSet, Finset.filter_singleton, pow_succ, mul_comm]
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
    List.prod_cons, List.prod_nil, mul_one]
  rw [hc]
  exact ⟨fun h => h.2, fun h => ⟨hprod.trans_lt h, h⟩⟩

/-- The first label stop belongs to the actual parent admission. -/
theorem parent_two_iff (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p : Fin 3 → ℕ) (hp0 : 0 < p 0) :
    FirstExitValidSelection (policy e chi m omega N) [] true (List.ofFn p).dropLast ↔
      (p 0 : ℝ) ^ 3 < N ^ initial e ∧ firstStop e m N [p 0] := by
  have hdrop : (List.ofFn p).dropLast = [p 0, p 1] := by simp [List.ofFn_succ]
  rw [hdrop]
  simp only [FirstExitValidSelection, Bool.not_true, Bool.not_false, policy_even,
    and_true]
  rw [policy_through_two e chi m omega N false [p 0] (by simp)]
  simp [initialPolicy, oddFirstExitPolicy, singleton_admissible_iff _ _ hp0]

/-- The inclusive prime cutoff is exactly an inclusive logarithmic cutoff. -/
theorem active_iff_log {N : ℕ} (hN : 1 < N) (omega : ℝ)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i) :
    active omega (N : ℝ) (history p) ↔ omega ≤ actualPrimeTupleLog N p 2 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  rw [history, active_triple, ← actualPrimeTupleLog_rpow hN p hpos 2,
    Real.rpow_le_rpow_left_iff hNr]

/-- All three strict cubes survive the logarithmic dictionary. -/
theorem cube_tests_iff_log {N : ℕ} (hN : 1 < N) (initial third : ℝ)
    (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ initial ∧
      (p 0 : ℝ) ^ 3 < (N : ℝ) ^ third ∧
        (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ third) ↔
      3 * actualPrimeTupleLog N p 0 < initial ∧
        3 * actualPrimeTupleLog N p 0 < third ∧
          actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
            3 * actualPrimeTupleLog N p 2 < third := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hc i := actualPrimeTupleLog_rpow hN p hpos i
  have hcub (i : Fin 3) :
      (N : ℝ) ^ (3 * actualPrimeTupleLog N p i) = (p i : ℝ) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hN0.le, hc]
    norm_num
  have hprod : (N : ℝ) ^ (actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2) = (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, hc, hc, hcub]
  simp only [← hcub 0, ← hprod, Real.rpow_lt_rpow_left_iff hNr]

/-- Ordering, the initial first cube, the third own first cube, and the third cube. -/
def gateForms : Fin 5 → (Fin 3 → ℝ) →L[ℝ] ℝ :=
  let e (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  ![e 1 - e 0, e 2 - e 1, (3 : ℝ) • e 0, (3 : ℝ) • e 0,
    e 0 + e 1 + (3 : ℝ) • e 2]

def gateBounds (initial third : ℝ) : Fin 5 → ℝ := ![0, 0, initial, third, third]

theorem gateForms_ne_zero : ∀ j, gateForms j ≠ 0 := by
  intro j h
  have hh := congrArg (fun F : (Fin 3 → ℝ) →L[ℝ] ℝ =>
    F (fun i => (i.val : ℝ) + 1)) h
  fin_cases j <;> norm_num [gateForms] at hh

theorem mem_gateRegion (initial third : ℝ) (t : Fin 3 → ℝ) :
    t ∈ primeAffineGateRegion gateForms (gateBounds initial third) ↔
      StrictAnti t ∧ 3 * t 0 < initial ∧ 3 * t 0 < third ∧
        t 0 + t 1 + 3 * t 2 < third := by
  have hanti : StrictAnti t ↔ t 1 < t 0 ∧ t 2 < t 1 := by
    constructor
    · intro h
      exact ⟨h (by decide), h (by decide)⟩
    · rintro ⟨h1, h2⟩
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      fin_cases i
      · exact h1
      · exact h2
  simp only [hanti]
  simp [primeAffineGateRegion, gateForms, gateBounds, Fin.forall_fin_succ, and_assoc]

/-- The rough face is closed; every cube and ordering face remains strict. -/
def jointRegion (e omega : ℝ) (m : ℕ) (j : Cell m) : Set (Fin 3 → ℝ) :=
  primeAffineGateRegion gateForms (gateBounds (initial e) (levelExponent e (box m j))) ∩
    {t | omega ≤ t 2}

/-- Complete retained-admission dictionary on a half-open adopted cell.
No initial-to-third cap ordering is used to discard a first-cube condition. -/
theorem mem_activeRetainedTuples_iff_log_on_cell
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 3 → ℕ) (j : Cell m) (hj : j ∈ cells e chi m)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    p ∈ activeRetainedTuples e chi m omega N cap ((N : ℝ) ^ (19 / 96 : ℝ)) ↔
      (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
        0 ≤ (p i : ℝ) ∧ (p i : ℝ) < (N : ℝ) ^ (19 / 96 : ℝ)) ∧
          actualPrimeTupleLog N p ∈ jointRegion e omega m j := by
  have ht' : primeHistoryLogCoordinates (N : ℝ) 3 (history p) ∈
      logPrimeMeshCell 0 (19 / 96) m j := by
    rw [history_log]
    exact ht
  have hfront := mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap 2
    (policy e chi m omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) hcap p
  constructor
  · intro h
    obtain ⟨hret, ha⟩ := Finset.mem_filter.mp h
    obtain ⟨hf, hthird⟩ := Finset.mem_filter.mp hret
    obtain ⟨hsort, hprime, hparent⟩ := hfront.mp hf
    have hpos : ∀ i, 0 < p i := fun i => (hprime i).1.pos
    have hi := (parent_two_iff e chi m omega (N : ℝ) p (hpos 0)).mp hparent
    have hc := (policy_third_iff e chi m omega (N : ℝ)
      (p 0) (p 1) (p 2) (hpos 2)
      (hsort (by decide : (1 : Fin 3) < 2))
      (hsort (by decide : (0 : Fin 3) < 1))).mp hthird
    have hraw := rawLevel_on_cell e chi m omega (N : ℝ) (history p) ha j hj ht'
    change (p 0 : ℝ) ^ 3 < rawLevel e chi m omega (N : ℝ) (history p) ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 <
        rawLevel e chi m omega (N : ℝ) (history p) at hc
    rw [hraw] at hc
    have hlog := (cube_tests_iff_log hN (initial e) (levelExponent e (box m j))
      p hpos).mp ⟨hi.1, hc⟩
    refine ⟨hprime, ?_⟩
    change actualPrimeTupleLog N p ∈ primeAffineGateRegion gateForms
      (gateBounds (initial e) (levelExponent e (box m j))) ∧
        omega ≤ actualPrimeTupleLog N p 2
    exact ⟨(mem_gateRegion _ _ _).mpr
      ⟨(actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hsort, hlog⟩,
        (active_iff_log hN omega p hpos).mp ha⟩
  · rintro ⟨hprime, hg⟩
    have hpos : ∀ i, 0 < p i := fun i => (hprime i).1.pos
    change actualPrimeTupleLog N p ∈ primeAffineGateRegion gateForms
      (gateBounds (initial e) (levelExponent e (box m j))) ∧
        omega ≤ actualPrimeTupleLog N p 2 at hg
    have hlog := (mem_gateRegion _ _ _).mp hg.1
    have hsort := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp hlog.1
    have ha := (active_iff_log hN omega p hpos).mpr hg.2
    have hc := (cube_tests_iff_log hN (initial e) (levelExponent e (box m j))
      p hpos).mpr hlog.2
    have hparent := (parent_two_iff e chi m omega (N : ℝ) p (hpos 0)).mpr
      ⟨hc.1, firstStop_of_triple_cell e chi m (N : ℝ)
        (p 0) (p 1) (p 2) j hj ht'⟩
    have hraw := rawLevel_on_cell e chi m omega (N : ℝ) (history p) ha j hj ht'
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
    refine ⟨?_, ha⟩
    apply Finset.mem_filter.mpr
    exact ⟨hfront.mpr ⟨hsort, hprime, hparent⟩, hthird⟩

/-- Exact finite set equality, retaining half-open ownership, target deletion,
inclusive activation and all three strict cube tests. -/
theorem activeRetainedTuples_cell_filter
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Cell m) (hj : j ∈ cells e chi m) :
    (activeRetainedTuples e chi m omega N cap ((N : ℝ) ^ (19 / 96 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 3 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j) := by
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hp, ht⟩
    have hh := (mem_activeRetainedTuples_iff_log_on_cell
      e chi m omega N cap hN hcap p j hj ht).mp hp
    have hb : p ∈ actualPrimeBoxTuples N
        (fun _ : Fin 3 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hh.1 i).1, (hh.1 i).2.1⟩,
          logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96) m j ht⟩
    exact ⟨hb, ht, hh.2⟩
  · rintro ⟨hp, ht, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    refine ⟨(mem_activeRetainedTuples_iff_log_on_cell
      e chi m omega N cap hN hcap p j hj ht).mpr ⟨?_, hg⟩, ht⟩
    exact fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩

/-- Every real tuple summand transfers through the exact finite equality. -/
theorem activeRetainedTuples_cell_sum
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Cell m) (hj : j ∈ cells e chi m) (F : (Fin 3 → ℕ) → ℝ) :
    (∑ p ∈ (activeRetainedTuples e chi m omega N cap
      ((N : ℝ) ^ (19 / 96 : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j), F p) =
      ∑ p ∈ (actualPrimeBoxTuples N (fun _ : Fin 3 => (0 : ℝ))
        (fun _ => (19 / 96 : ℝ))).filter
          (fun p => actualPrimeTupleLog N p ∈
            logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion e omega m j), F p := by
  rw [activeRetainedTuples_cell_filter e chi m omega N cap hN hcap j hj]

end HistoricalThirdCoarse.P1ActualTuple

end

end ImbalancedChen
