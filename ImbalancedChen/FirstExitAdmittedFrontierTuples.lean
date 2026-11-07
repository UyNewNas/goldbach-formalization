import ImbalancedChen.FirstExitFrontierTupleReindex

/-!
# Exact tuple sums for the admitted depth frontier

Unlike next candidates, every selected prime in this frontier has passed
its policy test. The concrete recursion and the complete valid sublist
enumeration have the same multiplicities, before taking a finite set.
This transfers fourth-level upper residuals on the actual historical tree.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators

/-- Processing-order choices with every selected prefix tested. -/
def firstExitAdmittedChoices {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (pre : List α) (positive : Bool)
    (carrier : List α) : List (List α) :=
  (carrier.sublistsLen k).filter fun chosen =>
    decide (FirstExitValidSelection parent pre positive chosen)

private theorem admittedChoices_zero {α : Type*}
    (parent : Bool → List α → Bool) (pre carrier : List α) (positive : Bool) :
    firstExitAdmittedChoices 0 parent pre positive carrier = [[]] := by
  have hv : decide (FirstExitValidSelection parent pre positive []) = true :=
    decide_eq_true_eq.mpr trivial
  simp [firstExitAdmittedChoices, List.filter_nil, hv]

private theorem admittedChoices_cons {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (pre carrier : List α) (positive : Bool) (p : α) :
    firstExitAdmittedChoices (k + 1) parent pre positive (p :: carrier) =
      firstExitAdmittedChoices (k + 1) parent pre positive carrier ++
        if parent (!positive) (p :: pre) = true then
          (firstExitAdmittedChoices k parent (p :: pre) (!positive) carrier).map (List.cons p)
        else [] := by
  by_cases hp : parent (!positive) (p :: pre) = true <;>
    simp [firstExitAdmittedChoices, List.sublistsLen_succ_cons, List.filter_append,
      List.filter_map, Function.comp_def, FirstExitValidSelection, hp]

/-- The genuine stopped frontier preserves the multiplicities of all
fully admitted sublists, including the empty frontier at depth zero. -/
theorem firstExitDepthFrontier_admitted_history_perm {α : Type*}
    (r : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    ((firstExitDepthFrontier (pre.length + r) parent h pre positive mass carrier).map
      (fun state => state.selectedPrefix.reverse)).Perm
      ((firstExitAdmittedChoices r parent pre positive carrier).map
        (fun chosen => pre.reverse ++ chosen)) := by
  induction carrier generalizing r pre positive mass with
  | nil =>
      cases r with
      | zero => simp [firstExitDepthFrontier, admittedChoices_zero]
      | succ r => simp [firstExitDepthFrontier, firstExitAdmittedChoices]
  | cons p ps ih =>
      cases r with
      | zero =>
          simp [firstExitDepthFrontier, admittedChoices_zero]
      | succ r =>
          have hk : ¬ pre.length + (r + 1) ≤ pre.length := by omega
          rw [firstExitDepthFrontier, if_neg hk, admittedChoices_cons,
            List.map_append, List.map_append]
          by_cases hp : parent (!positive) (p :: pre) = true
          · rw [if_pos hp, if_pos hp]
            apply List.Perm.append (ih (r + 1) pre positive mass)
            have hh := ih r (p :: pre) (!positive) (mass * h p)
            simpa only [List.length_cons, List.reverse_cons, List.map_map,
              Function.comp_def, List.append_assoc, List.singleton_append,
              show pre.length + 1 + r = pre.length + (r + 1) by omega] using hh
          · simp only [if_neg hp, List.map_nil, List.append_nil]
            exact ih (r + 1) pre positive mass

theorem firstExitRootFrontier_admitted_history_perm {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (h : α → ℝ) (carrier : List α) :
    ((firstExitDepthFrontier k parent h [] true 1 carrier).map
      (fun state => state.selectedPrefix.reverse)).Perm
      (firstExitAdmittedChoices k parent [] true carrier) := by
  simpa using firstExitDepthFrontier_admitted_history_perm k parent h [] carrier true 1

/-- Admitted tuples differ from candidate tuples: their final selection
is tested as well as every earlier selection. -/
def firstExitAdmittedTuples (k : ℕ) (parent : Bool → List ℕ → Bool)
    (carrier : List ℕ) : Finset (Fin k → ℕ) :=
  ((firstExitAdmittedChoices k parent [] true carrier).map
    (fun chosen => primeHistoryTuple k chosen.reverse)).toFinset

private theorem admittedTuple_ofFn {k : ℕ} {chosen : List ℕ}
    (hc : chosen.length = k) :
    List.ofFn (primeHistoryTuple k chosen.reverse) = chosen := by
  simpa only [List.reverse_reverse] using primeHistoryTuple_ofFn
    (show chosen.reverse.length = k by simpa using hc)

theorem mem_firstExitAdmittedTuples_iff (k : ℕ)
    (parent : Bool → List ℕ → Bool) (carrier : List ℕ) (p : Fin k → ℕ) :
    p ∈ firstExitAdmittedTuples k parent carrier ↔
      List.ofFn p <+ carrier ∧ FirstExitValidSelection parent [] true (List.ofFn p) := by
  simp only [firstExitAdmittedTuples, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨chosen, hc, rfl⟩
    have hh : chosen <+ carrier ∧ chosen.length = k ∧
        FirstExitValidSelection parent [] true chosen := by
      simpa only [firstExitAdmittedChoices, List.mem_filter, List.mem_sublistsLen,
        decide_eq_true_eq, and_assoc] using hc
    rw [admittedTuple_ofFn hh.2.1]
    exact ⟨hh.1, hh.2.2⟩
  · rintro ⟨hsub, hv⟩
    refine ⟨List.ofFn p, ?_, ?_⟩
    · simp only [firstExitAdmittedChoices, List.mem_filter, List.mem_sublistsLen,
        decide_eq_true_eq]
      exact ⟨⟨hsub, List.length_ofFn⟩, hv⟩
    · apply List.ofFn_injective
      exact admittedTuple_ofFn List.length_ofFn

private theorem admittedChoices_tuple_nodup (k : ℕ)
    (parent : Bool → List ℕ → Bool) (carrier : List ℕ) (hc : carrier.Nodup) :
    ((firstExitAdmittedChoices k parent [] true carrier).map
      (fun chosen => primeHistoryTuple k chosen.reverse)).Nodup := by
  apply ((List.nodup_sublistsLen k hc).filter
    (fun chosen => decide (FirstExitValidSelection parent [] true chosen))).map_on
  intro x hx y hy he
  have hxlen := List.length_of_sublistsLen (List.mem_filter.mp hx).1
  have hylen := List.length_of_sublistsLen (List.mem_filter.mp hy).1
  simpa only [admittedTuple_ofFn hxlen, admittedTuple_ofFn hylen] using congrArg List.ofFn he

theorem firstExitRootFrontier_admitted_tuple_perm (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ) :
    ((firstExitDepthFrontier k parent h [] true 1 carrier).map
      (fun state => primeHistoryTuple k state.selectedPrefix)).Perm
      ((firstExitAdmittedChoices k parent [] true carrier).map
        (fun chosen => primeHistoryTuple k chosen.reverse)) := by
  simpa only [List.map_map, Function.comp_def, List.reverse_reverse] using
    (firstExitRootFrontier_admitted_history_perm k parent h carrier).map
      (fun chosen => primeHistoryTuple k chosen.reverse)

theorem firstExitRootFrontier_admitted_tuple_nodup (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (hc : carrier.Nodup) :
    ((firstExitDepthFrontier k parent h [] true 1 carrier).map
      (fun state => primeHistoryTuple k state.selectedPrefix)).Nodup :=
  (firstExitRootFrontier_admitted_tuple_perm k parent h carrier).nodup_iff.mpr
    (admittedChoices_tuple_nodup k parent carrier hc)

/-- Exact arbitrary summation on the fully admitted tuple set. -/
theorem firstExitRootFrontier_sum_eq_admitted_tuple_sum (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (hc : carrier.Nodup) (f : (Fin k → ℕ) → ℝ) :
    ((firstExitDepthFrontier k parent h [] true 1 carrier).map
      (fun state => f (primeHistoryTuple k state.selectedPrefix))).sum =
      ∑ p ∈ firstExitAdmittedTuples k parent carrier, f p := by
  have he := ((firstExitRootFrontier_admitted_tuple_perm k parent h carrier).map f).sum_eq
  simp only [List.map_map, Function.comp_def] at he
  rw [he]
  simpa only [List.map_map, Function.comp_def, firstExitAdmittedTuples] using
    (List.sum_toFinset f (admittedChoices_tuple_nodup k parent carrier hc)).symm

theorem firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (hc : carrier.Nodup) (f : (Fin k → ℕ) → ℝ) :
    ((firstExitDepthFrontier k parent h [] true 1 carrier).map (fun state =>
      (state.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        f (primeHistoryTuple k state.selectedPrefix))).sum =
      ∑ p ∈ firstExitAdmittedTuples k parent carrier,
        (∏ i, 1 / ((p i : ℝ) - 1)) * f p := by
  rw [← firstExitRootFrontier_sum_eq_admitted_tuple_sum k parent h carrier hc
    (fun p => (∏ i, 1 / ((p i : ℝ) - 1)) * f p)]
  congr 1
  apply List.map_congr_left
  intro state hs
  rw [primeHistoryTuple_reciprocal_mass
    (firstExitDepthFrontier_selected_length k parent h [] carrier true 1 (by simp) state hs)]

theorem firstExitRootFrontier_history_sum_eq_admitted_tuple_sum (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (hc : carrier.Nodup) (F : List ℕ → ℝ) :
    ((firstExitDepthFrontier k parent h [] true 1 carrier).map (fun state =>
      (state.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        F state.selectedPrefix)).sum =
      ∑ p ∈ firstExitAdmittedTuples k parent carrier,
        (∏ i, 1 / ((p i : ℝ) - 1)) * F (List.ofFn p).reverse := by
  rw [← firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum k parent h carrier hc
    (fun p => F (List.ofFn p).reverse)]
  congr 1
  apply List.map_congr_left
  intro state hs
  rw [primeHistoryTuple_reverse_ofFn
    (firstExitDepthFrontier_selected_length k parent h [] carrier true 1 (by simp) state hs)]

theorem mem_firstExitAdmittedTuples_iff_of_decreasing (k : ℕ)
    (parent : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hc : carrier.Pairwise (· > ·)) (p : Fin k → ℕ) :
    p ∈ firstExitAdmittedTuples k parent carrier ↔
      StrictAnti p ∧ (∀ i, p i ∈ carrier) ∧
        FirstExitValidSelection parent [] true (List.ofFn p) := by
  rw [mem_firstExitAdmittedTuples_iff]
  constructor
  · rintro ⟨hs, hv⟩
    exact ⟨List.pairwise_ofFn.mp (hc.sublist hs),
      fun i => hs.subset (List.mem_ofFn.mpr ⟨i, rfl⟩), hv⟩
  · rintro ⟨ha, hm, hv⟩
    have hp : (List.ofFn p).Pairwise (· > ·) := List.pairwise_ofFn.mpr ha
    have hsub : List.ofFn p ⊆ carrier := by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact hm i
    exact ⟨List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset hp.nodup hsub) hp hc, hv⟩

theorem mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap (k : ℕ)
    (parent : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hzcap : z ≤ (cap : ℝ)) (p : Fin k → ℕ) :
    p ∈ firstExitAdmittedTuples k parent (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧ w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        FirstExitValidSelection parent [] true (List.ofFn p) := by
  rw [mem_firstExitAdmittedTuples_iff_of_decreasing k parent _
    (roughPrimeUniverse_pairwise_gt N cap w z)]
  simp only [mem_roughPrimeUniverse_iff_of_cutoff_le_cap hzcap]

end

end ImbalancedChen
