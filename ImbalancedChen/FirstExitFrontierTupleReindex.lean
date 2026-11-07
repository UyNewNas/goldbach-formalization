import ImbalancedChen.FirstExitOwnCubeSplice
import ImbalancedChen.FirstExitFrontierInvariants
import ImbalancedChen.FirstExitValidSelection
import ImbalancedChen.FinitePrimeGeometryCore

/-!
# Exact tuple reindexing before a candidate's own admission

The actual rank-`k` parent frontier is flattened into all next-selection
candidates. Its histories, with their original multiplicities, are proved
to be a permutation of the length-`k+1` sublists whose first `k` selections
pass the parent policy. The last selected label is deliberately untested.
Only after this permutation and a no-repetition proof do we pass to a
finite tuple set. No density or distribution estimate is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical List BigOperators

/-- The literal candidate list, before either own-cube admission test. -/
def firstExitFrontierCandidates {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (h : α → ℝ) (carrier : List α) :
    List (FirstExitDepthState α) :=
  (firstExitDepthFrontier k parent h [] true 1 carrier).flatMap fun state =>
    firstExitNextSelectionCandidates h state.selectedPrefix state.positive state.mass
      state.remaining

/-- Processing-order selections with only their proper parent prefix tested. -/
def firstExitParentChoices {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (pre : List α) (positive : Bool)
    (carrier : List α) : List (List α) :=
  (carrier.sublistsLen (k + 1)).filter fun chosen =>
    decide (FirstExitValidSelection parent pre positive chosen.dropLast)

private theorem nextCandidates_reverse_history {α : Type*} (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    (firstExitNextSelectionCandidates h pre positive mass carrier).map
        (fun state => state.selectedPrefix.reverse) =
      carrier.map (fun p => pre.reverse ++ [p]) := by
  induction carrier with
  | nil => rfl
  | cons p ps ih =>
      change (p :: pre).reverse ::
          ((firstExitNextSelectionCandidates h pre positive mass ps).map
            (fun state => state.selectedPrefix.reverse)) =
        (pre.reverse ++ [p]) :: ps.map (fun q => pre.reverse ++ [q])
      rw [List.reverse_cons, ih]

private theorem parentChoices_zero {α : Type*}
    (parent : Bool → List α → Bool) (pre carrier : List α) (positive : Bool) :
    firstExitParentChoices 0 parent pre positive carrier = carrier.reverse.map (fun p => [p]) := by
  simp [firstExitParentChoices, List.sublistsLen_one, List.filter_map,
    Function.comp_def, FirstExitValidSelection]

private theorem parentChoices_cons {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (pre carrier : List α) (positive : Bool) (p : α) :
    firstExitParentChoices (k + 1) parent pre positive (p :: carrier) =
      firstExitParentChoices (k + 1) parent pre positive carrier ++
        if parent (!positive) (p :: pre) = true then
          (firstExitParentChoices k parent (p :: pre) (!positive) carrier).map (List.cons p)
        else [] := by
  unfold firstExitParentChoices
  rw [List.sublistsLen_succ_cons, List.filter_append]
  congr 1
  have hfilter (xs : List (List α)) (hne : ∀ x ∈ xs, x ≠ []) :
      (xs.map (List.cons p)).filter (fun x =>
          decide (FirstExitValidSelection parent pre positive x.dropLast)) =
        if parent (!positive) (p :: pre) = true then
          (xs.filter (fun x => decide
            (FirstExitValidSelection parent (p :: pre) (!positive) x.dropLast))).map (List.cons p)
        else [] := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        have hx := hne x (by simp)
        have hxs := ih (fun y hy => hne y (by simp [hy]))
        cases x with
        | nil => exact (hx rfl).elim
        | cons q qs =>
            by_cases hp : parent (!positive) (p :: pre) = true <;>
              by_cases hv : FirstExitValidSelection parent (p :: pre) (!positive)
                (q :: qs).dropLast <;>
              simp [List.dropLast_cons_cons,
                FirstExitValidSelection, hp, hxs, hv]
  apply hfilter
  intro x hx heq
  have hlen := List.length_of_sublistsLen hx
  simp [heq] at hlen

/-- The stopped frontier has precisely the multiplicities of the concrete
valid sublist enumeration; no leaf-support surrogate is used. -/
theorem firstExitDepthFrontier_candidates_history_perm
    {α : Type*} (r : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    (((firstExitDepthFrontier (pre.length + r) parent h pre positive mass carrier).flatMap
      (fun state => firstExitNextSelectionCandidates h state.selectedPrefix state.positive
        state.mass state.remaining)).map (fun state => state.selectedPrefix.reverse)).Perm
      ((firstExitParentChoices r parent pre positive carrier).map
        (fun chosen => pre.reverse ++ chosen)) := by
  induction carrier generalizing r pre positive mass with
  | nil => cases r <;> simp [firstExitDepthFrontier, firstExitNextSelectionCandidates,
      firstExitParentChoices]
  | cons p ps ih =>
      cases r with
      | zero =>
          rw [Nat.add_zero, firstExitDepthFrontier_of_rank_le_length _ _ _ _ _ _ _ le_rfl]
          simp only [List.flatMap_singleton, nextCandidates_reverse_history, parentChoices_zero,
            List.map_map, Function.comp_def, List.reverse_cons]
          simpa only [List.reverse_cons] using (List.reverse_perm (p :: ps)).symm.map
            (fun p => pre.reverse ++ [p])
      | succ r =>
          have hk : ¬ pre.length + (r + 1) ≤ pre.length := by omega
          rw [firstExitDepthFrontier, if_neg hk, parentChoices_cons,
            List.flatMap_append, List.map_append, List.map_append]
          by_cases hp : parent (!positive) (p :: pre) = true
          · rw [if_pos hp, if_pos hp]
            apply List.Perm.append (ih (r + 1) pre positive mass)
            have hh := ih r (p :: pre) (!positive) (mass * h p)
            simpa only [List.length_cons, List.reverse_cons, List.map_map,
              Function.comp_def, List.append_assoc, List.singleton_append,
              show pre.length + 1 + r = pre.length + (r + 1) by omega] using hh
          · simp only [if_neg hp, List.flatMap_nil, List.map_nil, List.append_nil]
            exact ih (r + 1) pre positive mass

theorem firstExitFrontierCandidates_history_perm {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (h : α → ℝ) (carrier : List α) :
    ((firstExitFrontierCandidates k parent h carrier).map
      (fun state => state.selectedPrefix.reverse)).Perm
        (firstExitParentChoices k parent [] true carrier) := by
  simpa [firstExitFrontierCandidates] using
      firstExitDepthFrontier_candidates_history_perm k parent h [] carrier true 1

/-- Exact no-repetition holds for the actual candidate history list,
before any conversion to a finite set. -/
theorem firstExitFrontierCandidates_history_nodup {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (h : α → ℝ) (carrier : List α)
    (hc : carrier.Nodup) :
    ((firstExitFrontierCandidates k parent h carrier).map
      (fun state => state.selectedPrefix.reverse)).Nodup := by
  apply (firstExitFrontierCandidates_history_perm k parent h carrier).nodup_iff.mpr
  exact (List.nodup_sublistsLen _ hc).filter _

theorem mem_firstExitFrontierCandidates_history_iff {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (h : α → ℝ) (carrier chosen : List α) :
    chosen ∈ (firstExitFrontierCandidates k parent h carrier).map
        (fun state => state.selectedPrefix.reverse) ↔
      chosen <+ carrier ∧ chosen.length = k + 1 ∧
        FirstExitValidSelection parent [] true chosen.dropLast := by
  rw [(firstExitFrontierCandidates_history_perm k parent h carrier).mem_iff]
  simp only [firstExitParentChoices, List.mem_filter, List.mem_sublistsLen, decide_eq_true_eq]
  tauto

theorem firstExitFrontierCandidates_selected_length {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (h : α → ℝ) (carrier : List α)
    (state : FirstExitDepthState α)
    (hs : state ∈ firstExitFrontierCandidates k parent h carrier) :
    state.selectedPrefix.length = k + 1 := by
  have hh := (mem_firstExitFrontierCandidates_history_iff k parent h carrier
    state.selectedPrefix.reverse).mp (List.mem_map.mpr ⟨state, hs, rfl⟩)
  simpa only [List.length_reverse] using hh.2.1

/-- Canonical ordered tuple enumeration, independently of any local weights.
The only policy filter is on `dropLast`; the final candidate remains untested. -/
def firstExitFrontierTuples (k : ℕ) (parent : Bool → List ℕ → Bool)
    (carrier : List ℕ) : Finset (Fin (k + 1) → ℕ) :=
  ((firstExitParentChoices k parent [] true carrier).map
    (fun chosen => primeHistoryTuple (k + 1) chosen.reverse)).toFinset

private theorem selectionTuple_ofFn {k : ℕ} {chosen : List ℕ}
    (hc : chosen.length = k + 1) :
    List.ofFn (primeHistoryTuple (k + 1) chosen.reverse) = chosen := by
  simpa only [List.reverse_reverse] using primeHistoryTuple_ofFn
    (show chosen.reverse.length = k + 1 by simpa using hc)

private theorem selectionTuple_injective {k : ℕ} {x y : List ℕ}
    (hx : x.length = k + 1) (hy : y.length = k + 1)
    (he : primeHistoryTuple (k + 1) x.reverse = primeHistoryTuple (k + 1) y.reverse) :
    x = y := by
  simpa only [selectionTuple_ofFn hx, selectionTuple_ofFn hy] using congrArg List.ofFn he

theorem mem_firstExitFrontierTuples_iff (k : ℕ)
    (parent : Bool → List ℕ → Bool) (carrier : List ℕ) (p : Fin (k + 1) → ℕ) :
    p ∈ firstExitFrontierTuples k parent carrier ↔
      List.ofFn p <+ carrier ∧ FirstExitValidSelection parent [] true (List.ofFn p).dropLast := by
  simp only [firstExitFrontierTuples, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨chosen, hc, rfl⟩
    have hh : chosen <+ carrier ∧ chosen.length = k + 1 ∧
        FirstExitValidSelection parent [] true chosen.dropLast := by
      simpa only [firstExitParentChoices, List.mem_filter, List.mem_sublistsLen,
        decide_eq_true_eq, and_assoc] using hc
    rw [selectionTuple_ofFn hh.2.1]
    exact ⟨hh.1, hh.2.2⟩
  · rintro ⟨hsub, hv⟩
    refine ⟨List.ofFn p, ?_, ?_⟩
    · simp only [firstExitParentChoices, List.mem_filter, List.mem_sublistsLen,
        decide_eq_true_eq]
      exact ⟨⟨hsub, List.length_ofFn⟩, hv⟩
    · apply List.ofFn_injective
      exact selectionTuple_ofFn List.length_ofFn

private theorem parentChoices_tuple_nodup (k : ℕ)
    (parent : Bool → List ℕ → Bool) (carrier : List ℕ) (hc : carrier.Nodup) :
    ((firstExitParentChoices k parent [] true carrier).map
      (fun chosen => primeHistoryTuple (k + 1) chosen.reverse)).Nodup := by
  apply ((List.nodup_sublistsLen (k + 1) hc).filter
    (fun chosen => decide (FirstExitValidSelection parent [] true chosen.dropLast))).map_on
  intro x hx y hy he
  exact selectionTuple_injective (List.length_of_sublistsLen (List.mem_filter.mp hx).1)
    (List.length_of_sublistsLen (List.mem_filter.mp hy).1) he

theorem firstExitFrontierCandidates_tuple_perm (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ) :
    ((firstExitFrontierCandidates k parent h carrier).map
      (fun state => primeHistoryTuple (k + 1) state.selectedPrefix)).Perm
      ((firstExitParentChoices k parent [] true carrier).map
        (fun chosen => primeHistoryTuple (k + 1) chosen.reverse)) := by
  simpa only [List.map_map, Function.comp_def, List.reverse_reverse] using
    (firstExitFrontierCandidates_history_perm k parent h carrier).map
      (fun chosen => primeHistoryTuple (k + 1) chosen.reverse)

theorem firstExitFrontierCandidates_tuple_nodup (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (hc : carrier.Nodup) :
    ((firstExitFrontierCandidates k parent h carrier).map
      (fun state => primeHistoryTuple (k + 1) state.selectedPrefix)).Nodup :=
  (firstExitFrontierCandidates_tuple_perm k parent h carrier).nodup_iff.mpr
    (parentChoices_tuple_nodup k parent carrier hc)

/-- Exact finite-sum transfer, with no hidden multiplicity and no last gate. -/
theorem firstExitFrontierCandidates_sum_eq_tuple_sum (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (hc : carrier.Nodup) (f : (Fin (k + 1) → ℕ) → ℝ) :
    ((firstExitFrontierCandidates k parent h carrier).map
      (fun state => f (primeHistoryTuple (k + 1) state.selectedPrefix))).sum =
      ∑ p ∈ firstExitFrontierTuples k parent carrier, f p := by
  have he := ((firstExitFrontierCandidates_tuple_perm k parent h carrier).map f).sum_eq
  simp only [List.map_map, Function.comp_def] at he
  rw [he]
  simpa only [List.map_map, Function.comp_def, firstExitFrontierTuples] using
    (List.sum_toFinset f (parentChoices_tuple_nodup k parent carrier hc)).symm

/-- Prefix reciprocal mass is preserved before applying the tuple summand. -/
theorem firstExitFrontierCandidates_weighted_sum_eq_tuple_sum (k : ℕ)
    (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (hc : carrier.Nodup) (f : (Fin (k + 1) → ℕ) → ℝ) :
    ((firstExitFrontierCandidates k parent h carrier).map (fun state =>
      (state.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        f (primeHistoryTuple (k + 1) state.selectedPrefix))).sum =
      ∑ p ∈ firstExitFrontierTuples k parent carrier,
        (∏ i, 1 / ((p i : ℝ) - 1)) * f p := by
  rw [← firstExitFrontierCandidates_sum_eq_tuple_sum k parent h carrier hc
    (fun p => (∏ i, 1 / ((p i : ℝ) - 1)) * f p)]
  congr 1
  apply List.map_congr_left
  intro state hs
  rw [primeHistoryTuple_reciprocal_mass
    (firstExitFrontierCandidates_selected_length k parent h carrier state hs)]

/-- On a descending carrier the concrete tuple condition is exactly
strict decrease, coordinate membership, and admission of the proper prefix. -/
theorem mem_firstExitFrontierTuples_iff_of_decreasing (k : ℕ)
    (parent : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hc : carrier.Pairwise (· > ·)) (p : Fin (k + 1) → ℕ) :
    p ∈ firstExitFrontierTuples k parent carrier ↔
      StrictAnti p ∧ (∀ i, p i ∈ carrier) ∧
        FirstExitValidSelection parent [] true (List.ofFn p).dropLast := by
  rw [mem_firstExitFrontierTuples_iff]
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

/-- The literal target, cap, and both real endpoints survive the reindexing. -/
theorem mem_actualPrimeFrontierTuples_iff (k : ℕ)
    (parent : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (p : Fin (k + 1) → ℕ) :
    p ∈ firstExitFrontierTuples k parent (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, p i < cap ∧ Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        FirstExitValidSelection parent [] true (List.ofFn p).dropLast := by
  rw [mem_firstExitFrontierTuples_iff_of_decreasing k parent _
    (roughPrimeUniverse_pairwise_gt N cap w z)]
  simp only [mem_roughPrimeUniverse]

theorem mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap (k : ℕ)
    (parent : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hzcap : z ≤ (cap : ℝ)) (p : Fin (k + 1) → ℕ) :
    p ∈ firstExitFrontierTuples k parent (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        FirstExitValidSelection parent [] true (List.ofFn p).dropLast := by
  rw [mem_firstExitFrontierTuples_iff_of_decreasing k parent _
    (roughPrimeUniverse_pairwise_gt N cap w z)]
  simp only [mem_roughPrimeUniverse_iff_of_cutoff_le_cap hzcap]

/-- The nested arithmetic frontier sum has the same exact tuple sum.
The retained parent is arbitrary and the candidate's own gate is absent. -/
theorem actualPrimeFrontier_candidates_weighted_sum_eq_tuple_sum
    (k : ℕ) (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (f : (Fin (k + 1) → ℕ) → ℝ) :
    ((firstExitDepthFrontier k parent h [] true 1 (roughPrimeUniverse N cap w z)).map
      (fun frontier => ((firstExitNextSelectionCandidates h frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining).map (fun candidate =>
          (candidate.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
            f (primeHistoryTuple (k + 1) candidate.selectedPrefix))).sum)).sum =
      ∑ p ∈ firstExitFrontierTuples k parent (roughPrimeUniverse N cap w z),
        (∏ i, 1 / ((p i : ℝ) - 1)) * f p := by
  rw [← firstExitFrontierCandidates_weighted_sum_eq_tuple_sum k parent h _
    (roughPrimeUniverse_nodup N cap w z)]
  unfold firstExitFrontierCandidates
  generalize firstExitDepthFrontier k parent h [] true 1 (roughPrimeUniverse N cap w z) = states
  induction states with
  | nil => rfl
  | cons state states ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.map_append, List.sum_append, ih]

/-- An arbitrary history-dependent summand is reindexed by the recovered
reverse tuple. This form applies directly to old/new gated residual densities. -/
theorem firstExitFrontierCandidates_history_sum_eq_tuple_sum
    (k : ℕ) (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hc : carrier.Nodup) (F : List ℕ → ℝ) :
    ((firstExitFrontierCandidates k parent h carrier).map (fun candidate =>
      (candidate.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        F candidate.selectedPrefix)).sum =
      ∑ p ∈ firstExitFrontierTuples k parent carrier,
        (∏ i, 1 / ((p i : ℝ) - 1)) * F (List.ofFn p).reverse := by
  rw [← firstExitFrontierCandidates_weighted_sum_eq_tuple_sum k parent h carrier hc
    (fun p => F (List.ofFn p).reverse)]
  congr 1
  apply List.map_congr_left
  intro state hs
  rw [primeHistoryTuple_reverse_ofFn
    (firstExitFrontierCandidates_selected_length k parent h carrier state hs)]

end

end ImbalancedChen
