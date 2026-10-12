import ImbalancedChen.FirstExitOwnCubeSplice
import ImbalancedChen.ActualFrozenFrontierDensity

/-!
# Geometry of every next selection at an actual prime frontier

The next-selection enumeration scans all possible choices, independently of
their eventual admission. Its exact skipped prefix and unprocessed suffix
give the actual cutoff, sign and prime mass even for a branch rejected by
the old policy. The common frontier may have rank zero.
-/

namespace ImbalancedChen

noncomputable section

open scoped List

/-- Literal decomposition of the enumeration into skipped labels, the next
selected label, and its untouched suffix. No policy test occurs here. -/
theorem mem_firstExitNextSelectionCandidates_iff
    {α : Type*} (h : α → ℝ) (pre remaining : List α)
    (positive : Bool) (mass : ℝ) (state : FirstExitDepthState α) :
    state ∈ firstExitNextSelectionCandidates h pre positive mass remaining ↔
      ∃ before q after, remaining = before ++ q :: after ∧
        state = {
          selectedPrefix := q :: pre
          positive := !positive
          mass := mass * h q
          remaining := after } := by
  induction remaining with
  | nil => simp [firstExitNextSelectionCandidates]
  | cons p ps ih =>
      constructor
      · intro hs
        rcases List.mem_cons.mp hs with hs | hs
        · exact ⟨[], p, ps, rfl, hs⟩
        · obtain ⟨before, q, after, heq, hstate⟩ := ih.mp hs
          exact ⟨p :: before, q, after, by simp only [List.cons_append, heq], hstate⟩
      · rintro ⟨before, q, after, heq, hstate⟩
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, rfl⟩
            exact List.mem_cons.mpr (Or.inl hstate)
        | cons r before =>
            simp only [List.cons_append, List.cons.injEq] at heq
            exact List.mem_cons.mpr (Or.inr (ih.mpr
              ⟨before, q, after, heq.2, hstate⟩))

/-- The actual root frontier always leaves a suffix of the original
carrier. Rank zero has the empty skipped prefix. -/
theorem firstExitDepthFrontier_remaining_suffix
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1 carrier) :
    ∃ before, carrier = before ++ state.remaining := by
  by_cases hk : k = 0
  · rw [hk, firstExitDepthFrontier_of_rank_le_length 0 parent h [] carrier true 1
      (by simp), List.mem_singleton] at hstate
    rw [hstate]
    exact ⟨[], rfl⟩
  · obtain ⟨before, q, tail, hrem, _hsel⟩ :=
      firstExitDepthFrontier_exists_last_selection k parent h [] carrier true 1
        (by simp; omega) state hstate
    exact ⟨before ++ [q], by simpa only [List.append_assoc, List.singleton_append] using hrem⟩

/-- The entire geometry of an actual candidate is derived from the common
frontier and its enumeration. In particular its sign is not required to
pass any new or old admission predicate. -/
theorem actualPrimeNextSelection_geometry
    (k : ℕ) (parent : Bool → List ℕ → Bool) (N cap : ℕ) (z : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining) :
    candidate.selectedPrefix.length = k + 1 ∧
      candidate.selectedPrefix.Pairwise (· < ·) ∧
      (0 : ℝ) < candidate.selectedPrefix.prod ∧
      (∀ p ∈ candidate.selectedPrefix,
        (candidate.selectedPrefix.headD 0 : ℝ) ≤ (p : ℝ)) ∧
      candidate.remaining = roughPrimeUniverse N cap 0 (candidate.selectedPrefix.headD 0 : ℝ) ∧
      candidate.positive = evenListLength candidate.selectedPrefix ∧
      candidate.mass = (candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod ∧
      (∀ p ∈ candidate.selectedPrefix, p.Prime) := by
  obtain ⟨before, q, after, hrem, rfl⟩ :=
    (mem_firstExitNextSelectionCandidates_iff _ _ _ _ _ candidate).mp hcandidate
  have hqmem : q ∈ frontier.remaining := by simp [hrem]
  have hlen := firstExitDepthFrontier_selected_length k parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1
    (by simp) frontier hfrontier
  have hsub : frontier.selectedPrefix.reverse ++ frontier.remaining <+
      roughPrimeUniverse N cap 0 z := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z)
      true 1 frontier hfrontier
  have hqfull : q ∈ roughPrimeUniverse N cap 0 z :=
    hsub.subset (List.mem_append.mpr (Or.inr hqmem))
  have hprime : ∀ p ∈ q :: frontier.selectedPrefix, p.Prime := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact mem_roughPrimeUniverse_prime hqfull
    · exact mem_roughPrimeUniverse_prime
        (hsub.subset (List.mem_append.mpr (Or.inl (List.mem_reverse.mpr hp))))
  have hpair := List.pairwise_append.mp
    ((roughPrimeUniverse_pairwise_gt N cap 0 z).sublist hsub)
  have hsort : (q :: frontier.selectedPrefix).Pairwise (· < ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, ?_⟩
    · intro p hp
      exact hpair.2.2 p (List.mem_reverse.mpr hp) q hqmem
    · simpa only [List.pairwise_reverse] using hpair.1
  have hP : (0 : ℝ) < (q :: frontier.selectedPrefix).prod := by
    exact_mod_cast List.prod_pos (fun p hp => (hprime p hp).pos)
  have hcut : ∀ p ∈ q :: frontier.selectedPrefix, (q : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_rfl
    · exact_mod_cast ((List.pairwise_cons.mp hsort).1 p hp).le
  obtain ⟨past, hpast⟩ := firstExitDepthFrontier_remaining_suffix k parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) frontier hfrontier
  have hfull : roughPrimeUniverse N cap 0 z = (past ++ before) ++ q :: after := by
    rw [hpast, hrem, List.append_assoc]
  have hafter : after = roughPrimeUniverse N cap 0 (q : ℝ) := by
    calc
      after = (roughPrimeUniverse N cap 0 z).filter (fun p => p < q) := by
        rw [hfull]
        exact decreasingList_suffix_eq_filter_lt (past ++ before) after q
          (hfull ▸ roughPrimeUniverse_pairwise_gt N cap 0 z)
      _ = _ := roughPrimeUniverse_filter_lt_eq N cap 0 z q
        (mem_roughPrimeUniverse_upper hqfull).le
  refine ⟨?_, hsort, hP, hcut, hafter, ?_, ?_, hprime⟩
  · simpa only [List.length_cons] using congrArg (· + 1) hlen
  · change (!frontier.positive) = evenListLength (q :: frontier.selectedPrefix)
    rw [mem_firstExitDepthFrontier_positive_eq_evenListLength k parent _ _ frontier hfrontier]
    rfl
  · change frontier.mass * (1 / ((q : ℝ) - 1)) = _
    rw [mem_firstExitDepthFrontier_mass_eq_selected_prod k parent _ _ frontier hfrontier]
    simp only [List.map_cons, List.prod_cons, mul_comm]

/-- A rank-four candidate is an actual five-prime history. The last prime
is prime and strictly greater than one, including rejected fifth branches. -/
theorem actualPrimeNextSelection_rank_four_exists
    (parent : Bool → List ℕ → Bool) (N cap : ℕ) (z : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier 4 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining) :
    ∃ p1 p2 p3 p4 p5 : ℕ,
      frontier.selectedPrefix = [p4, p3, p2, p1] ∧
      candidate.selectedPrefix = [p5, p4, p3, p2, p1] ∧
      p5 < p4 ∧ p4 < p3 ∧ p3 < p2 ∧ p2 < p1 ∧
      p5.Prime ∧ 1 < p5 ∧ candidate.positive = false ∧
      candidate.mass = ([p5, p4, p3, p2, p1].map
        (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod ∧
      candidate.remaining = roughPrimeUniverse N cap 0 (p5 : ℝ) := by
  obtain ⟨_hlen, hsort, _hP, _hcut, hremaining, hsign, hmass, hprime⟩ :=
    actualPrimeNextSelection_geometry 4 parent N cap z frontier hfrontier candidate hcandidate
  obtain ⟨before, p5, after, _hrem, hc⟩ :=
    (mem_firstExitNextSelectionCandidates_iff _ _ _ _ _ candidate).mp hcandidate
  have hlen := firstExitDepthFrontier_selected_length 4 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1
    (by simp) frontier hfrontier
  obtain ⟨p4, t3, ht4, hl3⟩ := List.length_eq_succ_iff.mp hlen
  obtain ⟨p3, t2, ht3, hl2⟩ := List.length_eq_succ_iff.mp hl3
  obtain ⟨p2, t1, ht2, hl1⟩ := List.length_eq_succ_iff.mp hl2
  obtain ⟨p1, t0, ht1, hl0⟩ := List.length_eq_succ_iff.mp hl1
  have ht0 : t0 = [] := List.length_eq_zero_iff.mp hl0
  have hf : frontier.selectedPrefix = [p4, p3, p2, p1] := by
    rw [← ht4, ← ht3, ← ht2, ← ht1, ht0]
  have hs : candidate.selectedPrefix = [p5, p4, p3, p2, p1] := by simp [hc, hf]
  have hp5 : p5.Prime := hprime p5 (by simp [hs])
  rw [hs] at hsort hremaining hsign hmass
  have hord : p5 < p4 ∧ p4 < p3 ∧ p3 < p2 ∧ p2 < p1 := by
    simp only [List.pairwise_cons] at hsort
    exact ⟨hsort.1 p4 (by simp), hsort.2.1 p3 (by simp),
      hsort.2.2.1 p2 (by simp), hsort.2.2.2.1 p1 (by simp)⟩
  exact ⟨p1, p2, p3, p4, p5, hf, hs, hord.1, hord.2.1, hord.2.2.1,
    hord.2.2.2, hp5, hp5.one_lt, by simpa [evenListLength] using hsign,
    hmass, by simpa only [List.headD_cons] using hremaining⟩

end

end ImbalancedChen
