import ImbalancedChen.ActualThirdOriginalP4ASymmetricSelectorPermutation

/-!
SOURCE_WRITTEN / UNCOMPILED / MAIN OPEN30.
The actual ordinary minorant selector on symmetric below-mu boxes. Paired
scores tie, but source enumeration is not permuted: x precedes y and xz
precedes yz. The unsafe xz/fall possibility is deliberately retained.
-/
namespace ImbalancedChen.P4ASymmetricSelectedBranchClassificationSourceOnly

noncomputable section
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4ASymmetricBranchPermutationSourceOnly
open OriginalThirdP4ASymmetricSelectorPermutationSourceOnly

private theorem selected_tail_of_ne_head {α : Type*} (score : α → ℚ)
    (a p : α) (tail : List α) (hne : p ≠ a)
    (h : firstMax score (a :: tail) = some p) :
    firstMax score tail = some p := by
  cases ht : firstMax score tail with
  | none =>
      have he : a = p := by simpa only [firstMax, ht, Option.some.injEq] using h
      exact False.elim (hne he.symm)
  | some b =>
      by_cases hb : score b ≤ score a
      · have he : a = p := by
          simpa only [firstMax, ht, if_pos hb, Option.some.injEq] using h
        exact False.elim (hne he.symm)
      · have he : b = p := by
          simpa only [firstMax, ht, if_neg hb, Option.some.injEq] using h
        simpa only [he] using ht

private theorem selected_drop_prefix {α : Type*} (score : α → ℚ)
    (prefix tail : List α) (p : α) (hnot : p ∉ prefix)
    (h : firstMax score (prefix ++ tail) = some p) :
    firstMax score tail = some p := by
  revert hnot h
  induction prefix with
  | nil =>
      intro _ h
      simpa only [List.nil_append] using h
  | cons a prefix ih =>
      intro hnot h
      have hn : p ≠ a ∧ p ∉ prefix := by simpa only [List.mem_cons, not_or] using hnot
      exact ih hn.2 (selected_tail_of_ne_head score a p (prefix ++ tail) hn.1 h)

private theorem selected_strictly_beats_head {α : Type*} (score : α → ℚ)
    (a p : α) (tail : List α) (hne : p ≠ a)
    (h : firstMax score (a :: tail) = some p) : score a < score p := by
  have ht := selected_tail_of_ne_head score a p tail hne h
  have hn : ¬ score p ≤ score a := by
    intro hp
    have he : a = p := by
      simpa only [firstMax, ht, if_pos hp, Option.some.injEq] using h
    exact hne he.symm
  exact lt_of_not_ge hn

/-- Actual strict first-tie rule: a later equal-score candidate cannot replace
an eligible earlier head, even when other candidates intervene. -/
theorem firstMax_ne_later_tied {α : Type*} (score : α → ℚ)
    (prefix tail : List α) (early late : α) (hnot : late ∉ prefix)
    (hne : late ≠ early) (htie : score early = score late) :
    firstMax score (prefix ++ early :: tail) ≠ some late := by
  intro h
  have hs := selected_drop_prefix score prefix (early :: tail) late hnot h
  have hlt := selected_strictly_beats_head score early late tail hne hs
  rw [htie] at hlt
  exact (lt_irrefl _ hlt)

private theorem sourcePair_singleton_of_branch
    (lo hi : Fin 3 → ℤ) (D : ℤ) (s : TentSum) (k : TentSide)
    (h : branchTest lo hi D s k) : sourcePair lo hi D s = [.tent s k] := by
  cases k with
  | rise => exact if_pos h
  | fall => simp only [sourcePair, if_neg h.1, if_pos h.2]

private theorem tent_not_mem_other_sourcePair
    (lo hi : Fin 3 → ℤ) (D : ℤ) (s u : TentSum) (k : TentSide) (hne : s ≠ u) :
    Candidate.tent s k ∉ sourcePair lo hi D u := by
  unfold sourcePair
  split_ifs <;> simp_all

private theorem originalMinorant_ne_tied_after_prefix
    (lo hi : Fin 3 → ℤ) (D T : ℤ) (prefix tail : List Candidate)
    (early late : Candidate)
    (hraw : sourceRaw lo hi D = prefix ++ early :: tail)
    (hearly : rootTest lo hi D T early)
    (hnot : late ∉ prefix) (hne : late ≠ early)
    (htie : sourceScore lo hi D early = sourceScore lo hi D late) :
    originalMinorant lo hi D T ≠ some late := by
  classical
  have hc : sourceCandidates lo hi D T =
      prefix.filter (fun p => decide (rootTest lo hi D T p)) ++ early ::
        tail.filter (fun p => decide (rootTest lo hi D T p)) := by
    rw [sourceCandidates, hraw]
    simp only [List.filter_append, List.filter_cons, decide_eq_true hearly, if_true]
  rw [originalMinorant, hc]
  apply firstMax_ne_later_tied _ _ _ early late _ hne htie
  intro h
  exact hnot (List.mem_filter.mp h).1

/-- The exact original rational score ties and x-before-y list order exclude
y for either side. No ordering hypothesis about selected labels is assumed. -/
theorem symmetric_selector_ne_y (x0 x1 z0 z1 D T : ℤ) (k : TentSide) :
    originalMinorant ![x0,x0,z0] ![x1,x1,z1] D T ≠ some (.tent .y k) := by
  intro hselected
  have hy := (firstMax_mem_max _ _ _ hselected).1
  have hx : Candidate.tent .x k ∈ sourceCandidates ![x0,x0,z0] ![x1,x1,z1] D T := by
    apply (symmetric_literal_tent_mem_swap_iff x0 x1 z0 z1 D T .x k).mp
    simpa only [swapSum] using hy
  have hg := (tent_mem_candidates_iff _ _ D T .x k).mp hx
  have hp := sourcePair_singleton_of_branch _ _ D .x k hg.1
  have hraw : sourceRaw ![x0,x0,z0] ![x1,x1,z1] D = [.base] ++ .tent .x k ::
      (sourcePair ![x0,x0,z0] ![x1,x1,z1] D .y ++
       sourcePair ![x0,x0,z0] ![x1,x1,z1] D .xy ++
       sourcePair ![x0,x0,z0] ![x1,x1,z1] D .xz ++
       sourcePair ![x0,x0,z0] ![x1,x1,z1] D .yz ++
       sourcePair ![x0,x0,z0] ![x1,x1,z1] D .xyz) := by
    simp [sourceRaw, sourceSums, hp, List.append_assoc]
  exact originalMinorant_ne_tied_after_prefix _ _ D T _ _ (.tent .x k) (.tent .y k)
    hraw hg.2 (by simp) (by intro h; cases h)
    (symmetric_literal_paired_ties x0 x1 z0 z1 D k).1 hselected

/-- xz precedes yz and has identical original filters and exact rational
score. This excludes yz/rise AND yz/fall while preserving xz/fall. -/
theorem symmetric_selector_ne_yz (x0 x1 z0 z1 D T : ℤ) (k : TentSide) :
    originalMinorant ![x0,x0,z0] ![x1,x1,z1] D T ≠ some (.tent .yz k) := by
  intro hselected
  have hyz := (firstMax_mem_max _ _ _ hselected).1
  have hxz : Candidate.tent .xz k ∈ sourceCandidates ![x0,x0,z0] ![x1,x1,z1] D T := by
    apply (symmetric_literal_tent_mem_swap_iff x0 x1 z0 z1 D T .xz k).mp
    simpa only [swapSum] using hyz
  have hg := (tent_mem_candidates_iff _ _ D T .xz k).mp hxz
  have hp := sourcePair_singleton_of_branch _ _ D .xz k hg.1
  let prefix := Candidate.base ::
    (sourcePair ![x0,x0,z0] ![x1,x1,z1] D .x ++
     sourcePair ![x0,x0,z0] ![x1,x1,z1] D .y ++
     sourcePair ![x0,x0,z0] ![x1,x1,z1] D .xy)
  have hraw : sourceRaw ![x0,x0,z0] ![x1,x1,z1] D = prefix ++ .tent .xz k ::
      (sourcePair ![x0,x0,z0] ![x1,x1,z1] D .yz ++
       sourcePair ![x0,x0,z0] ![x1,x1,z1] D .xyz) := by
    simp [sourceRaw, sourceSums, hp, prefix, List.append_assoc]
  have hn : Candidate.tent .yz k ∉ prefix := by
    intro h
    simp only [prefix, List.mem_cons, List.mem_append, or_assoc] at h
    rcases h with h | h | h | h
    · cases h
    · exact tent_not_mem_other_sourcePair _ _ D .yz .x k (by intro he; cases he) h
    · exact tent_not_mem_other_sourcePair _ _ D .yz .y k (by intro he; cases he) h
    · exact tent_not_mem_other_sourcePair _ _ D .yz .xy k (by intro he; cases he) h
  exact originalMinorant_ne_tied_after_prefix _ _ D T _ _ (.tent .xz k) (.tent .yz k)
    hraw hg.2 hn (by intro h; cases h)
    (symmetric_literal_paired_ties x0 x1 z0 z1 D k).2 hselected

/-- Exact below-mu integer inequality. Equality still reaches rise first. -/
theorem symmetric_selector_ne_primary_fall (x0 x1 z0 z1 D T : ℤ)
    (hmu : 256*x1 ≤ 50*D) (s : TentSum) (hs : s = .x ∨ s = .y) :
    originalMinorant ![x0,x0,z0] ![x1,x1,z1] D T ≠ some (.tent s .fall) := by
  intro hselected
  have hg := (selected_tent_guards _ _ D T s .fall hselected).1.1
  rcases hs with rfl | rfl <;>
    simp [deltaNumerator, rawSum, literalTentX, literalTentY, literalTentZ] at hg <;>
    omega

/-- The real whole-box minimum test gives the same exact exclusion. -/
theorem symmetric_primary_sourceActive_not_fall (a b c d : ℝ)
    (hmu : b ≤ VariableEnvelope.mu) :
    ¬ sourceActive .x .fall ![a,a,c] ![b,b,d] ∧
      ¬ sourceActive .y .fall ![a,a,c] ![b,b,d] := by
  have hs := symmetric_primary_sides_below a b c d hmu
  constructor
  · intro h
    have hf := (sourceSide_eq_some_iff .x .fall _ _).mpr h
    rw [hs.1] at hf
    cases hf
  · intro h
    have hf := (sourceSide_eq_some_iff .y .fall _ _).mpr h
    rw [hs.2] at hf
    cases hf

/-- Balanced xy/xyz retain both sides; xz/fall is an explicit remaining
possibility. This is a necessary classification, not a feasibility claim. -/
def remainingCandidate (p : Candidate) : Prop :=
  p = .base ∨ ∃ s k, p = .tent s k ∧
    ((s = .xy ∨ s = .xyz) ∨ (s = .x ∧ k = .rise) ∨ s = .xz)

theorem symmetric_below_mu_selected_classification
    (x0 x1 z0 z1 D T : ℤ) (hmu : 256*x1 ≤ 50*D) (p : Candidate)
    (hselected : originalMinorant ![x0,x0,z0] ![x1,x1,z1] D T = some p) :
    remainingCandidate p := by
  cases p with
  | base => exact Or.inl rfl
  | tent s k =>
      cases s with
      | x =>
          cases k with
          | rise => exact Or.inr ⟨.x, .rise, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          | fall => exact False.elim
              (symmetric_selector_ne_primary_fall x0 x1 z0 z1 D T hmu .x (Or.inl rfl) hselected)
      | y => exact False.elim (symmetric_selector_ne_y x0 x1 z0 z1 D T k hselected)
      | xy => exact Or.inr ⟨.xy, k, rfl, Or.inl (Or.inl rfl)⟩
      | xz => exact Or.inr ⟨.xz, k, rfl, Or.inr (Or.inr rfl)⟩
      | yz => exact False.elim (symmetric_selector_ne_yz x0 x1 z0 z1 D T k hselected)
      | xyz => exact Or.inr ⟨.xyz, k, rfl, Or.inl (Or.inr rfl)⟩

/-- Public physical-coordinate entry point, retaining b_x<=mu literally. -/
theorem symmetric_below_mu_real_selected_classification
    (x0 x1 z0 z1 D T : ℤ) (hD : 0 < D) (b : ℝ)
    (hbind : b = (x1 : ℝ) / (D : ℝ)) (hmu : b ≤ VariableEnvelope.mu)
    (p : Candidate)
    (hselected : originalMinorant ![x0,x0,z0] ![x1,x1,z1] D T = some p) :
    remainingCandidate p := by
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hx : (x1 : ℝ) ≤ VariableEnvelope.mu * (D : ℝ) := by
    apply (div_le_iff₀ hDr).mp
    simpa only [← hbind] using hmu
  have hh : 256*(x1 : ℝ) ≤ 50*(D : ℝ) := by
    dsimp [VariableEnvelope.mu] at hx
    linarith
  have hi : 256*x1 ≤ 50*D := by exact_mod_cast hh
  exact symmetric_below_mu_selected_classification x0 x1 z0 z1 D T hi p hselected

end
end ImbalancedChen.P4ASymmetricSelectedBranchClassificationSourceOnly
