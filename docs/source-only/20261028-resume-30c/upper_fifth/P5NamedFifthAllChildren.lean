import ImbalancedChen.P5NamedFifthPayloadSemantics

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.

All 64 children of each of the two literal parents use the SAME fixed
parent picks. The exact rational childDQ has integer values on this whole
finite family. sourceChildD is an integer retrieval, whose equality with
childDQ is PROVED for all actual children; no truncation error or assumed
saved-d equality is introduced.

The two parent boxes split into 128 genuine half-open children with unique
ownership, before and after clipping by the same original fullCell. The
original gap and literal signed owner integrals are exactly additive. No
Q80 floor, numerical total, full adopted J5 or current K is claimed.
-/

namespace ImbalancedChen.P5NamedFifthAllChildren

open P5NamedFifthPayloadSemantics
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateTree
open P5OldFifthChildGapIntegral
open P5OldFifthPointwiseQ

/-- false is saved parent0; true is saved parent1. This order is explicit. -/
def namedParent (b : Bool) : FifthWireRow :=
  if b then selectedParent1 else selectedParent0

/-- Exact integer retrieval. The next TWO theorems prove that it does not
round on any of the 64 actual children of either named parent. -/
def sourceChildD (raw : FifthWireRow) (c : ChildIndex) : ℤ :=
  Int.floor (childDQ raw c)

/-- Closed finite rational proof, written for later compiler/kernel
execution. It checks every actual 22224 child index, not a sampled list. -/
theorem parent0_all_child_d_exact :
    ∀ c : ChildIndex, (sourceChildD selectedParent0 c : ℚ) =
      childDQ selectedParent0 c := by
  decide

theorem parent1_all_child_d_exact :
    ∀ c : ChildIndex, (sourceChildD selectedParent1 c : ℚ) =
      childDQ selectedParent1 c := by
  decide

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1FifthNamedParentActualIntegral
open P1FifthUnitBoxGainDecomposition P1FifthUnitBoxLiteralGainLower

/-- Uniform hd for ALL 128 actual parent/child pairs. It is not an input. -/
theorem namedChild_hd (b : Bool) (c : ChildIndex) :
    (sourceChildD (namedParent b) c : ℝ) =
      vertexD (sourcePicks (namedParent b)) (namedParent b) c := by
  have hq : (sourceChildD (namedParent b) c : ℚ) = childDQ (namedParent b) c := by
    cases b
    · exact parent0_all_child_d_exact c
    · exact parent1_all_child_d_exact c
  have hr : (sourceChildD (namedParent b) c : ℝ) =
      (childDQ (namedParent b) c : ℝ) := by exact_mod_cast hq
  exact hr.trans (cast_childDQ (namedParent b) c)

theorem named_grid (b : Bool) : (namedParent b).grid = 400 := by
  cases b <;> rfl

theorem named_positive_indices (b : Bool) : ∀ i, 1 ≤ (namedParent b).lo i := by
  intro i
  cases b <;> fin_cases i <;> norm_num [namedParent, selectedParent0, selectedParent1]

/-- One uniform original A/B range for every child. Child-specific two-plane
maxima may improve it later; this proved range already suffices for Jensen. -/
theorem named_ratio_range (b : Bool) :
    (2 : ℝ) < savedRatio (namedParent b) ∧ savedRatio (namedParent b) ≤ 4 := by
  cases b
  · change (2 : ℝ) < savedRatio selectedParent0 ∧ savedRatio selectedParent0 ≤ 4
    rw [parent0_ratio]
    norm_num
  · change (2 : ℝ) < savedRatio selectedParent1 ∧ savedRatio selectedParent1 ≤ 4
    rw [parent1_ratio]
    norm_num

theorem named_childLeft_pos (b : Bool) (c : ChildIndex) (i : Fin 5) :
    0 < childLeft (namedParent b) c i := by
  cases b
  · exact parent0_childLeft_pos c i
  · exact parent1_childLeft_pos c i

theorem named_child_new_ratio (b : Bool) (c : ChildIndex) (t : Fin 5 → ℝ)
    (ht : t ∈ Icc (childLeft (namedParent b) c) (childRight (namedParent b) c)) :
    residual (rawCandidate 0 (namedParent b) t) t ≤ savedRatio (namedParent b) := by
  cases b
  · exact parent0_child_new_ratio c t ht
  · exact parent1_child_new_ratio c t ht

/-- Every true closure vertex has positive fifth coordinate and obeys the
same actual residual range. No midpoint or surrogate point is substituted. -/
theorem named_vertex_ratio (b : Bool) (c : ChildIndex) (ε : VertexChoice) :
    residual (rawCandidate 0 (namedParent b) (vertexPoint (namedParent b) c ε))
      (vertexPoint (namedParent b) c ε) ≤ savedRatio (namedParent b) := by
  apply named_child_new_ratio b c
  have hv := vertexPoint_mem_closed (namedParent b) c ε
  exact ⟨fun i => (hv i).1, fun i => (hv i).2⟩

abbrev NamedChild := Bool × ChildIndex

def namedChildBox (z : NamedChild) : Set (Fin 5 → ℝ) :=
  childBox (namedParent z.1) z.2

theorem namedChild_card : Fintype.card NamedChild = 128 := by
  rw [Fintype.card_prod, childIndex_card]
  norm_num

/-- Exact half-open coverage of the two original raw parents. -/
theorem two_parents_eq_union_128_children :
    selectedParent0.originalBox ∪ selectedParent1.originalBox =
      ⋃ z ∈ (Finset.univ : Finset NamedChild), namedChildBox z := by
  ext t
  constructor
  · intro ht
    rcases ht with h0 | h1
    · obtain ⟨c, hc⟩ := parent_covered_by_child selectedParent0 rfl t h0
      exact mem_iUnion₂.mpr ⟨(false, c), Finset.mem_univ _, hc⟩
    · obtain ⟨c, hc⟩ := parent_covered_by_child selectedParent1 rfl t h1
      exact mem_iUnion₂.mpr ⟨(true, c), Finset.mem_univ _, hc⟩
  · intro ht
    obtain ⟨⟨b, c⟩, _, hc⟩ := mem_iUnion₂.mp ht
    cases b
    · exact Or.inl (child_subset_parent selectedParent0 rfl c hc)
    · exact Or.inr (child_subset_parent selectedParent1 rfl c hc)

/-- No boundary double count within a parent or between the literal parents. -/
theorem named_children_pairwise_disjoint :
    Set.PairwiseDisjoint (Set.univ : Set NamedChild) namedChildBox := by
  intro a _ b _ hne
  rcases a with ⟨ia, ca⟩
  rcases b with ⟨ib, cb⟩
  cases ia <;> cases ib
  · apply (children_pairwise_disjoint selectedParent0) (Set.mem_univ _) (Set.mem_univ _)
    intro h
    exact hne (by cases h; rfl)
  · exact named_raw_boxes_disjoint.mono
      (child_subset_parent selectedParent0 rfl ca)
      (child_subset_parent selectedParent1 rfl cb)
  · exact named_raw_boxes_disjoint.symm.mono
      (child_subset_parent selectedParent1 rfl ca)
      (child_subset_parent selectedParent0 rfl cb)
  · apply (children_pairwise_disjoint selectedParent1) (Set.mem_univ _) (Set.mem_univ _)
    intro h
    exact hne (by cases h; rfl)

/-- The actual original owner clipping commutes with the WHOLE 64-child
partition. Raw local bounds cannot remove this clipping. -/
theorem named_raw_owner_eq_union_children (b : Bool)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) :
    rawOwnerDomain (namedParent b) e chi m omega j =
      ⋃ c ∈ (Finset.univ : Finset ChildIndex),
        childOwnerDomain (namedParent b) c e chi m omega j :=
  rawOwnerDomain_eq_union_children (namedParent b) (named_grid b) e chi m omega j

/-- Signed original literal owner kernel, not an unbuffered positive-part
floor. Existing source integrability supplies exact finite additivity. -/
theorem named_literal_owner_integral_eq_sum_64 (b : Bool)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) :
    literalRawOwnerIntegral (namedParent b) e chi m omega j =
      ∑ c : ChildIndex,
        ∫ t in childOwnerDomain (namedParent b) c e chi m omega j,
          literalRawKernel (e : ℝ) (namedParent b) t :=
  literalRawOwnerIntegral_eq_sum_64_children (namedParent b) (named_grid b)
    (named_positive_indices b) e chi m omega j

/-- All-child d semantics yields a real gap-integral lower bound with its
signed d retained. The manuscript later assigns zero for nonpositive d
when passing to positive kernels; that is a different, subsequent step. -/
theorem named_child_gap_integral (b : Bool) (c : ChildIndex) :
    childVolume (namedParent b) c * (sourceChildD (namedParent b) c : ℝ) /
        (1024 * 1600) ≤
      ∫ t in childBox (namedParent b) c,
        frozenGap (sourcePicks (namedParent b)) (namedParent b) t :=
  integral_frozenGap_ge_saved_integer_d (sourcePicks (namedParent b))
    (namedParent b) c (sourceChildD (namedParent b) c) (namedChild_hd b c)

private theorem integrable_gap_on_raw_parent (b : Bool) :
    IntegrableOn (frozenGap (sourcePicks (namedParent b)) (namedParent b))
      (namedParent b).originalBox := by
  have hi : IntegrableOn
      (frozenGap (sourcePicks (namedParent b)) (namedParent b))
      (Icc (fun i => ((namedParent b).lower i : ℝ))
        (fun i => ((namedParent b).upper i : ℝ))) :=
    (continuous_frozenGap (sourcePicks (namedParent b)) (namedParent b)).integrableOn_Icc
  apply hi.mono_set
  intro t ht
  exact ⟨fun i => (ht i).1, fun i => (ht i).2.le⟩

/-- Full frozen-gap integral equals the sum over ALL true children. -/
theorem named_gap_integral_eq_sum_64 (b : Bool) :
    (∫ t in (namedParent b).originalBox,
      frozenGap (sourcePicks (namedParent b)) (namedParent b) t) =
      ∑ c : ChildIndex, ∫ t in childBox (namedParent b) c,
        frozenGap (sourcePicks (namedParent b)) (namedParent b) t := by
  rw [parent_eq_union_children (namedParent b) (named_grid b)]
  rw [integral_biUnion_finset (Finset.univ : Finset ChildIndex)
    (fun c _ => childBox_measurable (namedParent b) c)
    (children_pairwise_disjoint (namedParent b))
    (fun c _ => (integrable_gap_on_raw_parent b).mono_set
      (child_subset_parent (namedParent b) (named_grid b) c))]
  simp

/-- A symbolic full-parent finite sum, without any numerical total. -/
theorem named_all_child_d_gap_bound (b : Bool) :
    (∑ c : ChildIndex,
      childVolume (namedParent b) c * (sourceChildD (namedParent b) c : ℝ) /
        (1024 * 1600)) ≤
      ∫ t in (namedParent b).originalBox,
        frozenGap (sourcePicks (namedParent b)) (namedParent b) t := by
  rw [named_gap_integral_eq_sum_64]
  exact Finset.sum_le_sum (fun c _ => named_child_gap_integral b c)

end
end ImbalancedChen.P5NamedFifthAllChildren
