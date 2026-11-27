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

open scoped BigOperators

open P5NamedFifthPayloadSemantics
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateTree
open P5OldFifthFiveCoordinateBarycentric (childVolume)
open P5OldFifthChildGapIntegral
open P5OldFifthPointwiseQ

/-- false is saved parent0; true is saved parent1. This order is explicit. -/
def namedParent (b : Bool) : FifthWireRow :=
  if b then selectedParent1 else selectedParent0

/-- Exact integer retrieval. The next TWO theorems prove that it does not
round on any of the 64 actual children of either named parent. -/
def sourceChildD (raw : FifthWireRow) (c : ChildIndex) : ℤ :=
  Int.floor (childDQ raw c)

private theorem scaled_min_integral (k x y : ℚ)
    (hx : ∃ z : ℤ, (z : ℚ) = k * x)
    (hy : ∃ z : ℤ, (z : ℚ) = k * y) :
    ∃ z : ℤ, (z : ℚ) = k * min x y := by
  by_cases h : x ≤ y
  · simpa only [min_eq_left h] using hx
  · simpa only [min_eq_right (le_of_not_ge h)] using hy

private theorem scaled_max_integral (k x y : ℚ)
    (hx : ∃ z : ℤ, (z : ℚ) = k * x)
    (hy : ∃ z : ℤ, (z : ℚ) = k * y) :
    ∃ z : ℤ, (z : ℚ) = k * max x y := by
  by_cases h : x ≤ y
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left (le_of_not_ge h)] using hx

private theorem scaled_maxQ_integral {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℚ) (a k : ℚ)
    (ha : ∃ z : ℤ, (z : ℚ) = k * a)
    (hf : ∀ i ∈ S, ∃ z : ℤ, (z : ℚ) = k * f i) :
    ∃ z : ℤ, (z : ℚ) = k * maxQ S f a := by
  have hm : maxQ S f a ∈ valuesQ S f a := Finset.max'_mem _ _
  change maxQ S f a ∈ insert a (S.image f) at hm
  rcases Finset.mem_insert.mp hm with he | hm
  · simpa only [he] using ha
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    simpa only [← he] using hf i hi

private theorem child_plane_integral (pick : Fin 3) (s : ℤ) :
    ∃ z : ℤ, (z : ℚ) = 51200 * planeQ pick ((s : ℚ) / 1600) := by
  fin_cases pick
  · refine ⟨25600 + 16 * s, ?_⟩
    norm_num [planeQ]
    push_cast
    ring
  · refine ⟨45600 - 48 * s, ?_⟩
    norm_num [planeQ]
    push_cast
    ring
  · refine ⟨30600, ?_⟩
    norm_num [planeQ]

/-- Exact integer scaling, independent of which original parent picks win. -/
private theorem child_vertex_gap_integral (raw : FifthWireRow)
    (c : ChildIndex) (w : Word) :
    ∃ z : ℤ, (z : ℚ) =
      51200 * gapQ raw (childVertexQ raw c (wordChoice w)) := by
  let t := childVertexQ raw c (wordChoice w)
  let v : Fin 5 → ℤ := fun i =>
    if wordChoice w i then childRightNumer raw c i else childLeftNumer raw c i
  have ht (i : Fin 5) : t i = (v i : ℚ) / 1600 := by
    dsimp only [t, v, childVertexQ]
    split_ifs <;> rfl
  have hs (S : Finset (Fin 5)) :
      (∑ i ∈ S, t i) = ((∑ i ∈ S, v i : ℤ) : ℚ) / 1600 := by
    simp_rw [ht]
    simp [Finset.sum_div]
  have ho (I : OldMask) :
      (∑ i ∈ I, t i.castSucc) =
        ((∑ i ∈ I, v i.castSucc : ℤ) : ℚ) / 1600 := by
    simp_rw [ht]
    simp [Finset.sum_div]
  let ss : ℤ := ∑ i ∈ maskSlots 5 raw.mask.toNat, v i
  have hnew : ∃ z : ℤ, (z : ℚ) = 51200 *
      min ((1 + ∑ i ∈ maskSlots 5 raw.mask.toNat, t i) / 2)
        (57 / 64 - 3 * (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) / 2) := by
    apply scaled_min_integral
    · refine ⟨25600 + 16 * ss, ?_⟩
      rw [hs]
      dsimp only [ss]
      push_cast
      ring
    · refine ⟨45600 - 48 * ss, ?_⟩
      rw [hs]
      dsimp only [ss]
      push_cast
      ring
  have hold : ∃ z : ℤ, (z : ℚ) = 51200 * oldUpperQ raw t := by
    unfold oldUpperQ
    apply scaled_maxQ_integral
    · refine ⟨30600 - 12 * v 2, ?_⟩
      rw [ht]
      push_cast
      ring
    · intro I _
      rw [ho]
      exact child_plane_integral (sourcePick raw I) _
  have hown : ∃ z : ℤ, (z : ℚ) = 51200 * ((∑ i : Fin 5, t i) + 2 * t 4) := by
    refine ⟨32 * ((∑ i : Fin 5, v i) + 2 * v 4), ?_⟩
    rw [hs, ht]
    push_cast
    ring
  obtain ⟨zn, hn⟩ := hnew
  obtain ⟨zu, hu⟩ := scaled_max_integral _ _ _ hold hown
  refine ⟨zn - zu, ?_⟩
  push_cast
  rw [hn, hu]
  change _ = 51200 * gapQ raw t
  unfold gapQ
  ring

private theorem childDQ_integral (raw : FifthWireRow) (c : ChildIndex) :
    ∃ z : ℤ, (z : ℚ) = childDQ raw c := by
  classical
  choose z hz using child_vertex_gap_integral raw c
  refine ⟨∑ w : Word, z w, ?_⟩
  push_cast
  unfold childDQ
  apply Finset.sum_congr rfl
  intro w _
  simpa only [show (32 * 1600 : ℚ) = 51200 by norm_num] using hz w

private theorem sourceChildD_exact (raw : FifthWireRow) (c : ChildIndex) :
    (sourceChildD raw c : ℚ) = childDQ raw c := by
  obtain ⟨z, hz⟩ := childDQ_integral raw c
  unfold sourceChildD
  rw [← hz]
  simp

/-- Closed finite rational proof, written for later compiler/kernel
execution. It checks every actual 22224 child index, not a sampled list. -/
theorem parent0_all_child_d_exact :
    ∀ c : ChildIndex, (sourceChildD selectedParent0 c : ℚ) =
      childDQ selectedParent0 c := by
  exact sourceChildD_exact selectedParent0

theorem parent1_all_child_d_exact :
    ∀ c : ChildIndex, (sourceChildD selectedParent1 c : ℚ) =
      childDQ selectedParent1 c := by
  exact sourceChildD_exact selectedParent1

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
    (fun a _ c _ hac => (children_pairwise_disjoint (namedParent b))
      (Set.mem_univ a) (Set.mem_univ c) hac)
    (fun c _ => (integrable_gap_on_raw_parent b).mono_set
      (child_subset_parent (namedParent b) (named_grid b) c))]

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
