import ImbalancedChen.P5OriginalGenericWireFloorReceiver

/-! Original ordered pair fold: attained vertex maxima and the actual chosen
plane upper bound. The source list, strict comparisons and unreduced pairs
are unchanged. No saved ratio bound, SourceChildFacts or integral is assumed. -/
namespace ImbalancedChen.P5OriginalABFoldGeometry

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthRawBoxSelectorEquivalence
open P5OriginalChildIntegerWireBinding P5OriginalGenericWireFloorReceiver
open P5ArbitraryMaskChildVertexRatio P5NamedFifthPayloadSemantics
open P5NamedFifthAllChildren P5OldFifthExact64ChildTiling
open P5OldFifthFiveCoordinateTree P5OldFifthChildGapIntegral
open P5OldFifthPointwiseQ P5OldFifthFrozenUpperSurrogate
open P5OldFifthOneCoordinateVertexChord P5ChildSelectedOwnerJensenReserve

private def pairQ (p : RatioPair) : ℚ := (p.num : ℚ) / (p.den : ℚ)

private theorem update_facts (p q : RatioPair) (hp : 0 < p.den) (hq : 0 < q.den) :
    0 < (updatePair p q).den ∧
    (updatePair p q = p ∨ updatePair p q = q) ∧
    pairQ p ≤ pairQ (updatePair p q) ∧ pairQ q ≤ pairQ (updatePair p q) := by
  have hpq : (0 : ℚ) < (p.den : ℚ) := by exact_mod_cast hp
  have hqq : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast hq
  by_cases h : p.num * q.den < q.num * p.den
  · simp only [updatePair, if_pos h]
    refine ⟨hq, Or.inr trivial, ?_, le_rfl⟩
    apply (div_le_div_iff₀ hpq hqq).mpr
    exact_mod_cast h.le
  · simp only [updatePair, if_neg h]
    refine ⟨hp, Or.inl trivial, le_rfl, ?_⟩
    apply (div_le_div_iff₀ hqq hpq).mpr
    exact_mod_cast le_of_not_gt h

private theorem fold_facts {α : Type*} (P : α → RatioPair) (ws : List α)
    (first : RatioPair) (hfirst : 0 < first.den)
    (hws : ∀ w ∈ ws, 0 < (P w).den) :
    let res := ws.foldl (fun old w => updatePair old (P w)) first
    0 < res.den ∧ (res = first ∨ ∃ w ∈ ws, res = P w) ∧
    pairQ first ≤ pairQ res ∧ ∀ w ∈ ws, pairQ (P w) ≤ pairQ res := by
  induction ws generalizing first with
  | nil =>
      exact ⟨hfirst, Or.inl rfl, le_rfl, by intro w hw; cases hw⟩
  | cons a ws ih =>
      have ha := hws a (List.mem_cons_self ..)
      have hu := update_facts first (P a) hfirst ha
      have hr := ih (updatePair first (P a)) hu.1
        (fun w hw => hws w (List.mem_cons_of_mem a hw))
      refine ⟨hr.1, ?_, hu.2.2.1.trans hr.2.2.1, ?_⟩
      · rcases hr.2.1 with he | ⟨w, hw, he⟩
        · rcases hu.2.1 with hp | hq
          · exact Or.inl (he.trans hp)
          · exact Or.inr ⟨a, List.mem_cons_self .., he.trans hq⟩
        · exact Or.inr ⟨w, List.mem_cons_of_mem a hw, he⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hu.2.2.2.trans hr.2.2.1
        · exact hr.2.2.2 w hw

private theorem all_words_in_source (w : Word) : w ∈ producerBits := by
  rcases w with ⟨a, b, c, d, e⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private theorem vertexNumer_pos (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (w : Word) (i : Fin 5) :
    0 < vertexNumer raw c w i := by
  have hp : 0 < raw.lo i := lt_of_lt_of_le (by norm_num) (hpositive i)
  have hw : 0 < wireWidth i := by fin_cases i <;> decide
  have hc : (0 : ℤ) ≤ ((c i).val : ℤ) := Int.natCast_nonneg _
  unfold vertexNumer wireLo
  split_ifs <;> nlinarith

private theorem plane_den_pos (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (side : Bool) (w : Word) :
    0 < (planeRatioPair raw c side w).den :=
  mul_pos (by norm_num) (vertexNumer_pos raw c hpositive w 4)

/-- The original fold returns an ORIGINAL unreduced vertex pair and bounds
every original vertex ratio, for arbitrary source rows with positive indices. -/
theorem originalPlaneMax_facts (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (side : Bool) :
    0 < (originalPlaneMax raw c side).den ∧
    (∃ w : Word, originalPlaneMax raw c side = planeRatioPair raw c side w) ∧
    ∀ w : Word,
      ((planeRatioPair raw c side w).num : ℚ) / ((planeRatioPair raw c side w).den : ℚ) ≤
        ((originalPlaneMax raw c side).num : ℚ) / ((originalPlaneMax raw c side).den : ℚ) := by
  let z : Word := (false, false, false, false, false)
  have hf := fold_facts (planeRatioPair raw c side) producerBits.tail
    (planeRatioPair raw c side z) (plane_den_pos raw c hpositive side z)
    (fun w _ => plane_den_pos raw c hpositive side w)
  refine ⟨hf.1, ?_, ?_⟩
  · rcases hf.2.1 with h | ⟨w, _, h⟩
    · exact ⟨z, h⟩
    · exact ⟨w, h⟩
  · intro w
    have hw := all_words_in_source w
    have he : producerBits = z :: producerBits.tail := rfl
    rw [he] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hf.2.2.1
    · exact hf.2.2.2 w hw

/-- Source strict C<A comparison chooses C; ties keep the A pair exactly. -/
theorem originalAB_eq_chosen_plane (raw : FifthWireRow) (c : ChildIndex) :
    originalAB raw c = originalPlaneMax raw c (originalChosenSide raw c) := by
  dsimp only [originalAB, originalChosenSide]
  split_ifs with h <;> simp [h]

theorem originalAB_den_pos (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) :
    0 < (originalFields raw c).B := by
  change 0 < (originalAB raw c).den
  rw [originalAB_eq_chosen_plane]
  exact (originalPlaneMax_facts raw c hpositive (originalChosenSide raw c)).1

private theorem pairQ_eq_vertexRatio (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (side : Bool) (w : Word) :
    pairQ (planeRatioPair raw c side w) =
      vertexRatioQ raw side (childVertexQ raw c (wordChoice w)) := by
  have hw (i : Fin 5) : wireWidth i = (width i : ℤ) := by fin_cases i <;> decide
  have hv (i : Fin 5) : childVertexQ raw c (wordChoice w) i =
      (vertexNumer raw c w i : ℚ) / 1600 := by
    by_cases h : wordChoice w i
    · simp [childVertexQ, vertexNumer, wireLo, childLeftNumer, childRightNumer, hw, h]
    · simp [childVertexQ, vertexNumer, wireLo, childLeftNumer, childRightNumer, hw, h]
  have hS : (∑ i ∈ P1OriginalPrefixRowDecodeSoundness.maskSlots 5 raw.mask.toNat,
      childVertexQ raw c (wordChoice w) i) =
      ((selectedNumer raw (vertexNumer raw c w) : ℤ) : ℚ) / 1600 := by
    simp only [hv, selectedNumer, Int.cast_sum, Finset.sum_div]
  have hT : (∑ i : Fin 5, childVertexQ raw c (wordChoice w) i) =
      ((∑ i : Fin 5, vertexNumer raw c w i : ℤ) : ℚ) / 1600 := by
    simp only [hv, Int.cast_sum, Finset.sum_div]
  have hn : (vertexNumer raw c w 4 : ℚ) ≠ 0 := by
    exact_mod_cast (vertexNumer_pos raw c hpositive w 4).ne'
  unfold vertexRatioQ planeValueQ
  rw [hS, hT, hv]
  cases side <;>
    simp only [pairQ, planeRatioPair, Bool.false_eq_true, if_false, if_true,
      sideAlphaQ, sideBetaQ, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_ofNat] <;>
    field_simp [hn] <;> ring

/-- Actual chosen plane bounds every actual child vertex, supplied by the
original source fold itself rather than by an assumed finite checker fact. -/
theorem original_chosen_vertex_upper (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (w : Word) :
    vertexRatioQ raw (originalChosenSide raw c) (childVertexQ raw c (wordChoice w)) ≤
      originalRatioQ raw c := by
  rw [← pairQ_eq_vertexRatio raw c hpositive (originalChosenSide raw c) w]
  have h := (originalPlaneMax_facts raw c hpositive (originalChosenSide raw c)).2.2 w
  change pairQ (planeRatioPair raw c (originalChosenSide raw c) w) ≤ pairQ (originalAB raw c)
  rw [originalAB_eq_chosen_plane]
  exact h

noncomputable section
open Set

/-- The actual original A/B bounds the WHOLE closed child. No named-parent,
mask28, saved ratio domain or target integral hypothesis is needed here. -/
theorem originalRatioQ_bound_on_child (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (t : Fin 5 → ℝ) (ht : t ∈ Icc (childLeft raw c) (childRight raw c)) :
    residual (rawCandidate 0 raw t) t ≤ (originalRatioQ raw c : ℝ) := by
  exact actual_child_ratio_of_rational_vertices raw c
    (positiveKey_childLeft_pos raw hpositive c) (originalChosenSide raw c)
    (originalRatioQ raw c) (original_chosen_vertex_upper raw c hpositive) t ht

end
end ImbalancedChen.P5OriginalABFoldGeometry
