import ImbalancedChen.P5OriginalActiveRowDomain

/-! One original parent lower-vertex integer gate controls b<=4 for all64
children. Coordinate monotonicity of each plane-minus-four-times-denominator
replaces child-by-child domain evaluation; no archive claim is assumed. -/
set_option autoImplicit false

namespace ImbalancedChen.P5OriginalParentFourGate

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5OriginalChildIntegerWireBinding P5OriginalGenericWireFloorReceiver
open P5OriginalABFoldGeometry P5OriginalActiveRowDomain P5ArbitraryMaskChildVertexRatio
open P5OldFifthExact64ChildTiling P5OldFifthFiveCoordinateTree P5OldFifthChildGapIntegral

/-- Pure original parent keys; this is a new internal domain check, not a
stored child field or a numerical integral licence. -/
def parentFourGate (raw : FifthWireRow) : Prop :=
  let S : ℤ := ∑ i ∈ maskSlots 5 raw.mask.toNat, raw.lo i
  min (6400 + 16 * S) (11400 - 48 * S) ≤
    32 * ((∑ i : Fin 5, raw.lo i) + 4 * raw.lo 4)

instance (raw : FifthWireRow) : Decidable (parentFourGate raw) := by
  unfold parentFourGate
  infer_instance

private theorem vertex_ge_parent4 (raw : FifthWireRow) (c : ChildIndex) (w : Word)
    (i : Fin 5) : 4 * raw.lo i ≤ vertexNumer raw c w i := by
  have hw : 0 ≤ wireWidth i := by fin_cases i <;> decide
  have hm := mul_nonneg hw (Int.natCast_nonneg (c i).val)
  unfold vertexNumer wireLo
  split_ifs <;> linarith

private theorem vertex_plane_four (raw : FifthWireRow) (c : ChildIndex) (w : Word)
    (side : Bool)
    (hs : (if side then 11400 - 48 * (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.lo i)
      else 6400 + 16 * (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.lo i)) ≤
        32 * ((∑ i : Fin 5, raw.lo i) + 4 * raw.lo 4)) :
    (planeRatioPair raw c side w).num ≤ 4 * (planeRatioPair raw c side w).den := by
  let I := maskSlots 5 raw.mask.toNat
  let v := vertexNumer raw c w
  let delta : Fin 5 → ℤ := fun i => v i - 4 * raw.lo i
  have hd (i : Fin 5) : 0 ≤ delta i := sub_nonneg.mpr (vertex_ge_parent4 raw c w i)
  have hv (i : Fin 5) : v i = 4 * raw.lo i + delta i := by dsimp only [delta]; ring
  have hS0 : 0 ≤ ∑ i ∈ I, delta i := Finset.sum_nonneg (fun i _ => hd i)
  have hT0 : 0 ≤ ∑ i : Fin 5, delta i := Finset.sum_nonneg (fun i _ => hd i)
  have hST : (∑ i ∈ I, delta i) ≤ ∑ i : Fin 5, delta i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => hd i)
  have hS : (∑ i ∈ I, v i) =
      4 * (∑ i ∈ I, raw.lo i) + ∑ i ∈ I, delta i := by
    simp_rw [hv]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hT : (∑ i : Fin 5, v i) =
      4 * (∑ i : Fin 5, raw.lo i) + ∑ i : Fin 5, delta i := by
    simp_rw [hv]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (if side then 45600 - 48 * (∑ i ∈ I, v i)
    else 25600 + 16 * (∑ i ∈ I, v i)) - 32 * (∑ i : Fin 5, v i) ≤ 4 * (32 * v 4)
  rw [hS, hT, hv 4]
  change (if side then 11400 - 48 * (∑ i ∈ I, raw.lo i)
    else 6400 + 16 * (∑ i ∈ I, raw.lo i)) ≤
      32 * ((∑ i : Fin 5, raw.lo i) + 4 * raw.lo 4) at hs
  cases side <;> simp only [Bool.false_eq_true, if_false, if_true] at hs ⊢ <;>
    linarith [hd 4]

private theorem ratio_le_planeMax (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (side : Bool) :
    originalRatioQ raw c ≤
      ((originalPlaneMax raw c side).num : ℚ) / ((originalPlaneMax raw c side).den : ℚ) := by
  have ha : (0 : ℚ) < ((originalPlaneMax raw c false).den : ℚ) := by
    exact_mod_cast (originalPlaneMax_facts raw c hpositive false).1
  have hc : (0 : ℚ) < ((originalPlaneMax raw c true).den : ℚ) := by
    exact_mod_cast (originalPlaneMax_facts raw c hpositive true).1
  change ((originalAB raw c).num : ℚ) / ((originalAB raw c).den : ℚ) ≤ _
  dsimp only [originalAB]
  by_cases h : (originalPlaneMax raw c true).num * (originalPlaneMax raw c false).den <
      (originalPlaneMax raw c false).num * (originalPlaneMax raw c true).den
  · rw [if_pos h]
    cases side
    · apply (div_le_div_iff₀ hc ha).mpr
      exact_mod_cast h.le
    · exact le_rfl
  · rw [if_neg h]
    cases side
    · exact le_rfl
    · apply (div_le_div_iff₀ ha hc).mpr
      exact_mod_cast le_of_not_gt h

private theorem planeMax_le_four (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (side : Bool)
    (hs : (if side then 11400 - 48 * (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.lo i)
      else 6400 + 16 * (∑ i ∈ maskSlots 5 raw.mask.toNat, raw.lo i)) ≤
        32 * ((∑ i : Fin 5, raw.lo i) + 4 * raw.lo 4)) :
    ((originalPlaneMax raw c side).num : ℚ) / ((originalPlaneMax raw c side).den : ℚ) ≤ 4 := by
  obtain ⟨w, hw⟩ := (originalPlaneMax_facts raw c hpositive side).2.1
  have hd : (0 : ℚ) < ((originalPlaneMax raw c side).den : ℚ) := by
    exact_mod_cast (originalPlaneMax_facts raw c hpositive side).1
  apply (div_le_iff₀ hd).mpr
  rw [hw]
  exact_mod_cast vertex_plane_four raw c w side hs

/-- One integer parent gate implies b<=4 on EVERY original child, including
nonpositive d. No child floor/d enumeration or stored A/B identity is needed. -/
theorem all_child_ratios_le_four (raw : FifthWireRow)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (hgate : parentFourGate raw)
    (c : ChildIndex) : originalRatioQ raw c ≤ 4 := by
  unfold parentFourGate at hgate
  rcases min_le_iff.mp hgate with hA | hC
  · exact (ratio_le_planeMax raw c hpositive false).trans
      (planeMax_le_four raw c hpositive false hA)
  · exact (ratio_le_planeMax raw c hpositive true).trans
      (planeMax_le_four raw c hpositive true hC)

/-- Original complete child receiver, supplied by pure PARENT integer gates.
The actual source fact and its analytic consumers keep their original types. -/
theorem all_child_source_facts (raw : FifthWireRow) (hg : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hupper : ∀ i : Fin 5, 96 * (raw.lo i + 1) ≤ 19 * raw.grid)
    (hgate : parentFourGate raw) : ∀ c : ChildIndex, SourceChildFacts raw c := by
  intro c
  exact sourceChildFacts_of_upper_and_ratio4 raw hg hpositive hupper c
    (fun _ => all_child_ratios_le_four raw hpositive hgate c)

end ImbalancedChen.P5OriginalParentFourGate
