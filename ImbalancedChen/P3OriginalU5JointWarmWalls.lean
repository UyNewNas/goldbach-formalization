import ImbalancedChen.P3OriginalU5CommonPhysicalRoot
import ImbalancedChen.P3OriginalU5WarmMixedWallCover

/-!
The two marked prime pairs may differ. Their coordinates are the first
two slots of the wall, and the fixed physical cap supplies its centre.
Rough histories follow chronological order. The actual Boolean policy
takes the reversed histories.
-/

namespace ImbalancedChen.P3OriginalU5JointWarmWalls

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer (pairRoot)
open P2OriginalPairSourceReceiver (PairRange pairPlan ceiling)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P3OriginalU5WarmCapCodeStability
open P3OriginalU5WarmWordWalls
open P3OriginalU5WarmMixedWallCover (WallIndex wallForm wallCenter)
open P3OriginalU5CommonPhysicalRoot
open P4AUpperTaggedFrozenAdmissionCatalogue (strict_row_disagreement_proper_wall)
open P5Z.PresievedRoughSlotAffineGates (cubeRow)
open P5OriginalU5CausalFinite (pairSupport)

/-- The literal trace tests at each position, including the incoming flag. -/
private theorem accepted_iff_all_gates {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (X : Trace) (xs : List ℝ) :
    (run P a b X xs).accepted = true ↔ X.accepted = true ∧
      ∀ k : ℕ, ∀ hk : k < xs.length,
        admission (run P a b X (xs.take k)) (getElem xs k hk) := by
  induction xs generalizing X with
  | nil => simp [run]
  | cons x xs ih =>
    change (run P a b (step P a b X x) xs).accepted = true ↔ _
    rw [ih, step_accepted_iff]
    constructor
    · rintro ⟨⟨hX, hx⟩, hrest⟩
      refine ⟨hX, ?_⟩
      intro k hk
      cases k with
      | zero => exact hx
      | succ k => exact hrest k (by simpa using hk)
    · rintro ⟨hX, htests⟩
      refine ⟨⟨hX, htests 0 (by simp)⟩, ?_⟩
      intro k hk
      exact htests (k + 1) (by simpa using hk)

/-- A first genuine disagreement includes the individual earlier tests
on both original marked histories. -/
def FirstGateDifference {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (X Y : Trace) (xs ys : List ℝ) : Prop :=
  ∃ k : ℕ, ∃ hk : k < xs.length, ∃ hk' : k < ys.length,
    ¬(admission (run P a b X (xs.take k)) (getElem xs k hk) ↔
      admission (run P a b Y (ys.take k)) (getElem ys k hk')) ∧
    ∀ i : ℕ, ∀ hi : i < k,
      admission (run P a b X (xs.take i)) (getElem xs i (hi.trans hk)) ↔
        admission (run P a b Y (ys.take i)) (getElem ys i (hi.trans hk'))

theorem first_joint_admission_difference {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (X Y : Trace) (hX : X.accepted = true) (hY : Y.accepted = true)
    (xs ys : List ℝ) (hlen : xs.length = ys.length)
    (hd : ¬((run P a b X xs).accepted = true ↔ (run P a b Y ys).accepted = true)) :
    FirstGateDifference P a b X Y xs ys := by
  let bad (k : ℕ) : Prop := ∃ hk : k < xs.length, ∃ hk' : k < ys.length,
    ¬(admission (run P a b X (xs.take k)) (getElem xs k hk) ↔
      admission (run P a b Y (ys.take k)) (getElem ys k hk'))
  have hex : ∃ k, bad k := by
    by_contra hnone
    have heq (k : ℕ) (hk : k < xs.length) (hk' : k < ys.length) :
        admission (run P a b X (xs.take k)) (getElem xs k hk) ↔
          admission (run P a b Y (ys.take k)) (getElem ys k hk') := by
      by_contra hh
      exact hnone ⟨k, hk, hk', hh⟩
    apply hd
    rw [accepted_iff_all_gates, accepted_iff_all_gates, hX, hY]
    simp only [true_and]
    constructor
    · intro h k hk
      exact (heq k (by omega) hk).mp (h k (by omega))
    · intro h k hk
      exact (heq k hk (by omega)).mpr (h k (by omega))
  obtain ⟨hk, hk', hdifferent⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hk, hk', hdifferent, ?_⟩
  intro i hi
  by_contra hh
  exact (not_le.mpr hi) (Nat.find_min' hex ⟨hi.trans hk, hi.trans hk', hh⟩)

/-- Both marked coordinates precede every chronological rough coordinate. -/
def markedWord (N : ℕ) (t : ℕ × ℕ) (xs : List ℝ) : List ℝ :=
  coordinate N t.2 :: coordinate N t.1 :: xs

private theorem marked_cube {rank : ℕ} (N : ℕ) (t : ℕ × ℕ) (xs : List ℝ)
    (hx : xs.length = rank) (k : ℕ) (hk : k < xs.length) :
    cubeRow (⟨k + 2, by omega⟩ : Fin (rank + 2))
        (wordPoint (rank + 2) (markedWord N t xs)) =
      [coordinate N t.2, coordinate N t.1].sum + (xs.take k).sum + 3 * xs[k] := by
  have hlen : (markedWord N t xs).length = rank + 2 := by simp [markedWord, hx]
  rw [cubeRow_wordPoint _ hlen]
  change ((coordinate N t.2 :: coordinate N t.1 :: xs).take (k + 2)).sum + 3 * xs[k] = _
  simp only [List.take_succ_cons, List.sum_cons, List.sum_nil, add_zero]
  ring

/-- A mixed fine box for two actual marked roots has a proper wall in
the complete coordinate space. Both the bank and its seed are fixed. -/
theorem joint_marked_disagreement_wall {depth mesh rank : ℕ} (P : CapPlan depth mesh)
    (a b seed : ℝ) (hab : a < b) (N M : ℕ) (t u : ℕ × ℕ)
    (xs ys : List ℝ) (hx : xs.length = rank) (hy : ys.length = rank)
    {tau : ℝ} (htau : 0 < tau)
    (hfine : (markedWord N t xs).map (fun v => (⌊v / tau⌋ : ℤ)) =
      (markedWord M u ys).map (fun v => (⌊v / tau⌋ : ℤ)))
    (hd : ¬((run P a b (pairRoot N t seed) xs).accepted = true ↔
      (run P a b (pairRoot M u seed) ys).accepted = true)) :
    FirstGateDifference P a b (pairRoot N t seed) (pairRoot M u seed) xs ys ∧
      ∃ w : WallIndex depth mesh (rank + 2), wallForm w ≠ 0 ∧
        |wallForm w (wordPoint (rank + 2) (markedWord N t xs)) -
          wallCenter P a b seed 0 w| ≤ max 1 ‖wallForm w‖ * tau := by
  let X := pairRoot N t seed
  let Y := pairRoot M u seed
  let zx := markedWord N t xs
  let zy := markedWord M u ys
  have hz : zx.length = rank + 2 := by simp [zx, markedWord, hx]
  have hz' : zy.length = rank + 2 := by simp [zy, markedWord, hy]
  have hfirst := first_joint_admission_difference P a b X Y rfl rfl xs ys (hx.trans hy.symm) hd
  refine ⟨hfirst, ?_⟩
  by_cases hc : coarseWord a b mesh zx = coarseWord a b mesh zy
  · obtain ⟨k, hk, hk', htest, _⟩ := hfirst
    let i : Fin (rank + 2) := ⟨k + 2, by omega⟩
    have hbase : coarseWord a b mesh X.word = coarseWord a b mesh Y.word := by
      have h := congrArg (fun l : List (CellCode mesh) => l.take 2) hc
      simpa [coarseWord, zx, zy, markedWord, X, Y, pairRoot] using h
    have hrough : coarseWord a b mesh xs = coarseWord a b mesh ys := by
      have h := congrArg (fun l : List (CellCode mesh) => l.drop 2) hc
      simpa [coarseWord, zx, zy, markedWord] using h
    have hprefix : coarseWord a b mesh (xs.take k) = coarseWord a b mesh (ys.take k) := by
      simpa only [coarseWord, List.map_take] using congrArg (fun l => List.take k l) hrough
    have hcaps := run_cap_eq_of_coarseWord P a b _ _ X Y rfl hbase hprefix
    have hxl : (run P a b X (xs.take k)).word.length = 2 + k := by
      rw [run_word, List.length_append, List.length_take, Nat.min_eq_left hk.le]
      rfl
    have hyl : (run P a b Y (ys.take k)).word.length = 2 + k := by
      rw [run_word, List.length_append, List.length_take, Nat.min_eq_left hk'.le]
      rfl
    have hnonzero : 2 + k ≠ 0 := by omega
    have heven : (2 + k + 1) % 2 = 0 := by
      by_contra hodd
      apply htest
      simp only [admission, hxl, hyl, if_neg hnonzero, if_neg hodd]
    let c := (run P a b X (xs.take k)).cap
    have hgateX : admission (run P a b X (xs.take k)) xs[k] ↔
        cubeRow i (wordPoint (rank + 2) zx) < c := by
      rw [marked_cube N t xs hx k hk, admission, hxl, if_neg hnonzero,
        if_pos heven, run_word, List.sum_append]
      exact Iff.rfl
    have hgateY : admission (run P a b Y (ys.take k)) ys[k] ↔
        cubeRow i (wordPoint (rank + 2) zy) < c := by
      rw [marked_cube M u ys hy k hk', admission, hyl, if_neg hnonzero,
        if_pos heven, run_word, List.sum_append, ← hcaps]
      exact Iff.rfl
    have hrow : ¬(cubeRow i (wordPoint (rank + 2) zx) < c ↔
        cubeRow i (wordPoint (rank + 2) zy) < c) :=
      fun hh => htest (hgateX.trans (hh.trans hgateY.symm))
    obtain ⟨hproper, hwall⟩ := strict_row_disagreement_proper_wall (cubeRow i) c tau
      (wordPoint (rank + 2) zx) (wordPoint (rank + 2) zy)
      (same_floor_wordPoint_norm_le htau zx zy hz hz' hfine) hrow
    have hcap : c ∈ capAlphabet P seed :=
      run_cap_mem_capAlphabet P a b seed X _ (seed_mem_capAlphabet P seed)
    obtain ⟨addr, _, haddr⟩ := Finset.mem_image.mp hcap
    refine ⟨Sum.inr (i, addr), hproper, ?_⟩
    change |cubeRow i (wordPoint (rank + 2) zx) - (addressedCap P seed addr - 0)| ≤ _
    rw [sub_zero, haddr]
    exact hwall.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) htau.le)
  · obtain ⟨i, hi⟩ := coarseWord_disagreement_coordinate (hz.trans hz'.symm) hc
    have hclose := same_floor_coordinate_le htau zx zy hfine i.val i.isLt
    obtain ⟨j, hj⟩ := exponentCode_disagreement_boundary hab hclose hi
    let i' : Fin (rank + 2) := ⟨i.val, by have := i.isLt; omega⟩
    have hproper : (ContinuousLinearMap.proj i' : (Fin (rank + 2) → ℝ) →L[ℝ] ℝ) ≠ 0 := by
      intro hz0
      have he := congrArg (fun L : (Fin (rank + 2) → ℝ) →L[ℝ] ℝ => L (fun _ => 1)) hz0
      simp at he
    refine ⟨Sum.inl (i', j), hproper, ?_⟩
    change |wordPoint (rank + 2) zx i' - logPrimeMeshPoint a b mesh j.val| ≤
      max 1 ‖(ContinuousLinearMap.proj i' : (Fin (rank + 2) → ℝ) →L[ℝ] ℝ)‖ * tau
    rw [wordPoint_getElem zx hz i']
    exact hj.trans (le_mul_of_one_le_left htau.le (le_max_left _ _))

/-- The wall result for the installed physical policy at two original
prime pairs sharing an owner. Its catalogue includes coarse boundaries
in either exterior slot. The centre of a cube wall is the actual
incoming cap at the first disagreeing decision. -/
theorem original_U5_joint_policy_disagreement_wall (R : PairRange) {mesh rank : ℕ}
    (bank : CandidateBank mesh) (b : ℚ) (m : ℕ) {N M : ℕ} (hN : 2 ≤ N) (hM : 2 ≤ M)
    {t u : ℕ × ℕ} (ht : t ∈ pairSupport N) (hu : u ∈ pairSupport M)
    (hj : rowOwner R m hN ht = rowOwner R m hM hu)
    (H K : List ℕ) (hH : H.length = rank) (hK : K.length = rank)
    {tau : ℝ} (htau : 0 < tau)
    (hfine : (markedWord N t (H.map (coordinate N))).map (fun v => (⌊v / tau⌋ : ℤ)) =
      (markedWord M u (K.map (coordinate M))).map (fun v => (⌊v / tau⌋ : ℤ)))
    (hd : ¬(policy R bank b m N t H.reverse = true ↔
      policy R bank b m M u K.reverse = true)) :
    let seed := physicalSeed R b (rowOwner R m hN ht)
    let P := pairPlan R bank (2 * b) seed
    FirstGateDifference P (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t seed) (pairRoot M u seed)
        (H.map (coordinate N)) (K.map (coordinate M)) ∧
      ∃ w : WallIndex 5 mesh (rank + 2), wallForm w ≠ 0 ∧
        |wallForm w (wordPoint (rank + 2) (markedWord N t (H.map (coordinate N)))) -
          wallCenter P (R.epsilon : ℝ) (ceiling : ℝ) seed 0 w| ≤ max 1 ‖wallForm w‖ * tau := by
  have hx := policy_eq_owner_trace R bank b m hN ht H.reverse
  have hy := policy_eq_owner_trace R bank b m hM hu K.reverse
  simp only [List.reverse_reverse] at hx hy
  rw [← hj] at hy
  rw [hx, hy] at hd
  have hab : (R.epsilon : ℝ) < (ceiling : ℝ) :=
    Rat.cast_lt.mpr (R.epsilon_lt_a.trans (by norm_num [ceiling]))
  exact joint_marked_disagreement_wall _ _ _ _ hab N M t u _ _
    (by simpa only [List.length_map] using hH) (by simpa only [List.length_map] using hK)
    htau hfine hd

end
end ImbalancedChen.P3OriginalU5JointWarmWalls
