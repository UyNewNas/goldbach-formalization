import ImbalancedChen.P3OriginalU5ThreeFrontierIdentity
import ImbalancedChen.FirstExitFrontierWeightBound
import Batteries.Tactic.OpenPrivate

/-! Prime window and total reciprocal weight of the actual cap changes on the
three marked-pair frontiers. The receiver is fixed before the large-target
threshold. Both external primes enter the strict full-square check. -/

namespace ImbalancedChen.P3OriginalU5ChangedFrontierSupport

noncomputable section
open scoped Classical List BigOperators
open Filter Topology
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalSelectedPairNativeData
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalLowerSelectedCapConstructor (Code prefixCode strictSquareGates)
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)
open P2EnhancedLowerPhysicalNode (Slot)
open P3OriginalU5WarmRosserAdmission (incoming)
open P5OriginalU5CausalFinite (pairSupport cutoff coordinates_mem_triangle)
open FirstExitFrontierWeightBound (windowWeight windowWeight_nonneg windowWeight_eq_of_mem
  exists_frontier_window_weight_bound)

open private incoming_cap_le incoming_cons from ImbalancedChen.P3OriginalU5WarmRosserAdmission

private abbrev weight (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

private theorem qHi_nonneg (R : PairRange) (mesh : ℕ) (c : CellCode mesh) :
    0 ≤ (qHi R mesh c : ℝ) := by
  cases c with
  | none => norm_num [qHi, ceiling]
  | some j =>
    have he := R.epsilon_pos
    have hd : 0 ≤ ceiling - R.epsilon := by
      dsimp only [ceiling]
      linarith [R.epsilon_lt_a]
    have hq : 0 ≤ qPoint R mesh (j.val+1) := by
      unfold qPoint
      positivity
    change (0 : ℝ) ≤ (qPoint R mesh (j.val+1) : ℝ)
    exact_mod_cast hq

private theorem impossible_square (j : Fin 3) (v : Fin 5 → ℝ) (M : ℝ)
    (hM : M ≤ 153/256) (h0 : 417/5000 ≤ v 0) (h1 : 417/5000 ≤ v 1)
    (h2 : 0 ≤ v 2) (h3 : 0 ≤ v 3) (hlast : v ⟨j.val+2, by omega⟩ = 59/250)
    (hs : strictSquareGates M 0 ([v 0, v 1, v 2, v 3, v 4].take (j.val+3))) : False := by
  fin_cases j
  · change v 2 = _ at hlast
    have hf : 0 + v 0 + v 1 + 2*v 2 < M := hs.2.2.1
    linarith
  · change v 3 = _ at hlast
    have hf : 0 + v 0 + v 1 + v 2 + 2*v 3 < M := hs.2.2.2.1
    linarith
  · change v 4 = _ at hlast
    have hf : 0 + v 0 + v 1 + v 2 + v 3 + 2*v 4 < M := hs.2.2.2.2.1
    linarith

private theorem missing_slot_inherits (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (j : Fin 3) (parent : ℝ) (code : Code mesh)
    (h0 : (417/5000 : ℝ) ≤ (qHi R mesh (code 0).1 : ℝ))
    (h1 : (417/5000 : ℝ) ≤ (qHi R mesh (code 1).1 : ℝ))
    (hm : (code ⟨j.val+2, by omega⟩).1 = none) :
    checkedChoice R bank delta ⟨j.val+3, by omega⟩ parent code = .inherit 2 := by
  let rank : Fin 6 := ⟨j.val+3, by omega⟩
  let i : Fin 5 := ⟨j.val+2, by omega⟩
  let C := prefixCode rank.val code
  let v (n : Fin 5) : ℝ := qHi R mesh (C n).1
  have hc (n : Fin 5) (hn : n.val < rank.val) : C n = code n := by
    simp only [C, prefixCode, if_pos hn]
  have hv0 : 417/5000 ≤ v 0 := by
    simpa only [v, hc 0 (by dsimp [rank]; omega)] using h0
  have hv1 : 417/5000 ≤ v 1 := by
    simpa only [v, hc 1 (by dsimp [rank]; omega)] using h1
  have hvi : v i = 59/250 := by
    unfold v
    rw [hc i (by dsimp [i, rank]; omega), show (code i).1 = none from hm]
    norm_num [qHi, ceiling]
  change checkedChoice R bank delta rank parent code = _
  unfold checkedChoice
  change (match select R bank delta rank C with
    | none => CapChoice.inherit 2
    | some branch => if freshCheck R rank C delta parent branch then
        .fresh (rowCap R C delta branch) branch.argument else .inherit 2) = _
  cases hsel : select R bank delta rank C with
  | none => rfl
  | some branch =>
    have hsource := (select_some_source R bank delta rank C branch hsel).2
    have hcc : prefixCode rank.val C = C := prefixCode_nested _ _ le_rfl code
    rw [hcc] at hsource
    have hfull : strictSquareGates (rowCap R C delta branch : ℝ) 0
        ([v 0, v 1, v 2, v 3, v 4].take rank.val) := by
      simpa only [v, ownSlots, List.map_take, List.map_cons, List.map_nil, ownSlot]
        using hsource.2.2.1
    have hn : ¬freshCheck R rank C delta parent branch := fun hx =>
      impossible_square j v _ hx.2.1 hv0 hv1 (qHi_nonneg R mesh (C 2).1)
        (qHi_nonneg R mesh (C 3).1) hvi hfull
    simp only [if_neg hn]

private theorem original_outer_endpoints (R : PairRange) (mesh : ℕ) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    let upper (p : ℕ) := (qHi R mesh (exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh (coordinate N p)) : ℝ)
    417/5000 ≤ upper t.2 ∧ 417/5000 ≤ upper t.1 := by
  obtain ⟨hu, hut, hh⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp (coordinates_mem_triangle hN ht)
  change (417/5000 : ℝ) ≤ coordinate N t.1 at hu
  change coordinate N t.1 < coordinate N t.2 at hut
  change coordinate N t.2 < (19/125 : ℝ) at hh
  have he : (R.epsilon : ℝ) ≤ 417/5000 := by
    have hr : (R.epsilon : ℝ) ≤ ((417/5000 : ℚ) : ℝ) := Rat.cast_le.mpr R.epsilon_lt_a.le
    norm_num at hr ⊢
    exact hr
  have hc : (19/125 : ℝ) ≤ (ceiling : ℝ) := by norm_num [ceiling]
  exact ⟨(hu.trans hut.le).trans (exponent_upper R mesh ⟨(he.trans hu).trans hut.le, hh.le.trans hc⟩),
    hu.trans (exponent_upper R mesh ⟨he.trans hu, (hut.le.trans hh.le).trans hc⟩)⟩

/-- A sub-grid arrival leaves its actual incoming cap unchanged. No rough
cutoff is imposed on the selected-policy carrier to obtain this equality. -/
theorem original_U5_below_grid_inherits (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (H : List ℕ) (q : ℕ) (hsmall : coordinate N q < (R.epsilon : ℝ)) :
    (incoming R bank b N t (q :: H)).cap = (incoming R bank b N t H).cap := by
  let x := coordinate N
  let seed := rootSeed false b N t
  have hm : exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh (x q) = none := by
    have hout : x q ∉ Set.Ico (R.epsilon : ℝ) (ceiling : ℝ) := fun hh => (not_le.mpr hsmall) hh.1
    simp only [exponentCode, dif_neg hout]
  obtain ⟨h0, h1⟩ := original_outer_endpoints R mesh hN ht
  cases H with
  | nil =>
    let C := codeAt R mesh 3 [x t.2, x t.1, x q]
    have hi := missing_slot_inherits R bank (2*b) 0 seed C h0 h1 hm
    change checkedChoice R bank (2*b) 3 seed C = CapChoice.inherit 2 at hi
    change (checkedChoice R bank (2*b) 3 seed C).freeze _ = _
    rw [hi]
    rfl
  | cons p H =>
    cases H with
    | nil =>
      let C := codeAt R mesh 4 [x t.2, x t.1, x p, x q]
      have hi := missing_slot_inherits R bank (2*b) 1 (cap3 R bank (2*b) seed C) C h0 h1 hm
      change checkedChoice R bank (2*b) 4 (cap3 R bank (2*b) seed C) C = CapChoice.inherit 2 at hi
      change (checkedChoice R bank (2*b) 4 (cap3 R bank (2*b) seed C) C).freeze _ = _
      rw [hi]
      rfl
    | cons r H =>
      cases H with
      | nil =>
        let C := codeAt R mesh 5 [x t.2, x t.1, x r, x p, x q]
        have hi := missing_slot_inherits R bank (2*b) 2 (cap4 R bank (2*b) seed C) C h0 h1 hm
        change checkedChoice R bank (2*b) 5 (cap4 R bank (2*b) seed C) C = CapChoice.inherit 2 at hi
        change (checkedChoice R bank (2*b) 5 (cap4 R bank (2*b) seed C) C).freeze _ = _
        rw [hi]
        rfl
      | cons s H =>
        rw [incoming_cons R bank b N t (p :: r :: s :: H) q]
        apply no_new_cap_outside_345
        simp only [incoming, P3OriginalU5AllSourceSquares.actualTrace_word, List.length_append, List.length_cons,
          List.length_nil, List.length_map, List.length_reverse]
        omega


/-- Public access to the monotonicity proved with the pinned warm trace's
causal prefix lookups. The theorem applies also to a terminal history. -/
theorem original_U5_incoming_cap_mono (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) (q : ℕ) :
    (incoming R bank b N t H).cap ≤ (incoming R bank b N t (q :: H)).cap :=
  incoming_cap_le R bank b N t H q

/-- Histories are in the original frontier list order, with its multiplicity. -/
def changedHistories (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (enum k : ℕ) : List (List ℕ) :=
  ((firstExitDepthFrontier k (evenFirstExitPolicy (selectedPolicy R bank b false N t)) weight
    [] true 1 (roughPrimeUniverse N enum 0 (cutoff N))).map (fun s => s.selectedPrefix)).filter
      (fun H => decide ((incoming R bank b N t H).cap ≠ (incoming R bank b N t H.tail).cap))

def changedMass (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (enum k : ℕ) : ℝ :=
  ((changedHistories R bank b N t enum k).map (fun H => (H.map weight).prod)).sum

/-- Every prime of an actually changed history belongs to the fixed power
window. The lower endpoint follows from the last checked square and the
strictly decreasing processing order. -/
theorem original_U5_changed_frontier_window (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (enum k : ℕ)
    (hk : 0 < k) (H : List ℕ) (hH : H ∈ changedHistories R bank b N t enum k) :
    H.length = k ∧ ∀ p ∈ H, p.Prime ∧ ¬p ∣ N ∧ (N : ℝ) ^ (R.epsilon : ℝ) ≤ p ∧ (p : ℝ) < cutoff N := by
  obtain ⟨hlist, hd⟩ := List.mem_filter.mp hH
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hlist
  have hdiff := of_decide_eq_true hd
  obtain ⟨hlen, _, _, hmin, _, _, _⟩ := actualPrimeFrontier_geometry k hk _ N enum (cutoff N) s hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k _ weight _ s hs
  have hhead : (N : ℝ) ^ (R.epsilon : ℝ) ≤ (s.selectedPrefix.headD 0 : ℝ) := by
    cases he : s.selectedPrefix with
    | nil => simp only [he, List.length_nil] at hlen; omega
    | cons q H =>
      rw [he] at hdiff hsub
      have hq : (R.epsilon : ℝ) ≤ coordinate N q := by
        by_contra! hl
        exact hdiff (original_U5_below_grid_inherits R bank b hN ht H q hl)
      have hmem := hsub.subset (List.mem_reverse.mpr (List.mem_cons_self (a := q) (l := H)))
      have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      exact (Real.rpow_le_rpow_of_exponent_le hNr.le hq).trans_eq
        (coordinate_power hNr (mem_roughPrimeUniverse_prime hmem).pos)
  refine ⟨hlen, ?_⟩
  intro p hp
  have hh := hsub.subset (List.mem_reverse.mpr hp)
  exact ⟨mem_roughPrimeUniverse_prime hh, mem_roughPrimeUniverse_not_dvd hh,
    hhead.trans (hmin p hp), mem_roughPrimeUniverse_upper hh⟩

private theorem filtered_sum_le (keep : List ℕ → Bool) (F : List ℕ → ℝ)
    (hF : ∀ H, 0 ≤ F H) (hs : List (List ℕ)) :
    ((hs.filter keep).map F).sum ≤ (hs.map F).sum := by
  induction hs with
  | nil => simp
  | cons H hs ih =>
    by_cases h : keep H = true
    · simpa [h] using add_le_add_left ih (F H)
    · simpa [h] using ih.trans (le_add_of_nonneg_left (hF H))

/-- The sum on the changed histories is bounded by a sum on the same full
frontier using the actual target-deleted power window. -/
theorem original_U5_changedMass_le (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum k : ℕ) (hk : 0 < k) :
    changedMass R bank b N t enum k ≤
      ((firstExitDepthFrontier k (evenFirstExitPolicy (selectedPolicy R bank b false N t))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N enum 0 (cutoff N))).map
        (fun s => (s.selectedPrefix.map (windowWeight N (R.epsilon : ℝ) (417/5000))).prod)).sum := by
  let g := windowWeight N (R.epsilon : ℝ) (417/5000)
  let F (H : List ℕ) := (H.map g).prod
  let L := (firstExitDepthFrontier k (evenFirstExitPolicy (selectedPolicy R bank b false N t))
    weight [] true 1 (roughPrimeUniverse N enum 0 (cutoff N))).map (fun s => s.selectedPrefix)
  let keep (H : List ℕ) := decide ((incoming R bank b N t H).cap ≠ (incoming R bank b N t H.tail).cap)
  have hF (H : List ℕ) : 0 ≤ F H := by
    induction H with
    | nil => exact zero_le_one
    | cons q H ih => exact mul_nonneg (windowWeight_nonneg N _ _ q) ih
  calc
    _ = ((L.filter keep).map F).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro H hH
      have hdata := (original_U5_changed_frontier_window R bank b hN ht enum k hk H hH).2
      apply congrArg List.prod
      apply List.map_congr_left
      intro p hp
      obtain ⟨hp', htarget, hlo, hhi⟩ := hdata p hp
      have hmem : p ∈ roughPrimeUniverse N (Nat.ceil (cutoff N)) 0 (cutoff N) :=
        (mem_roughPrimeUniverse_iff_of_cutoff_le_cap (Nat.le_ceil _)).mpr
          ⟨hp', htarget, Nat.cast_nonneg _, hhi⟩
      exact (windowWeight_eq_of_mem hmem hlo).symm
    _ ≤ (L.map F).sum := filtered_sum_le keep F hF L
    _ = _ := by simp only [L, F, g, List.map_map, Function.comp_def]

/-- One constant and threshold precede the target, the mesh, the bank, the
buffer, the pair, the enumeration cap and the selected rank. -/
theorem eventually_original_U5_changedMass_le (R : PairRange) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ {mesh : ℕ} (bank : CandidateBank mesh)
      (b : ℚ) {t : ℕ × ℕ}, t ∈ pairSupport N → ∀ enum k : ℕ, 0 < k →
        changedMass R bank b N t enum k ≤ C := by
  obtain ⟨C, hC, N0, hN0, hb⟩ := exists_frontier_window_weight_bound (R.epsilon : ℝ) (417/5000)
    (by exact_mod_cast R.epsilon_pos) (by norm_num)
  refine ⟨C, hC, N0, hN0, ?_⟩
  intro N hN mesh bank b t ht enum k hk
  exact (original_U5_changedMass_le R bank b (hN0.trans hN) ht enum k hk).trans
    (hb N hN enum k (evenFirstExitPolicy (selectedPolicy R bank b false N t)) weight)

end
end ImbalancedChen.P3OriginalU5ChangedFrontierSupport
