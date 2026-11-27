import ImbalancedChen.P3OriginalU5WarmRosserAdmission
import ImbalancedChen.ActualFrozenFrontierDensity

/-! Exact lower Rosser density of the original selected U5 pair policy. The two
external marks are present in every `rowLevel`. At each retained rough rank
one, two and three, the new level is read after the last selection and the
old level from its parent. Both continuations use the same signed frontier.
-/

namespace ImbalancedChen.P3OriginalU5ThreeFrontierIdentity

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2OriginalSelectedPairNativeData
open P2OriginalPairSourceReceiver P3OriginalU5AllSourceSquares
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P3OriginalU5WarmRosserAdmission (incoming rowLevel
  original_U5_warm_rosser_prefix_admissible original_U5_warm_rosser_admission)
open P5OriginalU5CausalFinite (pairSupport cutoff fullDensity)

private abbrev weight (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

private abbrev selectedTree (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) : Bool → List ℕ → Bool :=
  evenFirstExitPolicy (selectedPolicy R bank b false N t)

/-- The actual prime is tested against the incoming level of its parent. -/
private def incomingGate (Q : List ℕ → ℝ) (positive : Bool) (H : List ℕ) : Bool :=
  ordinaryParityRosserPolicy true (Q H.tail) positive H

private def stage (k : ℕ) (Q : List ℕ → ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy k (incomingGate Q) (frozenParityRosserPolicy true k Q)

private theorem left_subword (A B : List ℕ) : A <+ A ++ B := by
  induction A with
  | nil => simp
  | cons p A ih => exact ih.cons_cons p

private theorem selected_step (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) (q : ℕ)
    (ha : (incoming R bank b N t H).accepted = true) :
    selectedTree R bank b N t (!(evenListLength H)) (q :: H) = true ↔
      (incoming R bank b N t (q :: H)).accepted = true := by
  let seed := rootSeed false b N t
  have hh := validSelection_iff_warm_trace (pairPlan R bank (2*b) seed)
    (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t seed) rfl N [q] H ha
  exact ⟨fun hp => hh.mp ⟨hp, trivial⟩, fun hp => (hh.mpr hp).1⟩

private theorem incoming_cons_accepted (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) (q : ℕ) :
    (incoming R bank b N t (q :: H)).accepted = true ↔
      (incoming R bank b N t H).accepted = true ∧
        admission (incoming R bank b N t H) (coordinate N q) :=
  warmRetain_cons_iff (pairPlan R bank (2*b) (rootSeed false b N t))
    (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t (rootSeed false b N t)) N q H

/-- Both the polynomial and the complete stopped list agree, with the
selected policy providing the accepted trace at every recursive call. -/
private theorem selected_tree_comparison (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum k : ℕ) (h : ℕ → ℝ) (rem H : List ℕ) (mass : ℝ)
    (hsub : H.reverse ++ rem <+ roughPrimeUniverse N enum 0 (cutoff N))
    (hacc : (incoming R bank b N t H).accepted = true) :
    (firstExitRetainedPolynomial (selectedTree R bank b N t) h H (evenListLength H) mass rem =
      firstExitRetainedPolynomial (incomingGate (rowLevel R bank b N t)) h H
        (evenListLength H) mass rem) ∧
    (firstExitDepthFrontier k (selectedTree R bank b N t) h H (evenListLength H) mass rem =
      firstExitDepthFrontier k (incomingGate (rowLevel R bank b N t)) h H
        (evenListLength H) mass rem) := by
  induction rem generalizing H mass with
  | nil => exact ⟨rfl, rfl⟩
  | cons q rem ih =>
    have hskipSub := ((List.Sublist.refl H.reverse).append (List.sublist_cons_self q rem)).trans hsub
    have htakeSub : (q :: H).reverse ++ rem <+ roughPrimeUniverse N enum 0 (cutoff N) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsub
    have hqSub := (left_subword (q :: H).reverse rem).trans htakeSub
    have hstep := selected_step R bank b N t H q hacc
    have hcons := incoming_cons_accepted R bank b N t H q
    have htest := (original_U5_warm_rosser_admission R bank b hb hN ht enum 0 H q hqSub hacc).2
    have hgate : selectedTree R bank b N t (!(evenListLength H)) (q :: H) = true ↔
        incomingGate (rowLevel R bank b N t) (!(evenListLength H)) (q :: H) = true :=
      ⟨fun hp => htest.mp (hcons.mp (hstep.mp hp)).2,
        fun hp => hstep.mpr (hcons.mpr ⟨hacc, htest.mpr hp⟩)⟩
    have hskip := ih H mass hskipSub hacc
    by_cases hp : selectedTree R bank b N t (!(evenListLength H)) (q :: H) = true
    · have hother := hgate.mp hp
      have htake := ih (q :: H) (mass * h q) htakeSub (hstep.mp hp)
      simp only [evenListLength] at htake
      exact ⟨by simp only [firstExitRetainedPolynomial, hp, hother, if_true, hskip.1, htake.1],
        by simp only [firstExitDepthFrontier, hp, hother, if_true, hskip.2, htake.2]⟩
    · have hother := fun hv => hp (hgate.mpr hv)
      exact ⟨by simp only [firstExitRetainedPolynomial, if_neg hp, if_neg hother, hskip.1],
        by simp only [firstExitDepthFrontier, if_neg hp, if_neg hother, hskip.2]⟩

private theorem actual_frontier_accepted (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (k : ℕ) (h : ℕ → ℝ) (carrier : List ℕ)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier k (selectedTree R bank b N t) h [] true 1 carrier) :
    (incoming R bank b N t s.selectedPrefix).accepted = true := by
  obtain ⟨chosen, _, hv, he⟩ := exists_validSelection_of_mem_firstExitRetainedLeaves
    (selectedTree R bank b N t) h [] carrier true 1
    ⟨s.selectedPrefix, s.positive, s.mass⟩
    (firstExitDepthFrontier_toLeaf_mem k _ h [] carrier true 1 s hs)
  change s.selectedPrefix = chosen.reverse ++ [] at he
  rw [he]
  exact (validSelection_iff_warm_trace (pairPlan R bank (2*b) (rootSeed false b N t))
    (R.epsilon : ℝ) (ceiling : ℝ) (pairRoot N t (rootSeed false b N t)) rfl N chosen [] rfl).mp hv

/-- A state on the literal selected-policy frontier has passed all ordinary
prefix tests at both the incoming and the outgoing marked-pair levels. -/
theorem original_U5_selected_frontier_admissible (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (enum k : ℕ) (h : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier k (evenFirstExitPolicy (selectedPolicy R bank b false N t))
      h [] true 1 (roughPrimeUniverse N enum 0 (cutoff N))) :
    ordinaryRosserPrefixAdmissible true (rowLevel R bank b N t s.selectedPrefix.tail)
        s.selectedPrefix ∧
      ordinaryRosserPrefixAdmissible true (rowLevel R bank b N t s.selectedPrefix) s.selectedPrefix := by
  have ha := actual_frontier_accepted R bank b N t k h _ s hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k _ h _ s hs
  have hnew := (original_U5_warm_rosser_prefix_admissible R bank b hb hN ht enum 0
    s.selectedPrefix hsub ha).2
  refine ⟨?_, hnew⟩
  cases he : s.selectedPrefix with
  | nil => simpa only [he, List.tail_nil] using hnew
  | cons q H =>
    rw [he] at hsub ha
    have hpass := (incoming_cons_accepted R bank b N t H q).mp ha
    have hparent : H.reverse <+ roughPrimeUniverse N enum 0 (cutoff N) :=
      (left_subword H.reverse [q]).trans (by simpa only [List.reverse_cons] using hsub)
    have hz := (original_U5_warm_rosser_prefix_admissible R bank b hb hN ht enum 0 H hparent hpass.1).1
    obtain ⟨hadm, hg⟩ := original_U5_warm_rosser_admission R bank b hb hN ht enum 0 H q hsub hpass.1
    have hh := hg.mp hpass.2
    have hq := hsub.subset (List.mem_reverse.mpr (List.mem_cons_self (a := q) (l := H)))
    have hsort : (q :: H).Pairwise (· < ·) := by
      simpa only [List.pairwise_reverse] using (roughPrimeUniverse_pairwise_gt N enum 0 (cutoff N)).sublist hsub
    rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix true _ H (evenListLength H) q
      hadm rfl (mem_roughPrimeUniverse_prime hq) (fun _ => (mem_roughPrimeUniverse_upper hq).trans hz) hsort] at hh
    exact of_decide_eq_true hh

private theorem previous_ancestor {k : ℕ} {H : List ℕ} (hlen : H.length = k+1) :
    rosserAncestor k H = H.tail := by
  cases H with
  | nil => simp at hlen
  | cons q H =>
    have hH : H.length = k := by simp only [List.length_cons] at hlen; omega
    exact (rosserAncestor_cons k q H hH.ge).trans (rosserAncestor_self_of_length k H hH)

private theorem refreeze_previous_stage (k : ℕ) (Q : List ℕ → ℝ) :
    firstExitDepthSplicePolicy (k+1) (incomingGate Q)
      (frozenParityRosserPolicy true (k+1) (fun H => Q (rosserAncestor k H))) = stage k Q := by
  rw [frozenParityRosserPolicy_nested true k (k+1) (by omega) Q]
  funext positive H
  by_cases hsmall : H.length ≤ k
  · have hnext : H.length ≤ k+1 := by omega
    simp only [stage, firstExitDepthSplicePolicy, if_pos hnext, if_pos hsmall]
  · by_cases hnext : H.length ≤ k+1
    · have hlen : H.length = k+1 := by omega
      simp only [stage, firstExitDepthSplicePolicy, if_pos hnext, if_neg hsmall,
        incomingGate, frozenParityRosserPolicy, ancestorFrozenPolicy, previous_ancestor hlen]
    · simp only [stage, firstExitDepthSplicePolicy, if_neg hnext, if_neg hsmall]

private theorem stage_zero (Q : List ℕ → ℝ) : stage 0 Q = ordinaryParityRosserPolicy true (Q []) := by
  funext positive H
  cases H with
  | nil => rfl
  | cons q H =>
    have hlen : ¬(q :: H).length ≤ 0 := by simp
    simp only [stage, firstExitDepthSplicePolicy, if_neg hlen, frozenParityRosserPolicy,
      ancestorFrozenPolicy, rosserAncestor_zero]

private theorem level_after_three (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (H : List ℕ) :
    rowLevel R bank b N t (rosserAncestor 3 H) = rowLevel R bank b N t H := by
  induction H with
  | nil => rfl
  | cons q H ih =>
    by_cases hlong : 3 ≤ H.length
    · have hc : (incoming R bank b N t (q :: H)).cap = (incoming R bank b N t H).cap := by
        simp only [incoming, List.reverse_cons, actualTrace_snoc]
        apply no_new_cap_outside_345
        simp only [actualTrace_word, List.length_append, List.length_cons, List.length_nil,
          List.length_map, List.length_reverse]
        omega
      rw [rosserAncestor_cons 3 q H hlong, ih]
      unfold rowLevel
      rw [hc]
    · exact congrArg (rowLevel R bank b N t) (rosserAncestor_self_of_length_le 3 (q :: H)
        (by simp only [List.length_cons]; omega))

private theorem stage_three (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) :
    stage 3 (rowLevel R bank b N t) = incomingGate (rowLevel R bank b N t) := by
  funext positive H
  by_cases hshort : H.length ≤ 3
  · simp only [stage, firstExitDepthSplicePolicy, if_pos hshort]
  · cases H with
    | nil => simp at hshort
    | cons q H =>
      have hlong : 3 ≤ H.length := by simp only [List.length_cons] at hshort; omega
      simp only [stage, firstExitDepthSplicePolicy, if_neg hshort, incomingGate, List.tail_cons,
        frozenParityRosserPolicy, ancestorFrozenPolicy, rosserAncestor_cons 3 q H hlong,
        level_after_three R bank b N t H]

/-- Signed change of the full lower polynomial after a retained rough rank.
The state list keeps its multiplicities. Both residuals are strictly below
the last prime and divide their pair-normalized level by the same rough product. -/
def frontierChange (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (N : ℕ) (t : ℕ × ℕ) (enum k : ℕ) : ℝ :=
  ((firstExitDepthFrontier k (evenFirstExitPolicy (selectedPolicy R bank b false N t))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N enum 0 (cutoff N))).map
    (fun s => actualFrozenFrontierDensityTerm true N enum (rowLevel R bank b N t) s.selectedPrefix -
      actualFrozenFrontierDensityTerm true N enum (fun H => rowLevel R bank b N t H.tail)
        s.selectedPrefix)).sum

private theorem stage_difference (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (enum k : ℕ) :
    firstExitRetainedPolynomial (stage (k+1) (rowLevel R bank b N t)) weight [] true 1
        (roughPrimeUniverse N enum 0 (cutoff N)) -
      firstExitRetainedPolynomial (stage k (rowLevel R bank b N t)) weight [] true 1
        (roughPrimeUniverse N enum 0 (cutoff N)) = frontierChange R bank b N t enum (k+1) := by
  let Q := rowLevel R bank b N t
  let U := roughPrimeUniverse N enum 0 (cutoff N)
  have hfront : firstExitDepthFrontier (k+1) (incomingGate Q) weight [] true 1 U =
      firstExitDepthFrontier (k+1) (selectedTree R bank b N t) weight [] true 1 U :=
    (selected_tree_comparison R bank b hb hN ht enum (k+1) weight U [] 1 (List.Sublist.refl _) rfl).2.symm
  have hvalid (s : FirstExitDepthState ℕ)
      (hs : s ∈ firstExitDepthFrontier (k+1) (incomingGate Q) weight [] true 1 U) :
      ordinaryRosserPrefixAdmissible true (Q (rosserAncestor k s.selectedPrefix)) s.selectedPrefix ∧
        ordinaryRosserPrefixAdmissible true (Q s.selectedPrefix) s.selectedPrefix := by
    rw [hfront] at hs
    have hl := firstExitDepthFrontier_selected_length (k+1) _ weight [] U true 1 (by simp) s hs
    rw [previous_ancestor hl]
    exact original_U5_selected_frontier_admissible R bank b hb hN ht enum (k+1) weight s hs
  have hx := firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum true (k+1)
    (by omega) (incomingGate Q) (fun H => Q (rosserAncestor k H)) Q N enum (cutoff N)
    (fun s hs => (hvalid s hs).1) (fun s hs => (hvalid s hs).2)
  rw [refreeze_previous_stage, hfront] at hx
  calc
    _ = ((firstExitDepthFrontier (k+1) (selectedTree R bank b N t) weight [] true 1 U).map
      (fun s => actualFrozenFrontierDensityTerm true N enum Q s.selectedPrefix -
        actualFrozenFrontierDensityTerm true N enum (fun H => Q (rosserAncestor k H)) s.selectedPrefix)).sum := hx
    _ = _ := by
      unfold frontierChange
      apply congrArg List.sum
      apply List.map_congr_left
      intro s hs
      have hl := firstExitDepthFrontier_selected_length (k+1) _ weight [] U true 1 (by simp) s hs
      simp only [actualFrozenFrontierDensityTerm, previous_ancestor hl, Q]

/-- The literal selected-policy polynomial is its ordinary buffered root
plus the full-rank three, four and five changes, for every enumeration cap. -/
theorem original_U5_three_frontier_retained_polynomial (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (enum : ℕ) :
    evenFirstExitRetainedPolynomial (selectedPolicy R bank b false N t)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N enum 0 (cutoff N)) =
      actualSmallRosserMinusDensity N enum (cutoff N) (rowLevel R bank b N t []) +
        frontierChange R bank b N t enum 1 + frontierChange R bank b N t enum 2 +
        frontierChange R bank b N t enum 3 := by
  let Q := rowLevel R bank b N t
  let U := roughPrimeUniverse N enum 0 (cutoff N)
  let A (k : ℕ) := firstExitRetainedPolynomial (stage k Q) weight [] true 1 U
  have h0 : A 0 = actualSmallRosserMinusDensity N enum (cutoff N) (Q []) := by
    dsimp only [A]
    rw [stage_zero]
    have hc := (original_U5_warm_rosser_prefix_admissible R bank b hb hN ht enum 0 [] (by simp) rfl).1
    have hz : 1 ≤ cutoff N := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
    exact firstExitRetainedPolynomial_ordinaryParityRosser_eq_actualDensity true N enum (cutoff N)
      (Q []) (hz.trans_lt hc) (fun _ => hc.le)
  have h3 : evenFirstExitRetainedPolynomial (selectedPolicy R bank b false N t) weight U = A 3 := by
    dsimp only [A, Q]
    rw [stage_three]
    exact (selected_tree_comparison R bank b hb hN ht enum 3 weight U [] 1 (List.Sublist.refl _) rfl).1
  have d1 : A 1 - A 0 = frontierChange R bank b N t enum 1 := stage_difference R bank b hb hN ht enum 0
  have d2 : A 2 - A 1 = frontierChange R bank b N t enum 2 := stage_difference R bank b hb hN ht enum 1
  have d3 : A 3 - A 2 = frontierChange R bank b N t enum 3 := stage_difference R bank b hb hN ht enum 2
  calc
    _ = A 3 := h3
    _ = A 0 + (A 1 - A 0) + (A 2 - A 1) + (A 3 - A 2) := by ring
    _ = _ := by rw [d1, d2, d3, h0]

/-- Exact original finite density on its full target-deleted prime carrier. -/
theorem original_U5_fullDensity_eq_three_frontiers (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (b : ℚ) (hb : b ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    fullDensity N (selectedPolicy R bank b false N t) =
      actualSmallRosserMinusDensity N (Nat.ceil (cutoff N)) (cutoff N) (rowLevel R bank b N t []) +
        frontierChange R bank b N t (Nat.ceil (cutoff N)) 1 +
        frontierChange R bank b N t (Nat.ceil (cutoff N)) 2 +
        frontierChange R bank b N t (Nat.ceil (cutoff N)) 3 := by
  calc
    _ = evenFirstExitRetainedPolynomial (selectedPolicy R bank b false N t) weight
        (roughPrimeUniverse N (Nat.ceil (cutoff N)) 0 (cutoff N)) :=
      (evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity _ N _ 0 (cutoff N)).symm
    _ = _ := original_U5_three_frontier_retained_polynomial R bank b hb hN ht _

end
end ImbalancedChen.P3OriginalU5ThreeFrontierIdentity
