import ImbalancedChen.P1CommonFifthElevenActualUpperGuard
import ImbalancedChen.OriginalFifthRetainedSelectedTailSupport
import ImbalancedChen.P1OriginalProducerAttainedRowBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An actual improving sixth finite maximum constructs its winning original
cell; the chosen mask is THAT winner's mask, not any eligible candidate's.
At the actual common policy6 source the same current Q6 pays full support,
selected/complement support and EVERY retained tail square. The exact
selected product and full product, plus the selected critical interval, are
proved from the original source gates. No hSupport, hTail, hWinner or
actualParent<=oldCap is assumed by the supported-source caller.

This is the sixth stage BEFORE the eighth replacement. Through rank eight
the final frontier is identical; deeper final tails may read a later cap
and are not identified with this sixth source.
-/

namespace ImbalancedChen.P1ActualCommonSixthWinnerSelectedTail

noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open Certificates.P2OriginalSixthElevenLogSemantics
open P1CommonFifthElevenActualUpperGuard

def selectedSlots6 (c : Cell) : List (Fin 6) :=
  if c.selectedMask = 34 then [1, 5]
  else if c.selectedMask = 50 then [1, 4, 5] else [0, 5]

def remainderSlots6 (c : Cell) : List (Fin 6) :=
  if c.selectedMask = 34 then [0, 2, 3, 4]
  else if c.selectedMask = 50 then [0, 2, 3] else [1, 2, 3, 4]

def selectedSet6 (c : Cell) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => bit c.selectedMask i.val = true)

def selectedProduct6 (c : Cell) (p : Fin 6 → ℕ) : ℕ := ((selectedSlots6 c).map p).prod
def remainderPrimes6 (c : Cell) (p : Fin 6 → ℕ) : List ℕ := (remainderSlots6 c).map p

theorem selected_product_eq_finset (c : Cell) (p : Fin 6 → ℕ) :
    selectedProduct6 c p = ∏ i ∈ selectedSet6 c, p i := by
  cases c <;> norm_num [selectedProduct6, selectedSlots6, selectedSet6, Cell.selectedMask,
    bit, Finset.prod_filter, Fin.prod_univ_succ] <;> ring

theorem selected_times_remaining6 (c : Cell) (p : Fin 6 → ℕ) :
    selectedProduct6 c p * (remainderPrimes6 c p).prod = (List.ofFn p).prod := by
  cases c <;> norm_num [selectedProduct6, selectedSlots6, remainderPrimes6, remainderSlots6,
    Cell.selectedMask, List.prod_ofFn, Fin.prod_univ_succ] <;> ring

theorem selected_product6_pos (c : Cell) (p : Fin 6 → ℕ) (hp : ∀ i, 0 < p i) :
    0 < selectedProduct6 c p := by
  apply List.prod_pos
  intro q hq
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hq
  exact hp i

private theorem remaining6_square_support (c : Cell) (p : Fin 6 → ℕ) (D : ℝ)
    (hg : ∀ q : Fin 6, bit c.selectedMask q.val = false →
      ((∏ a ∈ Finset.univ.filter (fun a => a < q ∧ bit c.selectedMask a.val = false),
        p a : ℕ) : ℝ) * (p q : ℝ) ^ 2 ≤ D) :
    actualDwellSupport D (remainderPrimes6 c p) := by
  intro i hi
  cases c <;> simp [remainderPrimes6, remainderSlots6, Cell.selectedMask] at hi ⊢
  all_goals interval_cases i
  all_goals first
    | simpa [Cell.selectedMask, bit, Finset.prod_filter, Fin.prod_univ_succ,
        mul_assoc, mul_comm, mul_left_comm] using hg (0 : Fin 6) (by decide)
    | simpa [Cell.selectedMask, bit, Finset.prod_filter, Fin.prod_univ_succ,
        mul_assoc, mul_comm, mul_left_comm] using hg (1 : Fin 6) (by decide)
    | simpa [Cell.selectedMask, bit, Finset.prod_filter, Fin.prod_univ_succ,
        mul_assoc, mul_comm, mul_left_comm] using hg (2 : Fin 6) (by decide)
    | simpa [Cell.selectedMask, bit, Finset.prod_filter, Fin.prod_univ_succ,
        mul_assoc, mul_comm, mul_left_comm] using hg (3 : Fin 6) (by decide)
    | simpa [Cell.selectedMask, bit, Finset.prod_filter, Fin.prod_univ_succ,
        mul_assoc, mul_comm, mul_left_comm] using hg (4 : Fin 6) (by decide)

private theorem validSelection_sixth_to_final (d : OriginalData) (N : ℝ) (hN : 1 ≤ N)
    (chosen pre : List ℕ) (positive : Bool)
    (h : FirstExitValidSelection (policy6 d N) pre positive chosen) :
    FirstExitValidSelection (policy8 d N) pre positive chosen := by
  induction chosen generalizing pre positive with
  | nil => trivial
  | cons p ps ih =>
      exact ⟨sixth_approval_preserved_by_eighth d N hN (!positive) (p :: pre) h.1,
        ih (p :: pre) (!positive) h.2⟩

/-- A real sixth-stage frontier yields a final retained word with exactly
the same history; this is causal approval transport, not signed monotonicity. -/
theorem sixth_frontier_has_final_same_history (d : OriginalData) (N : ℝ) (hN : 1 ≤ N)
    (k : ℕ) (weight : ℕ → ℝ) (carrier : List ℕ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier k (policy6 d N) weight [] true 1 carrier) :
    ∃ leaf ∈ firstExitRetainedLeaves (policy8 d N) weight [] true 1 carrier,
      leaf.selected = s.selectedPrefix := by
  let oldLeaf : FirstExitLeaf ℕ := ⟨s.selectedPrefix, s.positive, s.mass⟩
  have hold : oldLeaf ∈ firstExitRetainedLeaves (policy6 d N) weight [] true 1 carrier :=
    firstExitDepthFrontier_toLeaf_mem k (policy6 d N) weight [] carrier true 1 s hs
  obtain ⟨chosen, hsub, hvalid, heq⟩ := exists_validSelection_of_mem_firstExitRetainedLeaves
    (policy6 d N) weight [] carrier true 1 oldLeaf hold
  obtain ⟨leaf, hleaf, hselected⟩ := exists_firstExitRetainedLeaf_of_validSelection
    (policy8 d N) weight hsub [] true 1 (validSelection_sixth_to_final d N hN chosen [] true hvalid)
  exact ⟨leaf, hleaf, hselected.trans heq.symm⟩

/-- Every strict actual change constructs an attained ORIGINAL cell. The
seed branch remains separate. There is no caller-supplied winner label. -/
theorem actual_sixth_improvement_has_winner (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hchange : actualParent5 d N pre < lambda6 d N pre) :
    ∃ c : Cell, eligibleSixth d N c pre ∧
      lambda6 d N pre = newCap c (primeHistoryLogCoordinates N 6 pre) := by
  rcases P1OriginalProducerAttainedRowBinding.finiteMax_seed_or_winning_row
      allCells.toFinset (fun c => eligibleSixth d N c pre)
      (fun c => newCap c (primeHistoryLogCoordinates N 6 pre)) (actualParent5 d N pre)
      with hseed | hwinner
  · have hz : lambda6 d N pre = actualParent5 d N pre := hseed.1
    rw [hz] at hchange
    exact (lt_irrefl _ hchange).elim
  · obtain ⟨c, _hmem, helig, _hseed, _hmax, heq⟩ := hwinner
    exact ⟨c, helig, heq⟩

/-- Actual sixth-stage full support at its own frozen level; every prime,
order fact and complete ordinary test is supplied by the real carrier and
existing frontier-validity theorem, including inactive even ranks. -/
theorem actual_sixth_frontier_full_support
    (d : OriginalData) (N cap k : ℕ) (hk : 7 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier k (policy6 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z)) :
    actualDwellSupport ((N : ℝ) ^ lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix))
      s.selectedPrefix.reverse := by
  have hv := P4AActualSixthFrozenEighthAdmission.actual_frontier_admissible
    (policy5 d (N : ℝ)) (level6 d (N : ℝ)) k hk N cap w z weight s hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k (policy6 d (N : ℝ))
    weight (roughPrimeUniverse N cap w z) s hs
  exact Part3.ActualCompactAllRankSupport.upper_set_dwell_support s.selectedPrefix.reverse
    (fun p hp => mem_roughPrimeUniverse_prime (hsub.subset hp))
    ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub)
    (by simpa only [List.toFinset_reverse] using hv.2)

/-- The selected source gate is transported at the SAME attained Q6.
The complete tail uses original full-prefix products, then exact selected
factor cancellation; it is never assigned the old/current comparison cap. -/
theorem attained_sixth_selected_tail_support
    (d : OriginalData) (N cap k : ℕ) (hN : 1 < N) (hk : 6 ≤ k)
    (w z : ℝ) (weight : ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier k (policy6 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (c : Cell) (helig : eligibleSixth d (N : ℝ) c (rosserAncestor 6 s.selectedPrefix))
    (hwin : lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) =
      newCap c (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 s.selectedPrefix))) :
    let p := primeHistoryTuple 6 (rosserAncestor 6 s.selectedPrefix)
    let tail := s.selectedPrefix.reverse.drop 6
    let Q := (N : ℝ) ^ lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix)
    let B := selectedProduct6 c p
    0 < B ∧ actualDwellSupport Q s.selectedPrefix.reverse ∧
      actualDwellSupport (Q / (B : ℝ)) (remainderPrimes6 c p ++ tail) ∧
      B * (remainderPrimes6 c p ++ tail).prod = s.selectedPrefix.prod ∧
      (N : ℝ) ^ (2 * lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) - 1) < (B : ℝ) ∧
      (B : ℝ) < (N : ℝ) ^ ((2 / 3 : ℝ) *
        (57 / 64 - lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix))) := by
  dsimp only
  let a := rosserAncestor 6 s.selectedPrefix
  let p := primeHistoryTuple 6 a
  let t := primeHistoryLogCoordinates (N : ℝ) 6 a
  let tail := s.selectedPrefix.reverse.drop 6
  let B := selectedProduct6 c p
  let Q := (N : ℝ) ^ lambda6 d (N : ℝ) a
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlen := firstExitDepthFrontier_selected_length k _ weight []
    (roughPrimeUniverse N cap w z) true 1 (by simp) s hs
  have ha : a.length = 6 := by simp only [a, rosserAncestor_length, hlen]; omega
  have hfront : List.ofFn p = s.selectedPrefix.reverse.take 6 := by
    rw [primeHistoryTuple_ofFn ha]
    simp only [a, rosserAncestor, List.reverse_drop]
    congr 1
    omega
  have hsplit : List.ofFn p ++ tail = s.selectedPrefix.reverse := by
    rw [hfront]
    exact List.take_append_drop 6 s.selectedPrefix.reverse
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k (policy6 d (N : ℝ))
    weight (roughPrimeUniverse N cap w z) s hs
  have hpMem (i : Fin 6) : p i ∈ s.selectedPrefix.reverse := by
    apply (List.take_sublist 6 s.selectedPrefix.reverse).subset
    rw [← hfront]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hp : ∀ i, 0 < p i := fun i => (mem_roughPrimeUniverse_prime (hsub.subset (hpMem i))).pos
  have hapos : ∀ q ∈ a, 0 < q := by
    intro q hq
    have hq' : q ∈ s.selectedPrefix := (List.drop_sublist _ _).subset hq
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hq'))).pos
  have hcoord (i : Fin 6) : (p i : ℝ) ≤ (N : ℝ) ^ t i :=
    (rpow_primeHistoryLogCoordinates (N : ℝ) hNr ha hapos i).ge
  have hc : PhysicalCell c t := helig.2.1
  have hBnat : 0 < B := selected_product6_pos c p hp
  have hB : (0 : ℝ) < B := by exact_mod_cast hBnat
  have hfull6 : actualDwellSupport Q (List.ofFn p) := by
    intro i hi
    have hi6 : i < 6 := by simpa only [List.length_ofFn] using hi
    let q : Fin 6 := ⟨i, hi6⟩
    have hlog : prefixSquareExpr t q < newCap c t := by
      simpa [prefixSquareExpr, fullSquare, Finset.sum_filter] using hc.fullSquares q
    have hnat := prefixSquareExpr_actual_gate (N : ℝ) hNr p t hcoord q hlog
    have heq : Q = (N : ℝ) ^ newCap c t := congrArg (fun x : ℝ => (N : ℝ) ^ x) hwin
    rw [heq]
    simpa only [List.prod_take_ofFn, List.getElem_ofFn, actualNatList_cast_prod,
      Nat.cast_prod, Fin.lt_def] using hnat.le
  have hfullSource : actualDwellSupport Q s.selectedPrefix.reverse := by
    by_cases h7 : 7 ≤ k
    · exact actual_sixth_frontier_full_support d N cap k h7 w z weight s hs
    · have hk6 : k = 6 := by omega
      have hslen : s.selectedPrefix.length = 6 := by simpa only [hk6] using hlen
      have haself : a = s.selectedPrefix := rosserAncestor_self_of_length 6 s.selectedPrefix hslen
      have hwhole : List.ofFn p = s.selectedPrefix.reverse := by
        rw [primeHistoryTuple_ofFn ha, haself]
      rw [← hwhole]
      exact hfull6
  have hfinite : actualDwellSupport (Q / (B : ℝ)) (remainderPrimes6 c p) := by
    apply remaining6_square_support c p
    intro q hq
    have hlog : selectedSquareExpr (selectedSet6 c) t q < newCap c t := by
      simpa [selectedSquareExpr, selectedSet6, remainingSquare, selectedSum,
        Finset.sum_filter] using hc.remainingSquares q hq
    have hnat := selectedSquareExpr_actual_gate (selectedSet6 c) (N : ℝ) hNr p t hcoord q hlog
    rw [← selected_product_eq_finset c p] at hnat
    apply (le_div_iff₀ hB).mpr
    have heq : Q = (N : ℝ) ^ newCap c t := congrArg (fun x : ℝ => (N : ℝ) ^ x) hwin
    rw [heq]
    simpa only [selectedSet6, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.not_eq_true, mul_assoc, mul_comm, mul_left_comm] using hnat.le
  have hfull : actualDwellSupport Q (List.ofFn p ++ tail) := by
    rw [hsplit]
    exact hfullSource
  have hprodFront : B * (remainderPrimes6 c p).prod = (List.ofFn p).prod :=
    selected_times_remaining6 c p
  have hquot : actualDwellSupport (Q / (B : ℝ)) (remainderPrimes6 c p ++ tail) := by
    intro i hi
    by_cases hshort : i < (remainderPrimes6 c p).length
    · simpa only [List.take_append_of_le_length hshort.le,
        List.getElem_append_left hshort] using hfinite i hshort
    · let j := i - (remainderPrimes6 c p).length
      have hj : j < tail.length := by dsimp [j]; simp only [List.length_append] at hi; omega
      have hij : i = (remainderPrimes6 c p).length + j := by dsimp [j]; omega
      have ht := actualDwell_original_tail_square (List.ofFn p) tail hfull j hj
      have hid : ((List.ofFn p).prod : ℝ) = (B : ℝ) * ((remainderPrimes6 c p).prod : ℝ) := by
        exact_mod_cast hprodFront.symm
      rw [hid] at ht
      rw [hij]
      have htake : (remainderPrimes6 c p ++ tail).take ((remainderPrimes6 c p).length + j) =
          remainderPrimes6 c p ++ tail.take j := by
        rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
      have hget : (remainderPrimes6 c p ++ tail)[(remainderPrimes6 c p).length + j] = tail[j] := by
        simpa only [Nat.add_comm] using (List.getElem_append_right' (remainderPrimes6 c p) hj).symm
      rw [htake, hget, List.map_append, List.prod_append, actualNatList_cast_prod]
      apply (le_div_iff₀ hB).mpr
      simpa only [mul_assoc, mul_comm, mul_left_comm] using ht
  have hBpow : (B : ℝ) = (N : ℝ) ^ selectedSum c.selectedMask t := by
    have hsum : selectedSum c.selectedMask t = ∑ i ∈ selectedSet6 c, t i := by
      simp only [selectedSum, selectedSet6, Finset.sum_filter]
    rw [selected_product_eq_finset, hsum, Nat.cast_prod, Real.rpow_sum_of_pos hNpos]
    apply Finset.prod_congr rfl
    intro i _hi
    exact (rpow_primeHistoryLogCoordinates (N : ℝ) hNr ha hapos i).symm
  refine ⟨hBnat, hfullSource, hquot, ?_, ?_, ?_⟩
  · rw [List.prod_append, ← mul_assoc, hprodFront]
    simpa only [List.prod_append, List.prod_reverse] using congrArg List.prod hsplit
  · rw [hBpow]
    apply (Real.rpow_lt_rpow_left_iff hNr).mpr
    rw [hwin]
    linarith [hc.selectedAscending]
  · rw [hBpow]
    apply (Real.rpow_lt_rpow_left_iff hNr).mpr
    rw [hwin]
    linarith [hc.selectedDescending]

/-- The caller is the REAL common sixth frontier, not a supplied licence.
One original PhysicalCell plus its genuine third-support witness constructs
both parent guards, strict improvement, an actual winner, and the complete
selected/tail licence at the winner's OWN frozen Q6 and mask. -/
theorem actual_supported_sixth_winner_licence
    (d : OriginalData) (N cap k : ℕ) (hN : 1 < N) (he : 0 ≤ d.e) (hk : 6 ≤ k)
    (w z : ℝ) (weight : ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier k (policy6 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (c0 : Cell)
    (hc0 : PhysicalCell c0
      (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 s.selectedPrefix)))
    (hsThird : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      (rosserAncestor 3 s.selectedPrefix)) :
    ∃ c : Cell, eligibleSixth d (N : ℝ) c (rosserAncestor 6 s.selectedPrefix) ∧
      lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) =
        newCap c (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 s.selectedPrefix)) ∧
      let p := primeHistoryTuple 6 (rosserAncestor 6 s.selectedPrefix)
      let B := selectedProduct6 c p
      let tail := s.selectedPrefix.reverse.drop 6
      let Q := (N : ℝ) ^ lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix)
      0 < B ∧ actualDwellSupport Q s.selectedPrefix.reverse ∧
        actualDwellSupport (Q / (B : ℝ)) (remainderPrimes6 c p ++ tail) ∧
        B * (remainderPrimes6 c p ++ tail).prod = s.selectedPrefix.prod ∧
        (N : ℝ) ^ (2 * lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) - 1) < (B : ℝ) ∧
        (B : ℝ) < (N : ℝ) ^ ((2 / 3 : ℝ) *
          (57 / 64 - lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix))) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlen := firstExitDepthFrontier_selected_length k _ weight []
    (roughPrimeUniverse N cap w z) true 1 (by simp) s hs
  obtain ⟨leaf, hleaf, hselected⟩ := sixth_frontier_has_final_same_history d (N : ℝ)
    hNr.le k weight (roughPrimeUniverse N cap w z) s hs
  have hcLeaf : PhysicalCell c0
      (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 leaf.selected)) := by
    rwa [hselected]
  have hsLeaf : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      (rosserAncestor 3 leaf.selected) := by rwa [hselected]
  have helig0 := final_supported_source_eligibleSixth d N cap hNr he w z weight leaf hleaf
    (by rw [hselected, hlen]; omega) c0 hcLeaf hsLeaf
  rw [hselected] at helig0
  have hchange := (eligibleSixth_actualParent_lt_newCap d (N : ℝ) c0
    (rosserAncestor 6 s.selectedPrefix) helig0).trans_le
      (eligibleSixth_newCap_le_lambda6 d (N : ℝ) c0 (rosserAncestor 6 s.selectedPrefix) helig0)
  obtain ⟨c, helig, hwin⟩ := actual_sixth_improvement_has_winner d (N : ℝ)
    (rosserAncestor 6 s.selectedPrefix) hchange
  have hsupport := attained_sixth_selected_tail_support d N cap k hN hk w z weight s hs c helig hwin
  exact ⟨c, helig, hwin, hsupport⟩

/-- Exhaustive source alternative for the independent actual supplier.
Seed equality means this stage inherits its actual parent; it does not
mean that a signed source contribution vanishes. Every genuine changed
branch constructs its own winner and complete physical selected/tail
support, without any guard or support conclusion supplied as a premise. -/
theorem actual_sixth_frontier_seed_or_winner_licence
    (d : OriginalData) (N cap k : ℕ) (hN : 1 < N) (hk : 6 ≤ k)
    (w z : ℝ) (weight : ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier k (policy6 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z)) :
    lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) =
      actualParent5 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ∨
    ∃ c : Cell, eligibleSixth d (N : ℝ) c (rosserAncestor 6 s.selectedPrefix) ∧
      lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) =
        newCap c (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 s.selectedPrefix)) ∧
      let p := primeHistoryTuple 6 (rosserAncestor 6 s.selectedPrefix)
      let B := selectedProduct6 c p
      let tail := s.selectedPrefix.reverse.drop 6
      let Q := (N : ℝ) ^ lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix)
      0 < B ∧ actualDwellSupport Q s.selectedPrefix.reverse ∧
        actualDwellSupport (Q / (B : ℝ)) (remainderPrimes6 c p ++ tail) ∧
        B * (remainderPrimes6 c p ++ tail).prod = s.selectedPrefix.prod ∧
        (N : ℝ) ^ (2 * lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) - 1) < (B : ℝ) ∧
        (B : ℝ) < (N : ℝ) ^ ((2 / 3 : ℝ) *
          (57 / 64 - lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix))) := by
  by_cases hsame : lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) =
      actualParent5 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix)
  · exact Or.inl hsame
  · have hchange : actualParent5 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) <
        lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) :=
      lt_of_le_of_ne (actualParent5_le_lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix))
        (fun h => hsame h.symm)
    obtain ⟨c, helig, hwin⟩ := actual_sixth_improvement_has_winner d (N : ℝ)
      (rosserAncestor 6 s.selectedPrefix) hchange
    exact Or.inr ⟨c, helig, hwin,
      attained_sixth_selected_tail_support d N cap k hN hk w z weight s hs c helig hwin⟩

/-- The actual final rank-eight source is still the same sixth-stage
frontier. This exact structural identity permits this application; it
does not license arbitrarily deep final tails at the earlier Q6. -/
theorem actual_final_rank8_sixth_selected_tail
    (d : OriginalData) (N cap : ℕ) (hN : 1 < N) (he : 0 ≤ d.e)
    (w z : ℝ) (weight : ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8 (policy8 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (c0 : Cell)
    (hc0 : PhysicalCell c0
      (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 s.selectedPrefix)))
    (hsThird : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      (rosserAncestor 3 s.selectedPrefix)) :
    ∃ c : Cell, eligibleSixth d (N : ℝ) c (rosserAncestor 6 s.selectedPrefix) ∧
      lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) =
        newCap c (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 s.selectedPrefix)) ∧
      let p := primeHistoryTuple 6 (rosserAncestor 6 s.selectedPrefix)
      let B := selectedProduct6 c p
      let tail := s.selectedPrefix.reverse.drop 6
      let Q := (N : ℝ) ^ lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix)
      0 < B ∧ actualDwellSupport Q s.selectedPrefix.reverse ∧
        actualDwellSupport (Q / (B : ℝ)) (remainderPrimes6 c p ++ tail) ∧
        B * (remainderPrimes6 c p ++ tail).prod = s.selectedPrefix.prod ∧
        (N : ℝ) ^ (2 * lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) - 1) < (B : ℝ) ∧
        (B : ℝ) < (N : ℝ) ^ ((2 / 3 : ℝ) *
          (57 / 64 - lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix))) := by
  have hsource : s ∈ firstExitDepthFrontier 8 (policy6 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z) := by
    rwa [P5OriginalCommonRefinedAncestry.policy8_frontier_eight_eq_six] at hs
  exact actual_supported_sixth_winner_licence d N cap 8 hN he (by decide) w z weight s
    hsource c0 hc0 hsThird

end
end ImbalancedChen.P1ActualCommonSixthWinnerSelectedTail
