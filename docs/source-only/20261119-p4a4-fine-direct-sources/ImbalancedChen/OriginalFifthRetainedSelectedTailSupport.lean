import ImbalancedChen.OriginalFifthRawWinnerArithmeticSupport
import ImbalancedChen.Part3ActualCompactAllRankSupport
import ImbalancedChen.ActualDwellSelectedRemainder

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

Actual retained tail support at the SAME original attained variable Q5.
The generic ordinary-set to native D-well supplier is reused unchanged.
The retained leaf supplies its chronological prime vector and complete
original Rosser predicate. Removing the selected fifth slots preserves
their literal remaining order; every later tail square retains the FULL
original preceding product. Exact selected-factor cancellation yields
the genuine grouped quotient budget before any allocation is performed.
No full-modulus bound, tail-support predicate, distribution estimate, or
archived parent chronology is assumed.
-/

namespace ImbalancedChen.OriginalFifthRetainedSelectedTailSupport20261026b

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1OriginalFifthAttainedRowBinding
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b
open OriginalFifthRawWinnerArithmeticSupport20261026b

abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

def remainingSlots (I : Finset (Fin 5)) : List (Fin 5) :=
  [0, 1, 2, 3, 4].filter (fun q => decide (q ∉ I))

def remainingPrimes (I : Finset (Fin 5)) (p : Fin 5 → ℕ) : List ℕ :=
  (remainingSlots I).map p

/-- Original processing order, including every unselected occurrence. -/
theorem remainingPrimes_product (I : Finset (Fin 5)) (p : Fin 5 → ℕ) :
    (remainingPrimes I p).prod = remainingFactor I p := by
  by_cases h0 : (0 : Fin 5) ∈ I <;> by_cases h1 : (1 : Fin 5) ∈ I <;>
    by_cases h2 : (2 : Fin 5) ∈ I <;> by_cases h3 : (3 : Fin 5) ∈ I <;>
    by_cases h4 : (4 : Fin 5) ∈ I
  all_goals simp [remainingPrimes, remainingSlots, remainingFactor,
    Finset.prod_filter, Fin.prod_univ_succ, h0, h1, h2, h3, h4]

/-- Exact bit-selected finite-prefix to native-list quotient transport.
The input gates are the original selected-square products, not new
unverified tests on a rearranged prime list. -/
theorem remainingPrimes_square_support (I : Finset (Fin 5)) (p : Fin 5 → ℕ) (D : ℝ)
    (hg : ∀ q ∉ I,
      ((∏ a ∈ Finset.univ.filter (fun a => a < q ∧ a ∉ I), p a : ℕ) : ℝ) *
        (p q : ℝ) ^ 2 ≤ D) : actualDwellSupport D (remainingPrimes I p) := by
  have g0 := hg 0
  have g1 := hg 1
  have g2 := hg 2
  have g3 := hg 3
  have g4 := hg 4
  intro k hk
  by_cases h0 : (0 : Fin 5) ∈ I <;> by_cases h1 : (1 : Fin 5) ∈ I <;>
    by_cases h2 : (2 : Fin 5) ∈ I <;> by_cases h3 : (3 : Fin 5) ∈ I <;>
    by_cases h4 : (4 : Fin 5) ∈ I
  all_goals simp [remainingPrimes, remainingSlots, h0, h1, h2, h3, h4] at hk ⊢
  all_goals interval_cases k <;>
    simp_all [Finset.prod_filter, Fin.prod_univ_succ, mul_assoc]

def retainedTail (leaf : FirstExitLeaf ℕ) : List ℕ := leaf.selected.reverse.drop 5

theorem fifthTuple_chronological_prefix (leaf : FirstExitLeaf ℕ)
    (hlen : 5 ≤ leaf.selected.length) :
    List.ofFn (fifthTuple leaf.selected) = leaf.selected.reverse.take 5 := by
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by
    rw [rosserAncestor_length]
    omega
  rw [fifthTuple, primeHistoryTuple_ofFn h5]
  simp only [rosserAncestor, List.reverse_drop]
  congr 1
  omega

theorem chronological_prefix_tail_split (leaf : FirstExitLeaf ℕ)
    (hlen : 5 ≤ leaf.selected.length) :
    List.ofFn (fifthTuple leaf.selected) ++ retainedTail leaf = leaf.selected.reverse := by
  rw [fifthTuple_chronological_prefix leaf hlen]
  exact List.take_append_drop 5 leaf.selected.reverse

/-- All original tail squares are obtained from actual retained-leaf
validity and the unchanged generic native supplier. Q5 is frozen at the
leaf's own original fifth ancestor, rather than enlarged to Theta. -/
theorem retained_native_support_at_actual_Q5
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap : ℕ) (w z : ℝ) (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ))
    (hN : 1 < (N : ℝ)) (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega (N : ℝ) rows4 licensed J5 rows5)
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (hlen : 5 ≤ leaf.selected.length) :
    actualDwellSupport
      (level5 e chi m omega (N : ℝ) rows4 licensed J5 rows5 (rosserAncestor 5 leaf.selected))
      leaf.selected.reverse := by
  have hv := P1OriginalHistoricalRetainedModulusLevel.actual_original_fifth_retained_leaf_valid
    (e : ℝ) chi m omega N cap w z
    (level5 e chi m omega (N : ℝ) rows4 licensed J5 rows5) heupper hN weight leaf hleaf
  rw [P1OriginalHistoricalRetainedModulusLevel.currentLevel_from_five
    (e : ℝ) chi m omega (N : ℝ) _ leaf.selected hlen] at hv
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using
      firstExitRetainedLeaves_selected_reverse_sublist
        (policy5 e chi m omega (N : ℝ) rows4 licensed J5 rows5)
        weight [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  apply Part3.ActualCompactAllRankSupport.upper_set_dwell_support leaf.selected.reverse
    (fun p hp => mem_roughPrimeUniverse_prime (hsub.subset hp))
    ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub)
  simpa only [List.toFinset_reverse] using hv.2

/-- The actual nonseed raw winner licenses the entire grouped complement
and retained tail at Q5/B, before deterministic factor allocation. The
selected chronological fifth prefix is exactly the one read by the tree. -/
theorem nonseed_retained_grouped_quotient_support
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Label5 m))
    (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < N)
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5 (fifthFamily records5 m))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (hlen : 5 ≤ leaf.selected.length)
    (ht : actualPrimeTupleLog N (fifthTuple leaf.selected) ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (parent : ParentPosition records4)
    (hparent : parentOwner records4 e m j licensed
      (actualPrimeTupleLog N (fifthTuple leaf.selected)) = parent)
    (k : Fin records5.length)
    (hwin : fifthOwner records4 records5 e m j parent
      (actualPrimeTupleLog N (fifthTuple leaf.selected)) = k.succ) :
    let p := fifthTuple leaf.selected
    let I := (rawRowAt records5 m j k).selected
    let Q := level5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5
      (fifthFamily records5 m) (rosserAncestor 5 leaf.selected)
    actualDwellSupport (Q / (selectedFactor I p : ℝ))
        (remainingPrimes I p ++ retainedTail leaf) ∧
      selectedFactor I p * (remainingPrimes I p ++ retainedTail leaf).prod = leaf.selected.prod := by
  dsimp only
  let p := fifthTuple leaf.selected
  let I := (rawRowAt records5 m j k).selected
  let Q := level5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5
    (fifthFamily records5 m) (rosserAncestor 5 leaf.selected)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using
      firstExitRetainedLeaves_selected_reverse_sublist
        (policy5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5 (fifthFamily records5 m))
        weight [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hfront : List.ofFn p <+ leaf.selected.reverse := by
    rw [fifthTuple_chronological_prefix leaf hlen]
    exact List.take_sublist 5 leaf.selected.reverse
  have hp : ∀ q, Nat.Prime (p q) := fun q => mem_roughPrimeUniverse_prime
    (hsub.subset (hfront.subset (List.mem_ofFn.mpr ⟨q, rfl⟩)))
  have h5 : (rosserAncestor 5 leaf.selected).length = 5 := by
    rw [rosserAncestor_length]
    omega
  have hh : P1CorrectedFifthCausalTupleDictionary.tupleHistory p = rosserAncestor 5 leaf.selected :=
    P1CorrectedFifthCausalTupleDictionary.tupleHistory_primeHistoryTuple _ h5
  have ha := nonseed_winner_arithmetic_support records4 records5 e chi m omega J5 j hj licensed
    N hN p hp ht parent hparent k hwin
  dsimp only at ha
  rw [hh] at ha
  have hfinite : actualDwellSupport (Q / (selectedFactor I p : ℝ)) (remainingPrimes I p) :=
    remainingPrimes_square_support I p _ (fun q hq => (ha.2.2.2.2.1 q hq).le)
  have hfull : actualDwellSupport Q (List.ofFn p ++ retainedTail leaf) := by
    rw [chronological_prefix_tail_split leaf hlen]
    exact retained_native_support_at_actual_Q5 e chi m omega (fourthFamily records4) licensed
      J5 (fifthFamily records5 m) N cap w z heupper hNr weight leaf hleaf hlen
  have hfrontprod : selectedFactor I p * (remainingPrimes I p).prod = (List.ofFn p).prod := by
    rw [remainingPrimes_product, selected_mul_remaining, List.prod_ofFn]
  have hBpos : (0 : ℝ) < selectedFactor I p := by
    exact_mod_cast selectedFactor_pos I p (fun q => (hp q).pos)
  constructor
  · intro a ha
    by_cases hshort : a < (remainingPrimes I p).length
    · have hs := hfinite a hshort
      simpa only [List.take_append_of_le_length hshort.le, List.getElem_append_left hshort] using hs
    · let b := a - (remainingPrimes I p).length
      have hb : b < (retainedTail leaf).length := by
        dsimp [b]
        simp only [List.length_append] at ha
        omega
      have hab : a = (remainingPrimes I p).length + b := by dsimp [b]; omega
      have hs := actualDwell_original_tail_square (List.ofFn p) (retainedTail leaf) hfull b hb
      have hid : ((List.ofFn p).prod : ℝ) =
          (selectedFactor I p : ℝ) * ((remainingPrimes I p).prod : ℝ) := by
        exact_mod_cast hfrontprod.symm
      rw [hid] at hs
      rw [hab]
      have htake : (remainingPrimes I p ++ retainedTail leaf).take
          ((remainingPrimes I p).length + b) = remainingPrimes I p ++ (retainedTail leaf).take b := by
        rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
      have hget : (remainingPrimes I p ++ retainedTail leaf)[(remainingPrimes I p).length + b] =
          (retainedTail leaf)[b] := by
        simpa only [Nat.add_comm] using (List.getElem_append_right' (remainingPrimes I p) hb).symm
      rw [htake, hget, List.map_append, List.prod_append, actualNatList_cast_prod]
      apply (le_div_iff₀ hBpos).mpr
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  · rw [List.prod_append, ← mul_assoc, hfrontprod]
    have hprod := congrArg List.prod (chronological_prefix_tail_split leaf hlen)
    simpa only [List.prod_append, List.prod_reverse] using hprod

end
end ImbalancedChen.OriginalFifthRetainedSelectedTailSupport20261026b
