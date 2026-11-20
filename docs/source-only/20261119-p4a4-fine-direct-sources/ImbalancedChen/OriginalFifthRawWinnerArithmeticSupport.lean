import ImbalancedChen.OriginalFifthRawPositionalJointOwnership

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

Arithmetic support of the NONSEED original raw positional fifth winner.
The existing log-to-natural square bridge is reused. The new conclusion
is attached to the SAME attained variable Q5: exact selected/remainder
factorization, quotient remaining-square budget, and the buffered selected
product critical interval. No old fifth own-cube pass is a premise.
This is arithmetic geometry, not a distribution license or archive replay.
-/

namespace ImbalancedChen.OriginalFifthRawWinnerArithmeticSupport20261026b

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

def selectedFactor (I : Finset (Fin 5)) (p : Fin 5 → ℕ) : ℕ := ∏ q ∈ I, p q

def remainingFactor (I : Finset (Fin 5)) (p : Fin 5 → ℕ) : ℕ :=
  ∏ q ∈ Finset.univ.filter (fun q => q ∉ I), p q

theorem selected_mul_remaining (I : Finset (Fin 5)) (p : Fin 5 → ℕ) :
    selectedFactor I p * remainingFactor I p = ∏ q, p q := by
  have hI : Finset.univ.filter (fun q : Fin 5 => q ∈ I) = I := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun q : Fin 5 => q ∈ I) p
  simpa only [hI, selectedFactor, remainingFactor] using h

theorem selectedFactor_pos (I : Finset (Fin 5)) (p : Fin 5 → ℕ)
    (hp : ∀ q, 0 < p q) : 0 < selectedFactor I p :=
  Finset.prod_pos (fun q _hq => hp q)

theorem selectedFactor_eq_rpow (I : Finset (Fin 5)) (N : ℕ) (hN : 1 < N)
    (p : Fin 5 → ℕ) (hp : ∀ q, 0 < p q) :
    (selectedFactor I p : ℝ) = (N : ℝ) ^ (∑ q ∈ I, actualPrimeTupleLog N p q) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  rw [selectedFactor, Nat.cast_prod, Real.rpow_sum_of_pos (zero_lt_one.trans hNr)]
  apply Finset.prod_congr rfl
  intro q _hq
  exact (actualPrimeTupleLog_rpow hN p hp q).symm

/-- Both the fourth parent and fifth raw winner are attained at this
actual prime tuple. Thus no chosen row or surrogate old cap is assumed. -/
theorem attained_exponent_eq_raw_candidate
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Label5 m))
    (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (N : ℕ) (hN : 1 < N)
    (p : Fin 5 → ℕ) (hp : ∀ q, 0 < p q)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (parent : ParentPosition records4)
    (hparent : parentOwner records4 e m j licensed (actualPrimeTupleLog N p) = parent)
    (k : Fin records5.length)
    (hwin : fifthOwner records4 records5 e m j parent (actualPrimeTupleLog N p) = k.succ) :
    exponent5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5
        (fifthFamily records5 m) (P1CorrectedFifthCausalTupleDictionary.tupleHistory p) =
      candidate (e : ℝ) (rawRowAt records5 m j k).selected (actualPrimeTupleLog N p) := by
  have hv := owner_value records4 records5 e m j parent (actualPrimeTupleLog N p)
  rw [hwin] at hv
  have hv' : candidate (e : ℝ) (rawRowAt records5 m j k).selected (actualPrimeTupleLog N p) =
      nextFromParent records4 records5 e m j parent (actualPrimeTupleLog N p) := by
    simpa only [slotValue, Fin.cases_succ] using hv
  rw [exponent5_on_selected_owner e chi m omega (fourthFamily records4) licensed J5
    (fifthFamily records5 m) N hN p hp j hj ht,
    actualNext5_eq_nextFromParent records4 records5 e chi m omega J5 j hj licensed
      (actualPrimeTupleLog N p) ht parent hparent]
  exact hv'.symm

/-- Exact full and grouped selected arithmetic support at the SAME Q5.
The tuple may have failed its inherited fourth-level fifth own-cube test;
that test is deliberately absent from the hypotheses. -/
theorem nonseed_winner_arithmetic_support
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Label5 m))
    (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (N : ℕ) (hN : 1 < N)
    (p : Fin 5 → ℕ) (hp : ∀ q, Nat.Prime (p q))
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (parent : ParentPosition records4)
    (hparent : parentOwner records4 e m j licensed (actualPrimeTupleLog N p) = parent)
    (k : Fin records5.length)
    (hwin : fifthOwner records4 records5 e m j parent (actualPrimeTupleLog N p) = k.succ) :
    let I := (rawRowAt records5 m j k).selected
    let history := P1CorrectedFifthCausalTupleDictionary.tupleHistory p
    let lambda := exponent5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5
      (fifthFamily records5 m) history
    let Q := level5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5
      (fifthFamily records5 m) history
    0 < selectedFactor I p ∧
      selectedFactor I p * remainingFactor I p = ∏ q, p q ∧
      (∀ q, ((∏ a ∈ Finset.univ.filter (fun a => a < q), p a : ℕ) : ℝ) *
        (p q : ℝ) ^ 2 < Q) ∧
      (∀ q ∉ I, (selectedFactor I p : ℝ) *
        ((∏ a ∈ Finset.univ.filter (fun a => a < q ∧ a ∉ I), p a : ℕ) : ℝ) *
          (p q : ℝ) ^ 2 < Q) ∧
      (∀ q ∉ I, ((∏ a ∈ Finset.univ.filter (fun a => a < q ∧ a ∉ I), p a : ℕ) : ℝ) *
        (p q : ℝ) ^ 2 < Q / (selectedFactor I p : ℝ)) ∧
      (N : ℝ) ^ (2 * lambda + 4 * (e : ℝ) - 1) ≤ (selectedFactor I p : ℝ) ∧
      (selectedFactor I p : ℝ) ≤
        (N : ℝ) ^ ((2 / 3 : ℝ) * (57 / 64 - lambda - 2 * (e : ℝ))) := by
  dsimp only
  let I := (rawRowAt records5 m j k).selected
  let t := actualPrimeTupleLog N p
  let lambda := exponent5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5
    (fifthFamily records5 m) (P1CorrectedFifthCausalTupleDictionary.tupleHistory p)
  let Q := level5 e chi m omega (N : ℝ) (fourthFamily records4) licensed J5
    (fifthFamily records5 m) (P1CorrectedFifthCausalTupleDictionary.tupleHistory p)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ q, 0 < p q := fun q => (hp q).pos
  have hcoord : ∀ q, (p q : ℝ) ≤ (N : ℝ) ^ t q := fun q =>
    (actualPrimeTupleLog_rpow hN p hpos q).ge
  have heq : lambda = candidate (e : ℝ) I t :=
    attained_exponent_eq_raw_candidate records4 records5 e chi m omega J5 j hj licensed
      N hN p hpos ht parent hparent k hwin
  have hg := owned_raw_geometry records4 records5 e m j parent t ht k hwin
  have hQ : Q = (N : ℝ) ^ candidate (e : ℝ) I t :=
    congrArg (fun a : ℝ => (N : ℝ) ^ a) heq
  have hfull (q : Fin 5) :
      ((∏ a ∈ Finset.univ.filter (fun a => a < q), p a : ℕ) : ℝ) * (p q : ℝ) ^ 2 < Q := by
    rw [hQ]
    exact prefixSquareExpr_actual_gate (N : ℝ) hNr p t hcoord q (hg.2.2.1 q)
  have hselected (q : Fin 5) (hq : q ∉ I) : (selectedFactor I p : ℝ) *
      ((∏ a ∈ Finset.univ.filter (fun a => a < q ∧ a ∉ I), p a : ℕ) : ℝ) *
        (p q : ℝ) ^ 2 < Q := by
    rw [hQ]
    exact selectedSquareExpr_actual_gate I (N : ℝ) hNr p t hcoord q (hg.2.2.2 q hq)
  have hBpos : (0 : ℝ) < selectedFactor I p := by
    exact_mod_cast selectedFactor_pos I p hpos
  have hB : (selectedFactor I p : ℝ) = (N : ℝ) ^ (∑ q ∈ I, t q) :=
    selectedFactor_eq_rpow I N hN p hpos
  have hlow : 2 * lambda + 4 * (e : ℝ) - 1 ≤ ∑ q ∈ I, t q := by
    have h := min_le_left ((1 + ∑ q ∈ I, t q) / 2)
      (57 / 64 - (3 / 2 : ℝ) * ∑ q ∈ I, t q)
    rw [candidate_eq_original_cap] at heq
    linarith
  have hhigh : (∑ q ∈ I, t q) ≤ (2 / 3 : ℝ) * (57 / 64 - lambda - 2 * (e : ℝ)) := by
    have h := min_le_right ((1 + ∑ q ∈ I, t q) / 2)
      (57 / 64 - (3 / 2 : ℝ) * ∑ q ∈ I, t q)
    rw [candidate_eq_original_cap] at heq
    linarith
  refine ⟨selectedFactor_pos I p hpos, selected_mul_remaining I p, hfull, hselected, ?_, ?_, ?_⟩
  · intro q hq
    apply (lt_div_iff₀ hBpos).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hselected q hq
  · rw [hB]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le hlow
  · rw [hB]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le hhigh

end
end ImbalancedChen.OriginalFifthRawWinnerArithmeticSupport20261026b
