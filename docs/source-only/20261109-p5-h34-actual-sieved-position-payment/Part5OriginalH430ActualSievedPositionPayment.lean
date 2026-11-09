import ImbalancedChen.Part5OriginalH430ActualUnpaidOrdinaryEnvelope

/-!
P5.6 -> h34: actual positive source receipts at a resolved historical
LIST POSITION, and a quantitative one-position upper bound for the
original arithmetic q-to-marked unpaid gap.

This is more precise than the ordinary whole-q-count fallback: a
genuinely positive source sieve at ONE actually resolved historical
position forces a strict reduction of the unpaid gap whenever the
original arithmetic receiver is nonempty. The term carries the exact
physical Q, original integer parent product, original positive path
mark, and literal source-sieve cutoff. Product collisions are not
quotiented away. This does NOT equate a historical product with an
original arithmetic quotient q or construct the H430 selected owner.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualSievedPositionPayment

noncomputable section

open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TrueCountMarkedGap
open Part5OriginalH430ActualResolvedMarkedPushforward
open Part5OriginalH430ActualUnpaidOrdinaryEnvelope
open P2EnhancedTwentyOneSameQWeighted

/-- One ORIGINAL resolved list-position contribution to the true
same-Q Phi. The integer parent product is d, never the quotient q. -/
def actualPositionPhiTerm
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n k tau p g) : ℝ :=
  let d := parentProduct (levelOccurrence l).current.old
  levelMark l * (sourceSieveCount N d (d * N)
    (cutoff (rootQ N n k tau p) d (11/5)) : ℝ)

/-- Every true historical occurrence has a nonnegative finite
positive-marked source contribution. No geometric cutoffs are assumed. -/
theorem actual_position_Phi_term_nonneg
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n k tau p g) :
    0 ≤ actualPositionPhiTerm N n k tau p g l := by
  dsimp [actualPositionPhiTerm]
  exact mul_nonneg (mark_pos (levelOccurrence l)).le (Nat.cast_nonneg _)

/-- A single REAL resolved occurrence cannot exceed the full
positive marked Phi, even if many distinct list indices have the
same physical integer product. This is a lower bound on actual Phi,
not an assignment of an arithmetic q receipt to the position. -/
theorem actual_position_Phi_term_le_full
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n k tau p g)
    (hl : l ∈ activePositions N n k tau p g) :
    actualPositionPhiTerm N n k tau p g l ≤
      Phi N (rootQ N n k tau p)
        (activeProductSupport N n k tau p g)
        (activeProductSigma N n k tau p g) (11/5) := by
  rw [activeProduct_Phi_exact]
  let F : Index N n k tau p g → ℝ :=
    fun j => actualPositionPhiTerm N n k tau p g j
  change F l ≤ ∑ j ∈ activePositions N n k tau p g, F j
  calc
    F l = ∑ j ∈ activePositions N n k tau p g,
      if j = l then F j else 0 := by simp [hl]
    _ ≤ ∑ j ∈ activePositions N n k tau p g, F j := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases heq : j = l
      · simp [heq]
      · simpa [heq] using
          (actual_position_Phi_term_nonneg N n k tau p g j)

/-- Exact finite support criterion. A resolved level can have
positive Theta and STILL have zero Phi: true Phi is zero precisely
when every selected historical position has zero ORIGINAL source
sieve cardinality at its physical cutoff. -/
theorem actual_Phi_zero_iff_all_sieved_positions_empty
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    Phi N (rootQ N n k tau p)
      (activeProductSupport N n k tau p g)
      (activeProductSigma N n k tau p g) (11/5) = 0 ↔
    ∀ l : Index N n k tau p g,
      l ∈ activePositions N n k tau p g →
      sourceSieveCount N
        (parentProduct (levelOccurrence l).current.old)
        ((parentProduct (levelOccurrence l).current.old) * N)
        (cutoff (rootQ N n k tau p)
          (parentProduct (levelOccurrence l).current.old) (11/5)) = 0 := by
  constructor
  · intro hzero l hl
    by_contra hcount
    have hcountpos :
        0 < sourceSieveCount N
          (parentProduct (levelOccurrence l).current.old)
          ((parentProduct (levelOccurrence l).current.old) * N)
          (cutoff (rootQ N n k tau p)
            (parentProduct (levelOccurrence l).current.old) (11/5)) :=
      Nat.pos_of_ne_zero hcount
    have hcast :
        0 < (sourceSieveCount N
          (parentProduct (levelOccurrence l).current.old)
          ((parentProduct (levelOccurrence l).current.old) * N)
          (cutoff (rootQ N n k tau p)
            (parentProduct (levelOccurrence l).current.old) (11/5)) : ℝ) := by
      exact_mod_cast hcountpos
    have hterm : 0 < actualPositionPhiTerm N n k tau p g l := by
      dsimp [actualPositionPhiTerm]
      exact mul_pos (mark_pos (levelOccurrence l)) hcast
    have hle := actual_position_Phi_term_le_full N n k tau p g l hl
    linarith
  · intro hall
    rw [activeProduct_Phi_exact]
    apply Finset.sum_eq_zero
    intro l hl
    simp [hall l hl]

/-- An ACTUAL resolved source sieve position supplies a quantitative
upper bound on the UNPAID original q discrepancy. This result
does not assert that the position covers any particular arithmetic q,
or that the right side fits the H430 reserve. -/
theorem actual_unpaid_le_one_sieved_position
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n k tau p g)
    (hl : l ∈ activePositions N n k tau p g) :
    actualUnpaidAt N n k tau p g ≤
      max (((originalReceiver N p).card : ℝ) -
        5 * actualPositionPhiTerm N n k tau p g l) 0 := by
  have hle := actual_position_Phi_term_le_full N n k tau p g l hl
  have hlinear :
      ((originalReceiver N p).card : ℝ) -
        5 * Phi N (rootQ N n k tau p)
          (activeProductSupport N n k tau p g)
          (activeProductSigma N n k tau p g) (11/5) ≤
      ((originalReceiver N p).card : ℝ) -
        5 * actualPositionPhiTerm N n k tau p g l := by
    linarith
  dsimp only [actualUnpaidAt, unpaidOriginalMarkedGap,
    originalMarkedDiscrepancy]
  exact max_le (hlinear.trans (le_max_left _ _)) (le_max_right _ _)

/-- When a REAL selected occurrence has positive source-sieve count
and the original q receiver is nonempty, that historical mark makes
the explicit unpaid gap STRICTLY smaller than the original q count.
No effective global H430 asymptotic follows without quantitative
source occupancy, weights, and true selected-count owner matching. -/
theorem actual_positive_sieved_position_strictly_shrinks_unpaid
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n k tau p g)
    (hl : l ∈ activePositions N n k tau p g)
    (hsource : 0 < sourceSieveCount N
      (parentProduct (levelOccurrence l).current.old)
      ((parentProduct (levelOccurrence l).current.old) * N)
      (cutoff (rootQ N n k tau p)
        (parentProduct (levelOccurrence l).current.old) (11/5)))
    (hreceiver : 0 < (originalReceiver N p).card) :
    actualUnpaidAt N n k tau p g <
      ((originalReceiver N p).card : ℝ) := by
  have hcast :
      0 < (sourceSieveCount N
        (parentProduct (levelOccurrence l).current.old)
        ((parentProduct (levelOccurrence l).current.old) * N)
        (cutoff (rootQ N n k tau p)
          (parentProduct (levelOccurrence l).current.old) (11/5)) : ℝ) := by
    exact_mod_cast hsource
  have hterm : 0 < actualPositionPhiTerm N n k tau p g l := by
    dsimp [actualPositionPhiTerm]
    exact mul_pos (mark_pos (levelOccurrence l)) hcast
  have hphi : 0 < Phi N (rootQ N n k tau p)
      (activeProductSupport N n k tau p g)
      (activeProductSigma N n k tau p g) (11/5) :=
    lt_of_lt_of_le hterm
      (actual_position_Phi_term_le_full N n k tau p g l hl)
  have hcard : (0 : ℝ) < ((originalReceiver N p).card : ℝ) := by
    exact_mod_cast hreceiver
  dsimp only [actualUnpaidAt, unpaidOriginalMarkedGap,
    originalMarkedDiscrepancy]
  apply (max_lt_iff).2
  constructor
  · linarith
  · exact hcard

end
end ImbalancedChen.Part5OriginalH430ActualSievedPositionPayment
