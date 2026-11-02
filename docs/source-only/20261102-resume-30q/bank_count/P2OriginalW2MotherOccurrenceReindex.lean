import ImbalancedChen.P2OriginalW2ComplementAction

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact reindexing of the original Gamma7/8 mother WORD occurrences into
their half-open N-windows. The summand may retain an arbitrary history;
neither prime products nor parent labels are quotiented. The concrete
old-state specialization keeps the first-prime cutoff and separates
every rejected pair as its unchanged raw count. This is a finite count
carrier conversion, not an old H/h licence or an analytic base estimate.
-/
namespace ImbalancedChen.P2OriginalW2MotherOccurrenceReindex

noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2FrozenReceiverCountActions P2AllW1SameQRawCountInduction
open P2W2PhysicalChildFeedback P2OriginalW2ComplementAction

/-- A list-valued summand retains all selected-history data. The map to
the ordered pair is injective before any product or count is evaluated. -/
theorem colour_pair_reindex (P : Finset ℕ) (b c e : ℝ) (v w : ℕ)
    (F : List ℕ → ℝ) :
    (∑ l ∈ secondFunctionalMotherTuples P 2,
      if l.map (secondFunctionalMotherColour b c e) = [v,w] then F l else 0) =
      ∑ p ∈ P.filter (fun p => secondFunctionalMotherColour b c e p = v),
        ∑ q ∈ P.filter (fun q => secondFunctionalMotherColour b c e q = w),
          if p < q then F [p,q] else 0 := by
  rw [MotherPair.tuple_pairs, sum_image (by
    intro x _ y _ h
    have he : x.1 = y.1 ∧ x.2 = y.2 := by simpa using h
    exact Prod.ext he.1 he.2)]
  simp only [sum_filter, sum_product, List.map_cons, List.map_nil,
    List.cons.injEq, and_true]
  apply sum_congr rfl
  intro p _
  by_cases hp : secondFunctionalMotherColour b c e p = v
  · simp only [hp, if_true, true_and]
    apply sum_congr rfl
    intro q _
    split_ifs <;> simp_all
  · simp [hp]

/-- The actual paid quotient has no fallback on a prime ordered word.
Its bad-square branch remains inside paidChild. -/
theorem paidPrefix_pair_restrict (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) (v w : ℕ) :
    paidPrefix N Q old d a b c e f [v,w] =
      ∑ p ∈ (primeWindow N a f).filter
          (fun p => secondFunctionalMotherColour b c e p = v),
        ∑ q ∈ (primeWindow N a f).filter
            (fun q => secondFunctionalMotherColour b c e q = w),
          if p < q then paidChild N Q old d p q (p:ℝ) else 0 := by
  unfold paidPrefix
  rw [show [v,w].length = 2 from rfl, colour_pair_reindex]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  have hpp := (mem_primeWindow.mp (mem_filter.mp hp).1).1
  have hqp := (mem_primeWindow.mp (mem_filter.mp hq).1).1
  by_cases hpq : p < q
  · simp only [if_pos hpq, paidQuotient, hpp, hqp, hpq, and_self, if_true]
  · simp only [if_neg hpq]

theorem paidPrefix_seven (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) {a b c e f : ℝ} (hbf : b ≤ f) :
    paidPrefix N Q old d a b c e f [0,0] =
      ∑ p ∈ primeWindow N a b, ∑ q ∈ primeWindow N a b,
        if p < q then paidChild N Q old d p q (p:ℝ) else 0 := by
  rw [paidPrefix_pair_restrict, MotherPair.colour_zero_window N hbf]

theorem paidPrefix_eight (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) {a b c e f : ℝ} (hab : a ≤ b) (hbf : b ≤ f) (hcf : c ≤ f) :
    paidPrefix N Q old d a b c e f [0,1] =
      ∑ p ∈ primeWindow N a b, ∑ q ∈ primeWindow N b c,
        if p < q then paidChild N Q old d p q (p:ℝ) else 0 := by
  rw [paidPrefix_pair_restrict, MotherPair.colour_zero_window N hbf,
    MotherPair.colour_one_window N hab hcf]

/-- Exactly the old upper evaluations on the good physical pair gate. -/
def goodPairCount (Q : ℝ) (old : PhysicalState) (d : ℕ)
    (P R : Finset ℕ) (z : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ R,
    if p < q ∧ PairGate Q d p q then old.upper (d*p*q) (z p q) else 0

/-- The complement is the full literal positive count, with no H value. -/
def rejectedPairCount (N : ℕ) (Q : ℝ) (d : ℕ)
    (P R : Finset ℕ) (z : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ R,
    if p < q ∧ ¬ PairGate Q d p q then
      (frozenCount N (d*p*q) (fun _ => True) (z p q) : ℝ) else 0

theorem paid_pair_split (N : ℕ) (Q : ℝ) (old : PhysicalState) (d : ℕ)
    (P R : Finset ℕ) (z : ℕ → ℕ → ℝ) :
    (∑ p ∈ P, ∑ q ∈ R,
      if p < q then paidChild N Q old d p q (z p q) else 0) =
      goodPairCount Q old d P R z + rejectedPairCount N Q d P R z := by
  unfold goodPairCount rejectedPairCount
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  unfold paidChild
  by_cases hpq : p < q <;> by_cases hg : PairGate Q d p q <;> simp [hpq,hg]

theorem paidPairs_split (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a u v w : ℝ) :
    paidPairs N Q old d a u v w =
      goodPairCount Q old d (primeWindow N a u) (primeWindow N v w) (fun _ _ => a) +
      rejectedPairCount N Q d (primeWindow N a u) (primeWindow N v w) (fun _ _ => a) := by
  unfold paidPairs
  rw [sum_comm]
  exact paid_pair_split N Q old d _ _ _

theorem paidPrefix_seven_split (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) {a b c e f : ℝ} (hbf : b ≤ f) :
    paidPrefix N Q old d a b c e f [0,0] =
      goodPairCount Q old d (primeWindow N a b) (primeWindow N a b) (fun p _ => (p:ℝ)) +
      rejectedPairCount N Q d (primeWindow N a b) (primeWindow N a b) (fun p _ => (p:ℝ)) := by
  rw [paidPrefix_seven N Q old d hbf]
  exact paid_pair_split N Q old d _ _ _

theorem paidPrefix_eight_split (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) {a b c e f : ℝ} (hab : a ≤ b) (hbf : b ≤ f) (hcf : c ≤ f) :
    paidPrefix N Q old d a b c e f [0,1] =
      goodPairCount Q old d (primeWindow N a b) (primeWindow N b c) (fun p _ => (p:ℝ)) +
      rejectedPairCount N Q d (primeWindow N a b) (primeWindow N b c) (fun p _ => (p:ℝ)) := by
  rw [paidPrefix_eight N Q old d hab hbf hcf]
  exact paid_pair_split N Q old d _ _ _

/-- The original longer-word multiset is retained, including repeated
colour words in distinct Gamma occurrences and all unit quotients. -/
def higherPaidSwitched (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    (((secondFunctionalMotherGammaWords i).filter (fun cs => cs.length ≠ 2)).map
      (paidPrefix N Q old d a b c e f)).sum).sum

theorem paidSwitched_occurrences (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) :
    paidSwitched N Q old d a b c e f =
      paidPrefix N Q old d a b c e f [0,0] +
      paidPrefix N Q old d a b c e f [0,1] +
      higherPaidSwitched N Q old d a b c e f := by
  norm_num [paidSwitched, higherPaidSwitched, secondFunctionalMotherPrefixIndices,
    secondFunctionalMotherGammaWords]
  <;> ring

/-- Each long-word summand is still the original quotient carrier. -/
theorem paidQuotient_long (N : ℕ) (Q : ℝ) (old : PhysicalState) (d : ℕ)
    (l : List ℕ) (hl : l.length ≠ 2) :
    paidQuotient N Q old d l =
      ((P2EnhancedPrefixMaskDefect.quotientCarrier N d l).card : ℝ) := by
  cases l with
  | nil => rfl
  | cons p l =>
    cases l with
    | nil => rfl
    | cons q l =>
      cases l with
      | nil => exact False.elim (hl rfl)
      | cons r l => rfl

end
end ImbalancedChen.P2OriginalW2MotherOccurrenceReindex
