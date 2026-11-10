import ImbalancedChen.P2EnhancedW1RepeatedLabelClassification

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The selected graph action is the literal `StepShape.w1Singleton i j`.
For one actual old marked word and one old-mask receiver, the bad later
prime labels form a filtered subset of the eligible quotient prime factors.
Each bad label is sent by the Phase10 physical classification to the SAME
Phase9 square event. The finite weighted sum retains `sigma B`, the old
predicate `E B ell`, total `Q`, and every individual q fibre. No uniform
fibre cap is inserted: the right side still has its true receiver-dependent
eligible-prime cardinality. Hence this file is not a W1 K supplier.

Original: manuscript-body.tex 790--817, 819--875;
same-new-level-double-sieve-route.tex 93--105, 147--165.
-/

namespace ImbalancedChen.P2EnhancedW1SelectedBadLabelFibres

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPhysicalTransition (StepShape LocalDomain)
open P2EnhancedLowerFinitePhysicalGraph (TypedNode Program Coordinates Member realize)
open P2EnhancedW1R2ActualCarrierBranch (eligiblePrimes)
open P2EnhancedW1TripleActualCarrierBranch (oldMaskTripleCarrier)
open P2EnhancedW1SquareExceptionPower (squareEvent)
open P2EnhancedW1RepeatedLabelClassification (graph_selected_w1_triple_exception)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2LargerSActualPositiveCounts (historyCarrier)
open P5OriginalActionMassBound (W1Anchor)

/-- Exact canonical later-q fibre whose old-mask quotient carrier fails.
The first two selected labels remain visible in the definition. -/
def badLaterLabels (N ell : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) (a b : ℕ) : Finset ℕ :=
  (((eligiblePrimes N ell Q old i j).erase a).erase b).filter
    (fun q => ell ∉ oldMaskTripleCarrier N old.prod a b q E)

theorem badLaterLabels_data {N ell : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {E : ℕ → ℕ → Prop} {a b q : ℕ}
    (hq : q ∈ badLaterLabels N ell Q old i j E a b) :
    q ∈ eligiblePrimes N ell Q old i j ∧ q ≠ a ∧ q ≠ b ∧
      ell ∉ oldMaskTripleCarrier N old.prod a b q E := by
  obtain ⟨hqErase,hbad⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqb,hqA⟩ := Finset.mem_erase.mp hqErase
  obtain ⟨hqa,hqP⟩ := Finset.mem_erase.mp hqA
  exact ⟨hqP,hqa,hqb,hbad⟩

/-- Physical selected graph code plus the actual integer word send every
bad canonical later label to the counted square event. The graph's real
coordinate is not silently identified with the integer q. -/
theorem graph_selected_bad_label_in_squareEvent
    {N mesh depth ell : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b q : ℕ}
    {root : TypedNode} {code : Program mesh depth}
    {z : Coordinates depth} {action : Program mesh 1}
    {actionZ : Coordinates 1}
    (hprev : Member lo hi depth root code z)
    (hshape : (action 0).1 = StepShape.w1Singleton i j)
    (haction : Member lo hi 1
      ⟨true,(realize depth root code z).physical⟩ action actionZ)
    (hgamma : 0 < gamma)
    (hroot : gamma ≤ residual root.physical)
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : word (realize depth root code z).physical =
      old.map (physicalPrime N))
    (htotal : (realize depth root code z).physical.total =
      Real.log Q / Real.log (N : ℝ))
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r)
    (hq : q ∈ badLaterLabels N ell Q old i j E a b) :
    LocalDomain (realize depth root code z).physical
      (.w1Singleton i j) (actionZ 0) ∧
    ell ∈ squareEvent N old.prod E
      (cutoff Q old.prod (W1Anchor j))
      ((N : ℝ)^((gamma/(101:ℝ)^depth)/5)) := by
  obtain ⟨hqP,hqa,hqb,hbad⟩ := badLaterLabels_data hq
  have hbq : b < q := lt_of_le_of_ne (hsecond q hqP hqa) hqb.symm
  obtain ⟨hlocal,hclass⟩ := graph_selected_w1_triple_exception
    hprev hshape haction hgamma hroot hw hprime hword htotal
    hcomp hell ha hb hqP hab hbq hsecond
  exact ⟨hlocal,hclass.resolve_left hbad⟩

/-- The exact finite fibre bound at one receiver, with its still-variable
active-prime multiplicity. This counts labels, not merely receivers. -/
theorem badLaterLabels_card_le_event_fibre
    {N mesh depth ell : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b : ℕ}
    {root : TypedNode} {code : Program mesh depth}
    {z : Coordinates depth} {action : Program mesh 1}
    {actionZ : Coordinates 1}
    (hprev : Member lo hi depth root code z)
    (hshape : (action 0).1 = StepShape.w1Singleton i j)
    (haction : Member lo hi 1
      ⟨true,(realize depth root code z).physical⟩ action actionZ)
    (hgamma : 0 < gamma)
    (hroot : gamma ≤ residual root.physical)
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : word (realize depth root code z).physical =
      old.map (physicalPrime N))
    (htotal : (realize depth root code z).physical.total =
      Real.log Q / Real.log (N : ℝ))
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r) :
    (badLaterLabels N ell Q old i j E a b).card ≤
      if ell ∈ squareEvent N old.prod E
        (cutoff Q old.prod (W1Anchor j))
        ((N : ℝ)^((gamma/(101:ℝ)^depth)/5))
      then (eligiblePrimes N ell Q old i j).card else 0 := by
  classical
  by_cases hs : ell ∈ squareEvent N old.prod E
      (cutoff Q old.prod (W1Anchor j))
      ((N : ℝ)^((gamma/(101:ℝ)^depth)/5))
  · simp only [if_pos hs]
    apply Finset.card_le_card
    intro q hq
    exact (badLaterLabels_data hq).1
  · simp only [if_neg hs]
    suffices hempty : badLaterLabels N ell Q old i j E a b = ∅ by
      simp [hempty]
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro q hq
    exact hs (graph_selected_bad_label_in_squareEvent hprev hshape
      haction hgamma hroot hw hprime hword htotal hcomp hell ha hb
      hab hsecond hq).2

/-- Literal sigma(B) on the same receiver, before any uniform factor
count is supplied. -/
theorem weighted_badLaterLabels_le_event_fibre
    {N mesh depth ell : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b : ℕ} {sigma : ℕ → ℝ}
    {root : TypedNode} {code : Program mesh depth}
    {z : Coordinates depth} {action : Program mesh 1}
    {actionZ : Coordinates 1}
    (hprev : Member lo hi depth root code z)
    (hshape : (action 0).1 = StepShape.w1Singleton i j)
    (haction : Member lo hi 1
      ⟨true,(realize depth root code z).physical⟩ action actionZ)
    (hgamma : 0 < gamma)
    (hroot : gamma ≤ residual root.physical)
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : word (realize depth root code z).physical =
      old.map (physicalPrime N))
    (htotal : (realize depth root code z).physical.total =
      Real.log Q / Real.log (N : ℝ))
    (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r)
    (hsigma : 0 ≤ sigma old.prod) :
    sigma old.prod *
      ((badLaterLabels N ell Q old i j E a b).card : ℝ) ≤
    sigma old.prod *
      (if ell ∈ squareEvent N old.prod E
        (cutoff Q old.prod (W1Anchor j))
        ((N : ℝ)^((gamma/(101:ℝ)^depth)/5))
      then ((eligiblePrimes N ell Q old i j).card : ℝ) else 0) := by
  apply mul_le_mul_of_nonneg_left _ hsigma
  exact_mod_cast badLaterLabels_card_le_event_fibre hprev hshape
    haction hgamma hroot hw hprime hword htotal hcomp hell ha hb
    hab hsecond

/-- The switched bad-label count summed over the actual frozen old
historyCarrier's at-least-two-prime subfamily. Canonical first/second
labels may vary with the receiver, and sigma(B) stays at the same B. -/
theorem selected_bad_label_sum_le_square_fibre_sum
    {N mesh depth : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {sigma : ℕ → ℝ} {C : Finset ℕ}
    {a b : ℕ → ℕ}
    {root : TypedNode} {code : Program mesh depth}
    {z : Coordinates depth} {action : Program mesh 1}
    {actionZ : Coordinates 1}
    (hprev : Member lo hi depth root code z)
    (hshape : (action 0).1 = StepShape.w1Singleton i j)
    (haction : Member lo hi 1
      ⟨true,(realize depth root code z).physical⟩ action actionZ)
    (hgamma : 0 < gamma)
    (hroot : gamma ≤ residual root.physical)
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : word (realize depth root code z).physical =
      old.map (physicalPrime N))
    (htotal : (realize depth root code z).physical.total =
      Real.log Q / Real.log (N : ℝ))
    (hsigma : 0 ≤ sigma old.prod)
    (hC : C ⊆ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (hfirst : ∀ ell ∈ C,
      0 < N-ell ∧
      a ell ∈ eligiblePrimes N ell Q old i j ∧
      b ell ∈ eligiblePrimes N ell Q old i j ∧
      a ell < b ell ∧
      (∀ r ∈ eligiblePrimes N ell Q old i j,
        r ≠ a ell → b ell ≤ r)) :
    (∑ ell ∈ C,
      sigma old.prod *
        ((badLaterLabels N ell Q old i j E (a ell) (b ell)).card : ℝ)) ≤
    (∑ ell ∈ C,
      sigma old.prod *
        (if ell ∈ squareEvent N old.prod E
          (cutoff Q old.prod (W1Anchor j))
          ((N : ℝ)^((gamma/(101:ℝ)^depth)/5))
        then ((eligiblePrimes N ell Q old i j).card : ℝ) else 0)) := by
  apply Finset.sum_le_sum
  intro ell hcell
  have hell := hC hcell
  obtain ⟨hcomp,ha,hb,hab,hsecond⟩ := hfirst ell hcell
  exact weighted_badLaterLabels_le_event_fibre hprev hshape
    haction hgamma hroot hw hprime hword htotal hcomp hell ha hb
    hab hsecond hsigma

end
end ImbalancedChen.P2EnhancedW1SelectedBadLabelFibres
