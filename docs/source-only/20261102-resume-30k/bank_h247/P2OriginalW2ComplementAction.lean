import ImbalancedChen.P2OriginalW2CentreIncidence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Remove the four literal positive-child complement terms and the two
anchor complements from I's W2 expression, retaining their EXACT total
as a separately bounded error. The good-pair gates are unchanged; bad
pairs and all longer Gamma words retain the original raw source cost.
The only length-two switched occurrences are Gamma7 and Gamma8. Thus
the complete charge is at most 5 L_N + 4 L_N^3, not a number-of-primes
times log N bound. Every old-state value reads one immutable generation.
-/
namespace ImbalancedChen.P2OriginalW2ComplementAction

noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions P2AllW1SameQRawCountInduction
open P2W2PhysicalChildFeedback P2OriginalW2CentreIncidence
open P5OriginalU5FrozenSource (receiver)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedPrefixMaskDefect (quotientCarrier)
open P5OriginalActionMassBound (originalW2At)
open scoped Classical BigOperators

/-- The actual old upper value at a good pair; the full raw bad-pair
cost remains. No pair outside the original gates gets feedback. -/
def paidChild (N : ℕ) (Q : ℝ) (old : PhysicalState) (d p q : ℕ) (a : ℝ) : ℝ :=
  if PairGate Q d p q then old.upper (d*p*q) a
  else (frozenCount N (d*p*q) (fun _ => True) a : ℝ)

def childCharge (N : ℕ) (Q : ℝ) (d p q : ℕ) (a : ℝ) : ℝ :=
  if PairGate Q d p q then complementCount N (d*p*q) (receiver N) a else 0

theorem positiveChild_eq_paid_add_charge (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d p q : ℕ) (a : ℝ) :
    positiveChild N Q (receiver N) old d p q a =
      paidChild N Q old d p q a + childCharge N Q d p q a := by
  unfold positiveChild paidChild childCharge
  split_ifs <;> ring

def paidPairs (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a u v w : ℝ) : ℝ :=
  ∑ q∈primeWindow N v w, ∑ p∈primeWindow N a u,
    if p<q then paidChild N Q old d p q a else 0

def pairCharge (N : ℕ) (Q : ℝ) (d : ℕ) (a u v w : ℝ) : ℝ :=
  ∑ q∈primeWindow N v w, ∑ p∈primeWindow N a u,
    if p<q then childCharge N Q d p q a else 0

theorem positivePairs_eq_paid_add_charge (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a u v w : ℝ) :
    positivePairs N Q (receiver N) old d a u v w =
      paidPairs N Q old d a u v w + pairCharge N Q d a u v w := by
  unfold positivePairs paidPairs pairCharge
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro q _
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro p _
  split_ifs
  · exact positiveChild_eq_paid_add_charge N Q old d p q a
  · ring

theorem pairCharge_le {N : ℕ} (hN : 0<N) (hNP : ¬N.Prime)
    (Q : ℝ) (d : ℕ) (a u v w : ℝ) :
    pairCharge N Q d a u v w ≤ logRank N^3 := by
  have he : pairCharge N Q d a u v w =
      ∑ p∈primeWindow N a u, ∑ q∈primeWindow N v w,
        if p<q ∧ PairGate Q d p q then
          complementCount N (d*p*q) (receiver N) a else 0 := by
    unfold pairCharge childCharge
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    split_ifs <;> simp_all
  rw [he]
  exact gated_pair_complements_le hN hNP d _ _
    (fun p hp => (mem_primeWindow.mp hp).1)
    (fun q hq => (mem_primeWindow.mp hq).1) _ (fun _ _ => a)

def paidQuotient (N : ℕ) (Q : ℝ) (old : PhysicalState) (d : ℕ) (l : List ℕ) : ℝ :=
  match l with
  | [p,q] => if p.Prime ∧ q.Prime ∧ p<q then paidChild N Q old d p q (p:ℝ)
      else ((quotientCarrier N d l).card : ℝ)
  | _ => ((quotientCarrier N d l).card : ℝ)

def quotientCharge (N : ℕ) (Q : ℝ) (d : ℕ) (l : List ℕ) : ℝ :=
  match l with
  | [p,q] => if p.Prime ∧ q.Prime ∧ p<q then childCharge N Q d p q (p:ℝ) else 0
  | _ => 0

theorem quotientFeedback_eq_paid_add_charge (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (l : List ℕ) :
    quotientFeedback N Q (receiver N) old d l =
      paidQuotient N Q old d l + quotientCharge N Q d l := by
  cases l with
  | nil => simp [quotientFeedback,paidQuotient,quotientCharge]
  | cons p l =>
    cases l with
    | nil => simp [quotientFeedback,paidQuotient,quotientCharge]
    | cons q l =>
      cases l with
      | cons r l => simp [quotientFeedback,paidQuotient,quotientCharge]
      | nil =>
        simp only [quotientFeedback,paidQuotient,quotientCharge]
        split_ifs
        · exact positiveChild_eq_paid_add_charge N Q old d p q (p:ℝ)
        · ring

theorem quotientCharge_long (N : ℕ) (Q : ℝ) (d : ℕ) (l : List ℕ)
    (hl : l.length≠2) : quotientCharge N Q d l=0 := by
  cases l with
  | nil => rfl
  | cons p l =>
    cases l with
    | nil => rfl
    | cons q l =>
      cases l with
      | nil => exact False.elim (hl rfl)
      | cons r l => rfl

def paidPrefix (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l∈secondFunctionalMotherTuples (primeWindow N a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e)=cs then paidQuotient N Q old d l else 0

def prefixCharge (N : ℕ) (Q : ℝ) (d : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l∈secondFunctionalMotherTuples (primeWindow N a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e)=cs then quotientCharge N Q d l else 0

theorem prefixFeedback_eq_paid_add_charge (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    prefixFeedback N Q (receiver N) old d a b c e f cs =
      paidPrefix N Q old d a b c e f cs + prefixCharge N Q d a b c e f cs := by
  unfold prefixFeedback paidPrefix prefixCharge
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro l _
  split_ifs
  · exact quotientFeedback_eq_paid_add_charge N Q old d l
  · ring

theorem prefixCharge_long (N : ℕ) (Q : ℝ) (d : ℕ) (a b c e f : ℝ)
    (cs : List ℕ) (hcs : cs.length≠2) : prefixCharge N Q d a b c e f cs=0 := by
  apply sum_eq_zero
  intro l hl
  have hlen := ((secondFunctionalMother_tuple_mem _ _ l).mp hl).1
  split_ifs
  · exact quotientCharge_long N Q d l (by omega)
  · rfl

/-- The literal two-prime word is a gated subset of an ordered pair
window. The cutoff is its FIRST prime, as in the original Gamma7/8. -/
theorem prefixCharge_pair (N : ℕ) (Q : ℝ) (d : ℕ) (a b c e f : ℝ) (v w : ℕ) :
    prefixCharge N Q d a b c e f [v,w] =
      ∑ p∈primeWindow N a f, ∑ q∈primeWindow N a f,
        if p<q ∧ secondFunctionalMotherColour b c e p=v ∧
            secondFunctionalMotherColour b c e q=w ∧ PairGate Q d p q then
          complementCount N (d*p*q) (receiver N) (p:ℝ) else 0 := by
  unfold prefixCharge
  rw [show [v,w].length=2 from rfl, MotherPair.tuple_pairs,
    sum_image (by
      intro x _ y _ h
      have he : x.1=y.1 ∧ x.2=y.2 := by simpa using h
      exact Prod.ext he.1 he.2)]
  simp only [sum_filter,sum_product,List.map_cons,List.map_nil,List.cons.injEq,and_true]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  have hpp := (mem_primeWindow.mp hp).1
  have hqp := (mem_primeWindow.mp hq).1
  simp only [quotientCharge,childCharge,hpp,hqp,true_and]
  split_ifs <;> simp_all

theorem prefixCharge_pair_le {N : ℕ} (hN : 0<N) (hNP : ¬N.Prime)
    (Q : ℝ) (d : ℕ) (a b c e f : ℝ) (v w : ℕ) :
    prefixCharge N Q d a b c e f [v,w] ≤ logRank N^3 := by
  rw [prefixCharge_pair]
  exact gated_pair_complements_le hN hNP d _ _
    (fun p hp => (mem_primeWindow.mp hp).1)
    (fun q hq => (mem_primeWindow.mp hq).1) _ (fun p _ => (p:ℝ))

def paidSwitched (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map (paidPrefix N Q old d a b c e f)).sum).sum

def switchedCharge (N : ℕ) (Q : ℝ) (d : ℕ) (a b c e f : ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map (prefixCharge N Q d a b c e f)).sum).sum

theorem switchedFeedback_eq_paid_add_charge (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) :
    switchedFeedback N Q (receiver N) old d a b c e f =
      paidSwitched N Q old d a b c e f + switchedCharge N Q d a b c e f := by
  unfold switchedFeedback paidSwitched switchedCharge
  simp only [prefixFeedback_eq_paid_add_charge,List.sum_map_add]

/-- All original word occurrences are kept. Exactly Gamma7 and Gamma8
contain a length-two word; no longer word's unit quotient is deleted. -/
theorem switchedCharge_two (N : ℕ) (Q : ℝ) (d : ℕ) (a b c e f : ℝ) :
    switchedCharge N Q d a b c e f =
      prefixCharge N Q d a b c e f [0,0] + prefixCharge N Q d a b c e f [0,1] := by
  norm_num [switchedCharge,secondFunctionalMotherPrefixIndices,
    secondFunctionalMotherGammaWords,prefixCharge_long]

def paidRest (N : ℕ) (Q : ℝ) (old : PhysicalState) (d : ℕ) (a b c e f : ℝ) : ℝ :=
  -negativeWindow N Q (receiver N) old d a f-
    negativeWindow N Q (receiver N) old d a c-
    negativeWindow N Q (receiver N) old d a e+
    paidPairs N Q old d a c a c+paidPairs N Q old d a b c e+
    paidSwitched N Q old d a b c e f+
    P2EnhancedTwentyOneQuotientFinite.collisionSwitched N d N a b c e f+
    fourthRowMotherBadPrime N d a f+fourthRowMotherBadPrime N d a c+
    fourthRowMotherBadPrime N d a e

def paidW2 (N : ℕ) (Q : ℝ) (old : PhysicalState) (d : ℕ) (j : Fin 36) : ℝ :=
  let p := originalW2At j
  let a := cutoff Q d p.s0
  let b := cutoff Q d p.phi1
  (4*old.upper d a+old.upper d b+
    paidRest N Q old d a b (cutoff Q d p.phi2) (cutoff Q d p.phi3) (cutoff Q d p.s))/5

def W2Charge (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) : ℝ :=
  let p := originalW2At j
  let a := cutoff Q d p.s0
  let b := cutoff Q d p.phi1
  let c := cutoff Q d p.phi2
  let e := cutoff Q d p.phi3
  let f := cutoff Q d p.s
  4*complementCount N d (receiver N) a+complementCount N d (receiver N) b+
    pairCharge N Q d a c a c+pairCharge N Q d a b c e+switchedCharge N Q d a b c e f

theorem W2Bound_eq_paid_add_charge (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (j : Fin 36) :
    W2Bound N Q (receiver N) old d j=paidW2 N Q old d j+W2Charge N Q d j/5 := by
  unfold W2Bound paidW2 W2Charge
  dsimp only
  unfold feedbackRest paidRest
  rw [positivePairs_eq_paid_add_charge,positivePairs_eq_paid_add_charge,
    switchedFeedback_eq_paid_add_charge]
  ring

/-- Exactly five anchor copies and four pair occurrences. No action
count or window cardinality multiplies this bound. -/
theorem W2Charge_le {N : ℕ} (hN : 0<N) (hNP : ¬N.Prime)
    (Q : ℝ) (d : ℕ) (j : Fin 36) :
    W2Charge N Q d j ≤ 5*logRank N+4*logRank N^3 := by
  have ha := complement_le_logRank hN d (cutoff Q d (originalW2At j).s0)
  have hb := complement_le_logRank hN d (cutoff Q d (originalW2At j).phi1)
  have h5 := pairCharge_le hN hNP Q d
    (cutoff Q d (originalW2At j).s0) (cutoff Q d (originalW2At j).phi2)
    (cutoff Q d (originalW2At j).s0) (cutoff Q d (originalW2At j).phi2)
  have h6 := pairCharge_le hN hNP Q d
    (cutoff Q d (originalW2At j).s0) (cutoff Q d (originalW2At j).phi1)
    (cutoff Q d (originalW2At j).phi2) (cutoff Q d (originalW2At j).phi3)
  have h7 := prefixCharge_pair_le hN hNP Q d
    (cutoff Q d (originalW2At j).s0) (cutoff Q d (originalW2At j).phi1)
    (cutoff Q d (originalW2At j).phi2) (cutoff Q d (originalW2At j).phi3)
    (cutoff Q d (originalW2At j).s) 0 0
  have h8 := prefixCharge_pair_le hN hNP Q d
    (cutoff Q d (originalW2At j).s0) (cutoff Q d (originalW2At j).phi1)
    (cutoff Q d (originalW2At j).phi2) (cutoff Q d (originalW2At j).phi3)
    (cutoff Q d (originalW2At j).s) 0 1
  unfold W2Charge
  dsimp only
  rw [switchedCharge_two]
  linarith

/-- The old-state invariant is supplied by I's actual arithmetic
recursion, including all W1/W2/Buchstab alternatives and signed seed
remainders. It is not an assumed enhanced numeric table invariant. -/
theorem iterate_W2_upper (N : ℕ) (Q : ℝ) (bank : List P2ActualMarkedCountState.Query)
    (rounds : ℕ) {d : ℕ} (j : Fin 36) (hd : 0<d) (hR : 1<Q/(d:ℝ)) :
    (frozenCount N d (receiver N) (cutoff Q d (originalW2At j).s):ℝ) ≤
      paidW2 N Q (P2AllW2ImmutableCountRecursion.iterate N Q (receiver N) bank rounds) d j+
        W2Charge N Q d j/5 := by
  rw [←W2Bound_eq_paid_add_charge]
  exact W2Bound_upper N Q (receiver N) _ j hd hR
    (P2AllW2ImmutableCountRecursion.iterate_encloses N Q (receiver N) bank rounds)

end
end ImbalancedChen.P2OriginalW2ComplementAction
