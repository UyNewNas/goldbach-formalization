import ImbalancedChen.P2EnhancedW1IntegerPrimeGraphStep
import ImbalancedChen.P2EnhancedW1SquareExceptionPower

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original positive W1 switched term is a labelled ordered triple
q1<q2<q3 at the SAME parent action (i,j), with a rough quotient tail.
It is not three successive `StepShape.w1Singleton` feedback edges: that
graph constructor appends one prime and switches to a lower child.
This source builds the finite integer triple family directly from the
actual eligible-prime set and parent old-mask historyCarrier.

The tail is the exact integer quotient after q1*q2*q3, not a proxy.
All repeated factors of the concatenated selected triple and rough
tail are classified: q1 cannot recur in the tail, a recurrence of q2
or q3 forces its square in the old quotient, and a tail square does
likewise. Every such labelled term lies in the Phase9 squareEvent at
the unchanged parent B, Q, E and a fixed power cutoff. The source set
retains label multiplicity and is bounded by the cube of the actual
eligible-prime fibre. The fixed graph-derived cap of PhaseB2 is the
next finite weighted payment step.

Original: manuscript-body.tex 790--817,819--875;
same-new-level-double-sieve-route.tex 93--105,147--165.
-/

namespace ImbalancedChen.P2EnhancedW1OrderedPositiveTripleWord

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedW1R2ActualCarrierBranch (eligiblePrimes eligiblePrime_data)
open P2EnhancedW1SquareExceptionPower (squareEvent)
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPhysicalTransition (StepShape)
open P2EnhancedLowerFinitePhysicalGraph (TypedNode Program Coordinates Member realize)
open P2EnhancedLowerPrimeChildCarriers (parentWindow physicalPrime)
open P2EnhancedLowerPrimeChildGeometry (physicalLevel)
open P2EnhancedW1RepeatedLabelClassification
  (physical_level_eq_parent_residual graph_w1_fixed_power)
open P2EnhancedW1FixedPowerLabelMultiplicity
  (graph_selected_eligible_fibre_fixed_power)
open P2LargerSActualPositiveCounts (historyCarrier)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalActionMassBound (W1Anchor)

abbrev TripleLabel := (ℕ × ℕ) × ℕ
def first (t : TripleLabel) : ℕ := t.1.1
def middle (t : TripleLabel) : ℕ := t.1.2
def last (t : TripleLabel) : ℕ := t.2
def tripleProduct (t : TripleLabel) : ℕ := first t * middle t * last t
def oldQuotient (N ell : ℕ) (old : List ℕ) : ℕ := (N-ell)/old.prod
def roughTail (m z : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ m → z ≤ r
def tail (N ell : ℕ) (old : List ℕ) (t : TripleLabel) : ℕ :=
  oldQuotient N ell old / tripleProduct t

/-- The exact finite ordered q1<q2<q3 positive W1 word at one true
old-mask receiver. Its quotient tail is rough at q2. The product of
prime sets retains every distinct ordered triple label separately. -/
def positiveTripleWords (N ell : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) : Finset TripleLabel :=
  let P := eligiblePrimes N ell Q old i j
  ((P.product P).product P).filter (fun t =>
    ell ∈ historyCarrier N old.prod E (cutoff Q old.prod (W1Anchor j)) ∧
    ell < N ∧ first t < middle t ∧ middle t < last t ∧
    tripleProduct t ∣ oldQuotient N ell old ∧
    roughTail (tail N ell old t) (middle t))

theorem positiveTripleWords_data {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {t : TripleLabel}
    (ht : t ∈ positiveTripleWords N ell Q old i j E) :
    first t ∈ eligiblePrimes N ell Q old i j ∧
    middle t ∈ eligiblePrimes N ell Q old i j ∧
    last t ∈ eligiblePrimes N ell Q old i j ∧
    ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)) ∧
    ell < N ∧ first t < middle t ∧ middle t < last t ∧
    tripleProduct t ∣ oldQuotient N ell old ∧
    roughTail (tail N ell old t) (middle t) := by
  unfold positiveTripleWords at ht
  obtain ⟨hambient,hconditions⟩ := Finset.mem_filter.mp ht
  obtain ⟨hpair,hlast⟩ := Finset.mem_product.mp hambient
  obtain ⟨hfirst,hmiddle⟩ := Finset.mem_product.mp hpair
  exact ⟨hfirst,hmiddle,hlast,hconditions⟩

/-- The selected product and exact residual tail multiply back to
the original old quotient. -/
theorem positiveTripleWords_quotient_identity {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {t : TripleLabel}
    (ht : t ∈ positiveTripleWords N ell Q old i j E) :
    tripleProduct t * tail N ell old t = oldQuotient N ell old := by
  exact Nat.mul_div_cancel' (positiveTripleWords_data ht).2.2.2.2.2.2.2.1

/-- The exact positive product m=B*q1*q2*q3*tail equals N-ell.
No multiplicity or normalization is dropped. -/
theorem positiveTripleWords_physical_product {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {t : TripleLabel}
    (ht : t ∈ positiveTripleWords N ell Q old i j E) :
    old.prod * tripleProduct t * tail N ell old t = N-ell := by
  have hell := (positiveTripleWords_data ht).2.2.2.1
  have hB : old.prod ∣ N-ell :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hell).1).2.2.1
  calc
    old.prod * tripleProduct t * tail N ell old t =
        old.prod * oldQuotient N ell old := by
      rw [← mul_assoc,positiveTripleWords_quotient_identity ht]
    _ = N-ell := Nat.mul_div_cancel' hB

/-- q1 is smaller than the rough-tail threshold q2 and therefore
cannot occur again in that tail. -/
theorem positiveTripleWords_first_absent_from_tail {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {t : TripleLabel}
    (ht : t ∈ positiveTripleWords N ell Q old i j E) :
    ¬ first t ∣ tail N ell old t := by
  intro hdiv
  have h := positiveTripleWords_data ht
  have hp := (eligiblePrime_data h.1).1
  have hrough := h.2.2.2.2.2.2.2.2 (first t) hp hdiv
  have horder := h.2.2.2.2.2.1
  omega

/-- A repeated factor in the literal selected triple plus residual
tail. The selected q labels are strictly ordered, so their own word
contains no repetition. -/
def repeatedResidual (N ell : ℕ) (old : List ℕ) (t : TripleLabel) : Prop :=
  ∃ r : ℕ, r.Prime ∧
    (r^2 ∣ tail N ell old t ∨
      (r ∣ tripleProduct t ∧ r ∣ tail N ell old t))

def repeatedTripleWords (N ell : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) : Finset TripleLabel :=
  (positiveTripleWords N ell Q old i j E).filter
    (repeatedResidual N ell old)

/-- Each possible repeated residual pattern squares into the ACTUAL
old quotient. The three selected labels are kept distinct. -/
theorem repeatedTripleWords_square_oldQuotient {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {t : TripleLabel}
    (ht : t ∈ repeatedTripleWords N ell Q old i j E) :
    ∃ r : ℕ, r.Prime ∧ middle t ≤ r ∧
      r^2 ∣ oldQuotient N ell old := by
  obtain ⟨hsource,hrpt⟩ := Finset.mem_filter.mp ht
  have hdata := positiveTripleWords_data hsource
  have hqprod := positiveTripleWords_quotient_identity hsource
  obtain ⟨r,hrPrime,hsquare|⟨hselected,htail⟩⟩ := hrpt
  · have hrough (hd : r ∣ tail N ell old t) : middle t ≤ r :=
      hdata.2.2.2.2.2.2.2.2 r hrPrime hd
    have hrTail : r ∣ tail N ell old t :=
      (dvd_pow_self r (by norm_num)).trans hsquare
    have hquotTail : tail N ell old t ∣ oldQuotient N ell old :=
      Nat.div_dvd_of_dvd hdata.2.2.2.2.2.2.2.1
    exact ⟨r,hrPrime,hrough hrTail,hsquare.trans hquotTail⟩
  · change r ∣ first t * middle t * last t at hselected
    rcases hrPrime.dvd_mul.mp hselected with h12 | h3
    · rcases hrPrime.dvd_mul.mp h12 with h1 | h2
      · have hrFirst : r = first t :=
          (Nat.prime_dvd_prime_iff_eq hrPrime
            (eligiblePrime_data hdata.1).1).mp h1
        exact False.elim (positiveTripleWords_first_absent_from_tail
          hsource (hrFirst ▸ htail))
      · have hrMiddle : r = middle t :=
          (Nat.prime_dvd_prime_iff_eq hrPrime
            (eligiblePrime_data hdata.2.1).1).mp h2
        subst r
        obtain ⟨k,hk⟩ := htail
        have hsqProduct : (middle t)^2 ∣
            tripleProduct t * tail N ell old t := by
          refine ⟨first t * last t * k, ?_⟩
          dsimp [tripleProduct]
          rw [hk]
          ring
        rw [hqprod] at hsqProduct
        exact ⟨middle t,(eligiblePrime_data hdata.2.1).1,le_refl _,
          hsqProduct⟩
    · have hrLast : r = last t :=
        (Nat.prime_dvd_prime_iff_eq hrPrime
          (eligiblePrime_data hdata.2.2.1).1).mp h3
      subst r
      obtain ⟨k,hk⟩ := htail
      have hsqProduct : (last t)^2 ∣
          tripleProduct t * tail N ell old t := by
        refine ⟨first t * middle t * k, ?_⟩
        dsimp [tripleProduct]
        rw [hk]
        ring
      rw [hqprod] at hsqProduct
      exact ⟨last t,(eligiblePrime_data hdata.2.2.1).1,
        hdata.2.2.2.2.2.2.1.le,hsqProduct⟩

/-- All repeated patterns in the exact positive triple word are in
the SAME old-B squareEvent at any fixed power below the W1 cutoff. -/
theorem repeatedTripleWords_mem_squareEvent {N ell : ℕ} {Q eta : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {t : TripleLabel}
    (ht : t ∈ repeatedTripleWords N ell Q old i j E)
    (hcut : (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j)) :
    ell ∈ squareEvent N old.prod E
      (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^eta) := by
  have hsource := (Finset.mem_filter.mp ht).1
  have hdata := positiveTripleWords_data hsource
  obtain ⟨r,hrPrime,hrMiddle,hrSquare⟩ :=
    repeatedTripleWords_square_oldQuotient ht
  have hmiddleCut := (eligiblePrime_data hdata.2.1).2.2.1
  have hrBound : (N : ℝ)^eta ≤ (r : ℝ) := by
    have hreal : (middle t : ℝ) ≤ r := by exact_mod_cast hrMiddle
    exact (hcut.trans hmiddleCut).trans hreal
  exact Finset.mem_filter.mpr
    ⟨hdata.2.2.2.1,hdata.2.2.2.2.1,r,hrPrime,hrBound,hrSquare⟩

/-- This labelled source has at most the cube of the actual eligible
prime-factor fibre, with no unproved multiplicity premise. -/
theorem repeatedTripleWords_card_le_cube (N ell : ℕ) (Q : ℝ)
    (old : List ℕ) (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) :
    (repeatedTripleWords N ell Q old i j E).card ≤
      (eligiblePrimes N ell Q old i j).card^3 := by
  have hsub : repeatedTripleWords N ell Q old i j E ⊆
      ((eligiblePrimes N ell Q old i j).product
        (eligiblePrimes N ell Q old i j)).product
        (eligiblePrimes N ell Q old i j) := by
    intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hc := Finset.card_le_card hsub
  simpa [Finset.card_product,pow_succ,mul_assoc] using hc

/-- Every repeated positive triple label for ONE selected W1 graph
action is paid pointwise by the same physical squareEvent. The factor
`(1/eta)^3` is derived from the three ACTUAL eligible prime slots and
the PhaseB2 fixed-power fibre cap, rather than assumed multiplicity. -/
theorem graph_selected_repeated_triple_fibre_payment
    {N mesh depth ell : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {sigma : ℕ → ℝ}
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
    (hsigma : 0 ≤ sigma old.prod) :
    sigma old.prod *
      ((repeatedTripleWords N ell Q old i j E).card : ℝ) ≤
    sigma old.prod *
      (1 / ((gamma/(101:ℝ)^depth)/5))^3 *
      (if ell ∈ squareEvent N old.prod E
        (cutoff Q old.prod (W1Anchor j))
        ((N : ℝ)^((gamma/(101:ℝ)^depth)/5))
      then (1 : ℝ) else 0) := by
  let eta : ℝ := (gamma/(101:ℝ)^depth)/5
  let event := squareEvent N old.prod E
    (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^eta)
  have hcoord : physicalLevel N Q old =
      residual (realize depth root code z).physical :=
    physical_level_eq_parent_residual hw hprime hword htotal
  have hcut : (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j) :=
    graph_w1_fixed_power hprev hroot hgamma hw hcoord j
  by_cases he : ell ∈ event
  · have hell := (Finset.mem_filter.mp he).1
    have hlt := (Finset.mem_filter.mp he).2.1
    have hcap : ((eligiblePrimes N ell Q old i j).card : ℝ) ≤
        1/eta :=
      (graph_selected_eligible_fibre_fixed_power hprev hshape haction
        hgamma hroot hw hprime hword htotal (Nat.sub_pos_of_lt hlt)
        hell).2
    have hcardNat := repeatedTripleWords_card_le_cube
      N ell Q old i j E
    have hcard : ((repeatedTripleWords N ell Q old i j E).card : ℝ) ≤
        (1/eta)^3 := by
      calc
        _ ≤ ((eligiblePrimes N ell Q old i j).card : ℝ)^3 := by
          exact_mod_cast hcardNat
        _ ≤ (1/eta)^3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hcap 3
    have hpay := mul_le_mul_of_nonneg_left hcard hsigma
    simpa only [if_pos he,mul_one] using hpay
  · have hempty : repeatedTripleWords N ell Q old i j E = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro t ht
      exact he (repeatedTripleWords_mem_squareEvent ht hcut)
    simp [hempty,he]

end
end ImbalancedChen.P2EnhancedW1OrderedPositiveTripleWord
