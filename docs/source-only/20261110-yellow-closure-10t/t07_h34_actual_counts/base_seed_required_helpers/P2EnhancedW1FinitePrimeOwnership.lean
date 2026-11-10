import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted
import ImbalancedChen.P5OriginalActionMassBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite pointwise sign core of Wu's first-weighted action on ONE
same-Q W1 window.  For an integer with at least two distinct active
prime factors, choose its first two `a<b`.  Each further active prime
`q` owns the distinct ordered switched triple `[a,b,q]`.  There are
exactly `r-2` such triples for `r` active factors, paying all the
negative singleton coefficient beyond the first two:

     2 - r + (r-2) = 0.

The window is the literal `(Q/B)^(1/s0) <= q < (Q/B)^(1/v)` from one
selected original W1 action; no new Q or saved table is used.  This
is only a combinatorial sign/ownership lemma.  It does NOT identify
each triple with a `historyCarrier` quotient, prove the pointwise
sieve count inequality, or pay repeated-prime exceptions.

Source: manuscript-body.tex 790--865 and
same-new-level-double-sieve-route.tex, first-weighted inequality.
-/

namespace ImbalancedChen.P2EnhancedW1FinitePrimeOwnership

noncomputable section
open Finset
open scoped BigOperators
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalActionMassBound (W1Target W1Anchor)

/-- The distinct prime divisors in the actual W1 first-weighted window
for a fixed old marked product and unchanged total level Q. -/
def activePrimes (n : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) : Finset ℕ :=
  n.primeFactors.filter (fun q =>
    cutoff Q old.prod (W1Anchor j) ≤ (q : ℝ) ∧
      (q : ℝ) < cutoff Q old.prod (W1Target i))

theorem activePrime_data {n : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {q : ℕ}
    (hq : q ∈ activePrimes n Q old i j) :
    q.Prime ∧ q ∣ n ∧
      cutoff Q old.prod (W1Anchor j) ≤ (q : ℝ) ∧
      (q : ℝ) < cutoff Q old.prod (W1Target i) := by
  obtain ⟨hfactor, hwindow⟩ := Finset.mem_filter.mp hq
  have hp := Nat.mem_primeFactors.mp hfactor
  exact ⟨hp.1, hp.2.1, hwindow.1, hwindow.2⟩

/-- Canonical triple witnesses with the first two active primes fixed.
No triple is charged twice, because its last prime remains a label. -/
def canonicalTriples (P : Finset ℕ) (a b : ℕ) :
    Finset (Fin 3 → ℕ) :=
  ((P.erase a).erase b).image (fun q => ![a,b,q])

theorem canonicalTriples_member {P : Finset ℕ} {a b : ℕ}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a < b)
    (hsecond : ∀ q ∈ P, q ≠ a → b ≤ q)
    {t : Fin 3 → ℕ} (ht : t ∈ canonicalTriples P a b) :
    ∃ q ∈ P, b < q ∧ t = ![a,b,q] ∧
      ∀ r ∈ ((P.erase a).erase b).erase q, b ≤ r := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
  have hqb : q ≠ b := (Finset.mem_erase.mp hq).1
  have hqa : q ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
  have hqP : q ∈ P := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).2
  have hrough : ∀ r ∈ ((P.erase a).erase b).erase q, b ≤ r := by
    intro r hr
    have hr' := (Finset.mem_erase.mp hr).2
    have hr'' := (Finset.mem_erase.mp hr').2
    have hrP := (Finset.mem_erase.mp hr'').2
    have hra := (Finset.mem_erase.mp hr'').1
    exact hsecond r hrP hra
  exact ⟨q,hqP,lt_of_le_of_ne (hsecond q hqP hqa) hqb.symm, rfl,hrough⟩

/-- One injective switched triple for each active prime after the first
two.  The equality is literal finite cardinality, not an asymptotic. -/
theorem canonicalTriples_card {P : Finset ℕ} {a b : ℕ}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a < b) :
    (canonicalTriples P a b).card = P.card - 2 := by
  classical
  have hb' : b ∈ P.erase a :=
    Finset.mem_erase.mpr ⟨(ne_of_gt hab),hb⟩
  have hinj : Function.Injective (fun q : ℕ => (![a,b,q] : Fin 3 → ℕ)) := by
    intro q r h
    have hlast := congrFun h (2 : Fin 3)
    simpa using hlast
  unfold canonicalTriples
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_erase_of_mem hb',Finset.card_erase_of_mem ha]
  omega

/-- The finite signed coefficient is exactly zero once two distinct
active factors have appeared. The canonical positive triples own every
remaining negative singleton. -/
theorem signed_coefficient_two_or_more {P : Finset ℕ} {a b : ℕ}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a < b) :
    (2 : ℤ) - (P.card : ℤ) +
      ((canonicalTriples P a b).card : ℤ) = 0 := by
  have hcard := canonicalTriples_card ha hb hab
  have hsub : ({a,b} : Finset ℕ) ⊆ P := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ha
    · exact hb
  have htwo : 2 ≤ P.card := by
    have hbound := Finset.card_le_card hsub
    have hpair : ({a,b} : Finset ℕ).card = 2 := by simp [ne_of_lt hab]
    omega
  have hnat : P.card = (canonicalTriples P a b).card + 2 := by omega
  have hcast : (P.card : ℤ) = ((canonicalTriples P a b).card : ℤ) + 2 := by
    exact_mod_cast hnat
  omega

/-- At zero or one active prime the first-weighted coefficient is already
nonnegative, without a switched triple.  The left indicator is two only
in the empty-prime case. -/
theorem signed_coefficient_at_most_one (P : Finset ℕ) (hcard : P.card ≤ 1) :
    (if P.card = 0 then (2 : ℤ) else 0) ≤ 2 - (P.card : ℤ) := by
  by_cases hzero : P.card = 0
  · simp [hzero]
  · have hone : P.card = 1 := by omega
    simp [hzero, hone]

/-- Direct instance for one actual W1 window.  The first-two hypothesis
is the ordered-factor ownership condition, not an assumed W1 count bound. -/
theorem actual_window_signed_ownership (n : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) {a b : ℕ}
    (ha : a ∈ activePrimes n Q old i j)
    (hb : b ∈ activePrimes n Q old i j)
    (hab : a < b)
    (hsecond : ∀ q ∈ activePrimes n Q old i j, q ≠ a → b ≤ q) :
    (2 : ℤ) - ((activePrimes n Q old i j).card : ℤ) +
      ((canonicalTriples (activePrimes n Q old i j) a b).card : ℤ) = 0 ∧
    (∀ t ∈ canonicalTriples (activePrimes n Q old i j) a b,
      ∃ q ∈ activePrimes n Q old i j, b < q ∧ t = ![a,b,q] ∧
        ∀ r ∈ (((activePrimes n Q old i j).erase a).erase b).erase q,
          b ≤ r) := by
  exact ⟨signed_coefficient_two_or_more ha hb hab,
    fun _ ht => canonicalTriples_member ha hb hab hsecond ht⟩

end
end ImbalancedChen.P2EnhancedW1FinitePrimeOwnership
