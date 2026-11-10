import ImbalancedChen.P2EnhancedW1R2ActualCarrierBranch
import ImbalancedChen.QuotientChenSwitchGeometry
import Mathlib.Data.Nat.Squarefree

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The r>=3 SAME-Q W1 finite switched-carrier branch.  Fix a true parent
receiver ell, old marked product B and quotient n=(N-ell)/B.  Let a<b
be its first two eligible active primes and q>b any later eligible
prime.  The triple multiplier B*a*b*q divides N-ell.  The plain
historyCarrier at the original next-to-last cutoff b has the enlarged
mask B*a*b*q*N; it is not the old-mask switched quotient carrier.
The latter is supplied only when a does not repeat in n.  Otherwise
the precise square event a^2 | n is retained explicitly.

Every later q gives a distinct canonical positive triple.  On the
squarefree branch, the actual old-mask quotient carriers and singleton
children pay the finite signed coefficient 2-r+(r-2)=0.  The square
exception and positive-product K estimate,
full enhanced action admission and asymptotic old H/h readings remain
separate.  No triple count licence is supplied as a premise.

Source: manuscript-body.tex 790--865;
same-new-level-double-sieve-route.tex, first-weighted inequality and
"The exact positive switched mass".
-/

namespace ImbalancedChen.P2EnhancedW1TripleActualCarrierBranch

noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2EnhancedW1FinitePrimeOwnership (activePrimes signed_coefficient_two_or_more)
open P2EnhancedW1R2ActualCarrierBranch
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2LargerSActualPositiveCounts (historyCarrier)
open P5OriginalActionMassBound (W1Target W1Anchor)

/-- The stricter switched quotient carrier: its sieve mask remains the
old B*N, while the physical multiplier is B*a*b*q and cutoff is b.
This is the quotient-side carrier in the prefix-mask defect comparison. -/
def oldMaskTripleCarrier (N B a b q : ℕ) (E : ℕ → ℕ → Prop) : Finset ℕ :=
  (sieveCarrier N (B*a*b*q) (B*N) (b : ℝ)).filter (fun ell => E B ell)

/-- One ordered W1 triple in the enlarged-mask historyCarrier.  The old
receiver predicate is retained literally, but this carrier alone is not
the old-mask switched quotient source. -/
theorem triple_child_frozen_history {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b q : ℕ}
    (hB : 0 < old.prod) (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hq : q ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b) (hbq : b < q)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r) :
    ell ∈ historyCarrier N (old.prod*a*b*q)
      (fun _ x => E old.prod x) (b : ℝ) := by
  let n := (N-ell)/old.prod
  have hda := eligiblePrime_data ha
  have hdb := eligiblePrime_data hb
  have hdq := eligiblePrime_data hq
  obtain ⟨hsource,hE⟩ := Finset.mem_filter.mp hell
  obtain ⟨hrange,hprime,hdiv,hsift⟩ := Finset.mem_filter.mp hsource
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hcomp hdiv) hB
  have hprod : a*b*q ∣ n :=
    chen_switch_triple_product_dvd hda.1 hdb.1 hdq.1 hab hbq
      hda.2.1 hdb.2.1 hdq.2.1
  have hchildDiv : old.prod*a*b*q ∣ N-ell := by
    simpa only [mul_assoc] using (Nat.dvd_div_iff_mul_dvd hdiv).mp hprod
  have hquotDiv : (N-ell)/(old.prod*a*b*q) ∣ n := by
    simpa only [Nat.div_div_eq_div_mul, mul_assoc] using
      Nat.div_dvd_of_dvd hprod
  have hmaskDiv : old.prod*N ∣ old.prod*a*b*q*N := by
    refine ⟨a*b*q, ?_⟩
    ring
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hrange,hprime,hchildDiv,?_⟩,hE⟩
  intro r hr hmask hrb hrchild
  have hrn : r ∣ n := hrchild.trans hquotDiv
  have hmaskOld : r.Coprime (old.prod*N) :=
    hmask.of_dvd_right hmaskDiv
  by_cases hry : (r : ℝ) < cutoff Q old.prod (W1Anchor j)
  · exact hsift r hr hmaskOld hry hrn
  · have hyl : cutoff Q old.prod (W1Anchor j) ≤ (r : ℝ) :=
      le_of_not_gt hry
    have hrz : (r : ℝ) < cutoff Q old.prod (W1Target i) :=
      hrb.trans hdb.2.2.2.1
    have hactive : r ∈ activePrimes n Q old i j := by
      apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_primeFactors.mpr ⟨hr,hrn,hn.ne'⟩,⟨hyl,hrz⟩⟩
    have helig : r ∈ eligiblePrimes N ell Q old i j :=
      Finset.mem_filter.mpr ⟨hactive,hmaskOld⟩
    have hra : r ≠ a := by
      intro heq
      subst r
      have hadiv : a ∣ old.prod*a*b*q*N := by
        refine ⟨old.prod*b*q*N, ?_⟩
        ring
      exact (hda.1.coprime_iff_not_dvd.mp hmask) hadiv
    exact (not_lt_of_ge (hsecond r helig hra)) hrb

/-- Every later prime owns an enlarged-mask historyCarrier child. -/
theorem every_later_prime_triple {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b : ℕ}
    (hB : 0 < old.prod) (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r) :
    ∀ q ∈ ((eligiblePrimes N ell Q old i j).erase a).erase b,
      ell ∈ historyCarrier N (old.prod*a*b*q)
        (fun _ x => E old.prod x) (b : ℝ) := by
  intro q hq
  have hqb : q ≠ b := (Finset.mem_erase.mp hq).1
  have hq' := (Finset.mem_erase.mp hq).2
  have hqa : q ≠ a := (Finset.mem_erase.mp hq').1
  have hqP := (Finset.mem_erase.mp hq').2
  have hbq : b < q := lt_of_le_of_ne (hsecond q hqP hqa) hqb.symm
  exact triple_child_frozen_history hB hcomp hell ha hb hqP hab hbq hsecond

/-- The enlarged-mask triple belongs to the old-mask switched quotient
carrier unless the first selected prime repeats in the old quotient. -/
theorem triple_oldmask_of_no_first_square {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b q : ℕ}
    (hB : 0 < old.prod) (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hq : q ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b) (hbq : b < q)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r)
    (hnoSquare : ¬ a^2 ∣ (N-ell)/old.prod) :
    ell ∈ oldMaskTripleCarrier N old.prod a b q E := by
  let n := (N-ell)/old.prod
  have hda := eligiblePrime_data ha
  have hdb := eligiblePrime_data hb
  have hdq := eligiblePrime_data hq
  obtain ⟨hsource,hE⟩ := Finset.mem_filter.mp hell
  obtain ⟨_,_,hdiv,hsift⟩ := Finset.mem_filter.mp hsource
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hcomp hdiv) hB
  have hprod : a*b*q ∣ n :=
    chen_switch_triple_product_dvd hda.1 hdb.1 hdq.1 hab hbq
      hda.2.1 hdb.2.1 hdq.2.1
  have hquotDiv : (N-ell)/(old.prod*a*b*q) ∣ n := by
    simpa only [Nat.div_div_eq_div_mul, mul_assoc] using
      Nat.div_dvd_of_dvd hprod
  have hchild := triple_child_frozen_history hB hcomp hell ha hb hq
    hab hbq hsecond
  obtain ⟨hchildSource,_⟩ := Finset.mem_filter.mp hchild
  obtain ⟨hrange,hprime,hchildDiv,_⟩ := Finset.mem_filter.mp hchildSource
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hrange,hprime,hchildDiv,?_⟩,hE⟩
  intro r hr hmask hrb hrchild
  have hrn : r ∣ n := hrchild.trans hquotDiv
  by_cases hry : (r : ℝ) < cutoff Q old.prod (W1Anchor j)
  · exact hsift r hr hmask hry hrn
  · have hyl : cutoff Q old.prod (W1Anchor j) ≤ (r : ℝ) :=
      le_of_not_gt hry
    have hrz : (r : ℝ) < cutoff Q old.prod (W1Target i) :=
      hrb.trans hdb.2.2.2.1
    have hactive : r ∈ activePrimes n Q old i j := by
      apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_primeFactors.mpr ⟨hr,hrn,hn.ne'⟩,⟨hyl,hrz⟩⟩
    have helig : r ∈ eligiblePrimes N ell Q old i j :=
      Finset.mem_filter.mpr ⟨hactive,hmask⟩
    have hra : r ≠ a := by
      intro heq
      subst r
      have haProd : a ∣ a*b*q := by
        refine ⟨b*q, ?_⟩
        ring
      have hquotEq : (N-ell)/(old.prod*a*b*q) = n/(a*b*q) := by
        simp only [Nat.div_div_eq_div_mul, mul_assoc]
      have haQuot : a ∣ n/(a*b*q) := by
        simpa only [hquotEq] using hrchild
      have hsqMul := mul_dvd_mul haProd haQuot
      have hsq : a^2 ∣ n := by
        simpa only [pow_two, Nat.mul_div_cancel' hprod] using hsqMul
      exact hnoSquare hsq
    exact (not_lt_of_ge (hsecond r helig hra)) hrb

/-- The repeated-prime surface is kept as an exact alternative; it is
not absorbed into the signed cancellation. -/
theorem triple_oldmask_or_first_square {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b q : ℕ}
    (hB : 0 < old.prod) (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hq : q ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b) (hbq : b < q)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r) :
    ell ∈ oldMaskTripleCarrier N old.prod a b q E ∨
      a^2 ∣ (N-ell)/old.prod := by
  by_cases hsq : a^2 ∣ (N-ell)/old.prod
  · exact Or.inr hsq
  · exact Or.inl (triple_oldmask_of_no_first_square hB hcomp hell
      ha hb hq hab hbq hsecond hsq)

/-- The isolated quotient-square exception is also a square in the
actual unscaled complement, the surface to be charged by the paper's
repeated-prime power-saving estimate. -/
theorem first_square_in_physical_complement {N ell B a : ℕ}
    (hdiv : B ∣ N-ell) (hsq : a^2 ∣ (N-ell)/B) :
    a^2 ∣ N-ell := by
  have hm := dvd_mul_of_dvd_right hsq B
  simpa only [Nat.mul_div_cancel' hdiv] using hm

theorem every_later_prime_oldmask_squarefree {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b : ℕ}
    (hB : 0 < old.prod) (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r)
    (hsf : Squarefree ((N-ell)/old.prod)) :
    ∀ q ∈ ((eligiblePrimes N ell Q old i j).erase a).erase b,
      ell ∈ oldMaskTripleCarrier N old.prod a b q E := by
  intro q hq
  have hqb : q ≠ b := (Finset.mem_erase.mp hq).1
  have hq' := (Finset.mem_erase.mp hq).2
  have hqa : q ≠ a := (Finset.mem_erase.mp hq').1
  have hqP := (Finset.mem_erase.mp hq').2
  have hbq : b < q := lt_of_le_of_ne (hsecond q hqP hqa) hqb.symm
  have hnoSquare : ¬ a^2 ∣ (N-ell)/old.prod := by
    intro hsq
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf a
      (eligiblePrime_data ha).1) (by simpa only [pow_two] using hsq)
  exact triple_oldmask_of_no_first_square hB hcomp hell ha hb hqP
    hab hbq hsecond hnoSquare

/-- On squarefree old quotients, canonical old-mask switched triples
pay every negative singleton.  The repeated-prime surface is excluded
from this equality and remains in `triple_oldmask_or_first_square`. -/
theorem later_prime_signed_cancellation {N ell : ℕ} {Q : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a b : ℕ}
    (hB : 0 < old.prod) (hcomp : 0 < N-ell)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b)
    (hsecond : ∀ r ∈ eligiblePrimes N ell Q old i j,
      r ≠ a → b ≤ r)
    (hsf : Squarefree ((N-ell)/old.prod)) :
    (2 : ℤ) -
      (∑ p ∈ eligiblePrimes N ell Q old i j,
        if ell ∈ historyCarrier N (old.prod*p)
          (fun _ x => E old.prod x)
          (cutoff Q old.prod (W1Anchor j)) then (1 : ℤ) else 0) +
      (∑ q ∈ ((eligiblePrimes N ell Q old i j).erase a).erase b,
        if ell ∈ oldMaskTripleCarrier N old.prod a b q E
          then (1 : ℤ) else 0) = 0 := by
  classical
  have hsingle (p : ℕ) (hp : p ∈ eligiblePrimes N ell Q old i j) :
      ell ∈ historyCarrier N (old.prod*p) (fun _ x => E old.prod x)
        (cutoff Q old.prod (W1Anchor j)) :=
    singleton_child_frozen_history hell (eligiblePrime_data hp).2.1
  have htriple := every_later_prime_oldmask_squarefree hB hcomp hell
    ha hb hab hsecond hsf
  have hsumSingle :
      (∑ p ∈ eligiblePrimes N ell Q old i j,
        if ell ∈ historyCarrier N (old.prod*p)
          (fun _ x => E old.prod x)
          (cutoff Q old.prod (W1Anchor j)) then (1 : ℤ) else 0) =
      (eligiblePrimes N ell Q old i j).card := by
    calc
      _ = ∑ _p ∈ eligiblePrimes N ell Q old i j, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [hsingle p hp]
      _ = _ := by simp
  have hsumTriple :
      (∑ q ∈ ((eligiblePrimes N ell Q old i j).erase a).erase b,
        if ell ∈ oldMaskTripleCarrier N old.prod a b q E
          then (1 : ℤ) else 0) =
      (((eligiblePrimes N ell Q old i j).erase a).erase b).card := by
    calc
      _ = ∑ _q ∈ ((eligiblePrimes N ell Q old i j).erase a).erase b,
          (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro q hq
        simp [htriple q hq]
      _ = _ := by simp
  have hcard : (((eligiblePrimes N ell Q old i j).erase a).erase b).card =
      (eligiblePrimes N ell Q old i j).card - 2 := by
    have hb' : b ∈ (eligiblePrimes N ell Q old i j).erase a :=
      Finset.mem_erase.mpr ⟨(ne_of_gt hab),hb⟩
    rw [Finset.card_erase_of_mem hb',Finset.card_erase_of_mem ha]
    omega
  have htwo : 2 ≤ (eligiblePrimes N ell Q old i j).card := by
    have hsub : ({a,b} : Finset ℕ) ⊆ eligiblePrimes N ell Q old i j := by
      intro p hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
    have hc := Finset.card_le_card hsub
    have hpair : ({a,b} : Finset ℕ).card=2 := by simp [ne_of_lt hab]
    omega
  have hnat : (eligiblePrimes N ell Q old i j).card =
      (((eligiblePrimes N ell Q old i j).erase a).erase b).card + 2 := by
    omega
  have hcast : ((eligiblePrimes N ell Q old i j).card : ℤ) =
      ((((eligiblePrimes N ell Q old i j).erase a).erase b).card : ℤ) + 2 := by
    exact_mod_cast hnat
  rw [hsumSingle,hsumTriple]
  omega

end
end ImbalancedChen.P2EnhancedW1TripleActualCarrierBranch
