import ImbalancedChen.P2EnhancedW1FinitePrimeOwnership
import ImbalancedChen.P2LargerSActualPositiveCounts
import ImbalancedChen.P2PhysicalFrozenPrefixHistory

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The r=2 branch of the literal first-weighted W1 finite sieve inequality
at one unchanged Q.  A receiver ell in the actual parent historyCarrier
at y=(Q/B)^(1/s0) has residual quotient (N-ell)/B.  Two distinct eligible
prime divisors a,b in [y,z), z=(Q/B)^(1/v), exclude ell at z.  Each one
gives an actual child historyCarrier at multiplier B*q and cutoff y.
The child's quotient and its sieve mask are the literal (N-ell)/(B*q)
and B*q*N.  The original history predicate is frozen as E B ell.
The pointwise coefficient is exactly 2-1-1=0; no switched triple is
needed at r=2.

This is a genuine finite receiver-carrier branch, not a full enhanced
W1 action.  Admitting the appended prime in the computed stable-prefix
History.step and transporting its additional child predicate remains
separate.  Repeated factors and r>=3 are not silently discarded.

Source: manuscript-body.tex 790--865;
same-new-level-double-sieve-route.tex, first-weighted inequality.
-/

namespace ImbalancedChen.P2EnhancedW1R2ActualCarrierBranch

noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical
open P2EnhancedW1FinitePrimeOwnership (activePrimes activePrime_data)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2LargerSActualPositiveCounts (historyCarrier)
open P5OriginalActionMassBound (W1Target W1Anchor)
open P2EnhancedLowerPrimeChildCarriers (relativePrime physicalPrime)
open P2PhysicalFrozenPrefixHistory (History step)
open P2PhysicalIncomingPrefixCells (CapPlan)

/-- Original W1 prime window, with the required exclusion from the
existing B*N sieve mask.  The product B and total Q are unchanged. -/
def eligiblePrimes (N ell : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) : Finset ℕ :=
  (activePrimes ((N-ell)/old.prod) Q old i j).filter
    (fun q => q.Coprime (old.prod*N))

theorem eligiblePrime_data {N ell : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {q : ℕ}
    (hq : q ∈ eligiblePrimes N ell Q old i j) :
    q.Prime ∧ q ∣ (N-ell)/old.prod ∧
      cutoff Q old.prod (W1Anchor j) ≤ (q : ℝ) ∧
      (q : ℝ) < cutoff Q old.prod (W1Target i) ∧
      q.Coprime (old.prod*N) := by
  obtain ⟨ha,hcop⟩ := Finset.mem_filter.mp hq
  have hd := activePrime_data ha
  exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,hcop⟩

/-- Actual quotient child inclusion for ONE eligible W1 prime.  This
preserves the old receiver predicate exactly and proves new divisibility
and roughness from the parent carrier; no count bound is an input. -/
theorem singleton_child_frozen_history {N B ell q : ℕ} {E : ℕ → ℕ → Prop}
    {y : ℝ} (hell : ell ∈ historyCarrier N B E y)
    (hqdiv : q ∣ (N-ell)/B) :
    ell ∈ historyCarrier N (B*q) (fun _ x => E B x) y := by
  obtain ⟨hsource,hE⟩ := Finset.mem_filter.mp hell
  obtain ⟨hrange,hprime,hdiv,hsift⟩ := Finset.mem_filter.mp hsource
  have hchildDiv : B*q ∣ N-ell :=
    (Nat.dvd_div_iff_mul_dvd hdiv).mp hqdiv
  have hquotDiv : (N-ell)/(B*q) ∣ (N-ell)/B := by
    simpa only [Nat.div_div_eq_div_mul] using Nat.div_dvd_of_dvd hqdiv
  have hmaskDiv : B*N ∣ B*q*N := by
    refine ⟨q, ?_⟩
    ring
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hrange,hprime,hchildDiv,?_⟩,hE⟩
  intro r hr hmask hrz hrchild
  exact hsift r hr (hmask.of_dvd_right hmaskDiv) hrz
    (hrchild.trans hquotDiv)

/-- The literal computed W1 append on a frozen enhanced prefix.  Its
acceptance is a physical gate, not an arithmetic count hypothesis. -/
def w1HistoryChild {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (lo hi : ℝ) (H : History) (N : ℕ) (Q : ℝ)
    (old : List ℕ) (j : Fin 10) (q : ℕ) : History :=
  step plan lo hi H (physicalPrime N q)
    (W1Anchor j * (1-relativePrime Q old q))

/-- The old receiver test is retained literally and the computed child
acceptance is added.  No old cap or selected-slot tag is optimized anew. -/
def admittedChildPredicate (E : ℕ → ℕ → Prop) (B : ℕ)
    (child : History) : ℕ → ℕ → Prop :=
  fun _ ell => E B ell ∧ child.accepted=true

theorem singleton_child_computed_history {depth mesh N B ell q : ℕ}
    {Q y lo hi : ℝ} {old : List ℕ} {j : Fin 10}
    (plan : CapPlan depth mesh) (H : History)
    {E : ℕ → ℕ → Prop}
    (hell : ell ∈ historyCarrier N B E y)
    (hqdiv : q ∣ (N-ell)/B)
    (haccept : (w1HistoryChild plan lo hi H N Q old j q).accepted=true) :
    ell ∈ historyCarrier N (B*q)
      (admittedChildPredicate E B
        (w1HistoryChild plan lo hi H N Q old j q)) y := by
  have hfreeze := singleton_child_frozen_history hell hqdiv
  obtain ⟨hsource,hE⟩ := Finset.mem_filter.mp hfreeze
  exact Finset.mem_filter.mpr ⟨hsource,⟨hE,haccept⟩⟩

/-- Exactly two eligible active primes: the parent survives at y, is
excluded at z, and occurs in BOTH true singleton child carriers at y.
No positive switched term enters this branch. -/
theorem two_prime_actual_W1_branch (N ell : ℕ) (Q : ℝ)
    (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (E : ℕ → ℕ → Prop) {a b : ℕ}
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (hcard : (eligiblePrimes N ell Q old i j).card = 2)
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b) :
    eligiblePrimes N ell Q old i j = {a,b} ∧
    ell ∉ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Target i)) ∧
    ell ∈ historyCarrier N (old.prod*a) (fun _ x => E old.prod x)
      (cutoff Q old.prod (W1Anchor j)) ∧
    ell ∈ historyCarrier N (old.prod*b) (fun _ x => E old.prod x)
      (cutoff Q old.prod (W1Anchor j)) := by
  have hda := eligiblePrime_data ha
  have hdb := eligiblePrime_data hb
  have hsub : ({a,b} : Finset ℕ) ⊆ eligiblePrimes N ell Q old i j := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ha
    · exact hb
  have htwo : ({a,b} : Finset ℕ).card = 2 := by simp [ne_of_lt hab]
  have hset : eligiblePrimes N ell Q old i j = {a,b} :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hnot : ell ∉ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Target i)) := by
    intro hhigh
    obtain ⟨hsource,_⟩ := Finset.mem_filter.mp hhigh
    obtain ⟨_,_,_,hsift⟩ := Finset.mem_filter.mp hsource
    exact hsift a hda.1 hda.2.2.2.2 hda.2.2.2.1 hda.2.1
  exact ⟨hset,hnot,
    singleton_child_frozen_history hell hda.2.1,
    singleton_child_frozen_history hell hdb.2.1⟩

/-- If both literal W1 physical appends pass their computed frozen
history gates, the same r=2 receiver is in both admitted child carriers.
The gate hypotheses are actual `History.step` outputs, not count bounds. -/
theorem two_prime_computed_W1_children {depth mesh : ℕ}
    (plan : CapPlan depth mesh) (lo hi : ℝ) (H : History)
    (N ell : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop)
    {a b : ℕ}
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hacceptA : (w1HistoryChild plan lo hi H N Q old j a).accepted=true)
    (hacceptB : (w1HistoryChild plan lo hi H N Q old j b).accepted=true) :
    ell ∈ historyCarrier N (old.prod*a)
      (admittedChildPredicate E old.prod
        (w1HistoryChild plan lo hi H N Q old j a))
      (cutoff Q old.prod (W1Anchor j)) ∧
    ell ∈ historyCarrier N (old.prod*b)
      (admittedChildPredicate E old.prod
        (w1HistoryChild plan lo hi H N Q old j b))
      (cutoff Q old.prod (W1Anchor j)) := by
  have hda := (eligiblePrime_data ha).2.1
  have hdb := (eligiblePrime_data hb).2.1
  exact ⟨singleton_child_computed_history plan H hell hda hacceptA,
    singleton_child_computed_history plan H hell hdb hacceptB⟩

/-- The literal pointwise 2,-1,-1 sign for this r=2 actual carrier
branch. The singleton indicators refer to genuine child quotient counts. -/
theorem two_prime_signed_pointwise (N ell : ℕ) (Q : ℝ)
    (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (E : ℕ → ℕ → Prop) {a b : ℕ}
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (hcard : (eligiblePrimes N ell Q old i j).card = 2)
    (ha : a ∈ eligiblePrimes N ell Q old i j)
    (hb : b ∈ eligiblePrimes N ell Q old i j)
    (hab : a < b) :
    (if ell ∈ historyCarrier N old.prod E
        (cutoff Q old.prod (W1Target i)) then (2 : ℤ) else 0) ≤
      2 * (if ell ∈ historyCarrier N old.prod E
        (cutoff Q old.prod (W1Anchor j)) then (1 : ℤ) else 0) -
      (if ell ∈ historyCarrier N (old.prod*a) (fun _ x => E old.prod x)
        (cutoff Q old.prod (W1Anchor j)) then (1 : ℤ) else 0) -
      (if ell ∈ historyCarrier N (old.prod*b) (fun _ x => E old.prod x)
        (cutoff Q old.prod (W1Anchor j)) then (1 : ℤ) else 0) := by
  classical
  obtain ⟨_,hnot,hchildA,hchildB⟩ :=
    two_prime_actual_W1_branch N ell Q old i j E hell hcard ha hb hab
  simp [hnot,hell,hchildA,hchildB]

end
end ImbalancedChen.P2EnhancedW1R2ActualCarrierBranch
