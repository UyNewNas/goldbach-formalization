import ImbalancedChen.Part3ElementaryTauTruncation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred

/-!
SOURCE PROPOSAL ONLY -- 2026-10-22 -- UNCOMPILED -- HOLD -- heavy0

Single finite task: compress the TRUE eraseAt deletion fibers through
Fin.succAbove, retain every ordered multiplicity, and close the original
native tau cutoff inequality with its exact natural-number hypotheses.
No interval counting, harmonic mean, E1/E3, kappa selection or main theorem
is attempted. No actual Lean/runtime/pin write, compiler, proper, checker,
classifier, census, cache, Git operation or subagent is used by this author.

Pinned native goldbach: 09b97db5764ade1246bfb77206baa1b124760958.
Pinned mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

SOURCE DEPENDENCIES / NO HIDDEN CARDINALITY ASSUMPTION:
The actual imported base module Part3ElementaryTauTruncation has SHA256
8e315aec5a3f00506ac26e8710474c47a448b043d3cf38be27c4df30c18a478f.
Root applied that frozen finite-core source; it is still uncompiled.
The complete eight-proof cardinality bridge, plus its three new helper
carrier/maps definitions, is copied VERBATIM below from lines 71-180 of
20261022-ordered-tau-cardinality-source-proposal.txt, SHA256
b997a96beac6c4eca23239b14147e51739a3009bcc2cdde497dcab52f8a910ce.
Its existing orderedFactorTuples definition is NOT repeated here: it comes
from the actual base module and is byte-identical to the reviewed carrier.
The prior cardinality proposal is under independent review; this copy does
not alter that proposal or preempt a later concrete review correction.
No target identity is introduced as an assumption. Future integration may
import the cardinality module and omit the verbatim copied proof block.

NEW FINITE ARGUMENT:
For b in deletionFiber S i d, b i=1 and product b=d. Define compression by
  compressDeleted k i b j = b (i.succAbove j), j : Fin k.
Fin.prod_univ_succAbove gives its full product d. Each coordinate divides
d by dvd_prod_of_mem, so it lies in the existing orderedFactorTuples k d
carrier when d>0. If two normalized b have equal compressed tuples, their
pivot coordinates both equal 1, and Fin.exists_succAbove_eq recovers each
off-pivot coordinate. Therefore compression is injective on the deletion
fiber; no ordered tuples are sorted, permuted into a quotient, or lost.
The proof in fact works for any finite S and positive d. The requested
K>=2, n>0, d in n.divisors specialization follows immediately.

Combine this cardinal bound with the explicit native cardinality bridge
and the old indexed-cover truncation theorem. The outer Fin K sum consists
of K copies of the same truncated divisor sum. The last theorem is exactly
  fouvryTau K n <= K * sum_{d|n,d<=D} fouvryTau (K-1) d,
for K>=2, n>=1, n^(K-1)<=D^K. No unproved supplier is added.

All proofs are complete AS WRITTEN source proposals; no elaboration or
kernel acceptance is claimed. E1 still additionally requires interval
counts Y/d+1 and the reciprocal/ordinary divisor means. E3 and all actual
cleanup applications, original forall-kappa obligations, and the main
theorem remain outside this task. Completion here is only finite tau
truncation, not completion of those analytic or parameter obligations.
-/

namespace ImbalancedChen.Part3.ElementaryTauTruncation

noncomputable section

open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/- BEGIN VERBATIM PRIOR CARDINALITY PROOFS: original lines 71-180. -/
/-- For n != 0 the coordinate divisor restrictions are consequences of the product. -/
theorem mem_orderedFactorTuples_iff {k n : ℕ} (hn : n ≠ 0) {a : Fin k → ℕ} :
    a ∈ orderedFactorTuples k n ↔ (∏ j, a j) = n := by
  constructor
  · intro ha
    exact (Finset.mem_filter.mp ha).2
  · intro hprod
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, hprod⟩
    intro i
    have hdiv : a i ∣ ∏ j, a j := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    exact Nat.mem_divisors.mpr ⟨by simpa only [hprod] using hdiv, hn⟩

/-- The empty tuple has product 1; its carrier has no other element. -/
theorem orderedFactorTuples_zero (n : ℕ) :
    orderedFactorTuples 0 n = if n = 1 then {Fin.elim0} else ∅ := by
  by_cases hn : n = 1
  · subst n
    rw [if_pos rfl]
    apply Finset.ext
    intro a
    constructor
    · intro _ha
      apply Finset.mem_singleton.mpr
      funext i
      exact Fin.elim0 i
    · intro _ha
      apply Finset.mem_filter.mpr
      exact ⟨Fintype.mem_piFinset.mpr (fun i => Fin.elim0 i), Fin.prod_univ_zero a⟩
  · rw [if_neg hn]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hprod : (∏ j : Fin 0, a j) = n := (Finset.mem_filter.mp ha).2
    have hone : 1 = n := (Fin.prod_univ_zero a).symm.trans hprod
    exact hn hone.symm

/-- A head value, the tail product, and the full ordered tail tuple. -/
def headTailCarrier (k n : ℕ) : Finset (Σ _ : ℕ × ℕ, Fin k → ℕ) :=
  n.divisorsAntidiagonal.sigma (fun p => orderedFactorTuples k p.2)

def splitHeadTail (k : ℕ) (a : Fin (k + 1) → ℕ) : Σ _ : ℕ × ℕ, Fin k → ℕ :=
  ⟨(a 0, ∏ j : Fin k, Fin.tail a j), Fin.tail a⟩

def joinHeadTail (k : ℕ) (p : Σ _ : ℕ × ℕ, Fin k → ℕ) : Fin (k + 1) → ℕ :=
  Fin.cons p.1.1 p.2

theorem splitHeadTail_mem {k n : ℕ} (hn : 0 < n) {a : Fin (k + 1) → ℕ}
    (ha : a ∈ orderedFactorTuples (k + 1) n) :
    splitHeadTail k a ∈ headTailCarrier k n := by
  have hprod : a 0 * (∏ j : Fin k, Fin.tail a j) = n := by
    simpa only [Fin.prod_univ_succ, Fin.tail] using (mem_orderedFactorTuples_iff hn.ne').mp ha
  have hpair : (a 0, ∏ j : Fin k, Fin.tail a j) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hn.ne'⟩
  have htail : Fin.tail a ∈ orderedFactorTuples k (∏ j : Fin k, Fin.tail a j) :=
    (mem_orderedFactorTuples_iff (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hpair)).mpr rfl
  exact Finset.mem_sigma.mpr ⟨hpair, htail⟩

theorem joinHeadTail_mem {k n : ℕ} (hn : 0 < n) {p : Σ _ : ℕ × ℕ, Fin k → ℕ}
    (hp : p ∈ headTailCarrier k n) :
    joinHeadTail k p ∈ orderedFactorTuples (k + 1) n := by
  obtain ⟨hpair, htail⟩ := Finset.mem_sigma.mp hp
  have htprod : (∏ j, p.2 j) = p.1.2 :=
    (mem_orderedFactorTuples_iff (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hpair)).mp htail
  apply (mem_orderedFactorTuples_iff hn.ne').mpr
  calc
    (∏ j, joinHeadTail k p j) = p.1.1 * ∏ j, p.2 j := Fin.prod_cons _ _
    _ = p.1.1 * p.1.2 := by rw [htprod]
    _ = n := (Nat.mem_divisorsAntidiagonal.mp hpair).1

theorem join_splitHeadTail (k : ℕ) (a : Fin (k + 1) → ℕ) :
    joinHeadTail k (splitHeadTail k a) = a := by
  exact Fin.cons_self_tail a

theorem split_joinHeadTail {k n : ℕ} {p : Σ _ : ℕ × ℕ, Fin k → ℕ}
    (hp : p ∈ headTailCarrier k n) : splitHeadTail k (joinHeadTail k p) = p := by
  rcases p with ⟨⟨v, d⟩, b⟩
  obtain ⟨hpair, hb⟩ := Finset.mem_sigma.mp hp
  have hbprod : (∏ j, b j) = d :=
    (mem_orderedFactorTuples_iff (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hpair)).mp hb
  simp only [splitHeadTail, joinHeadTail, Fin.cons_zero, Fin.tail_cons, hbprod]

/-- This is the same full divisor recurrence as native fouvryTau_succ. -/
theorem card_orderedFactorTuples_succ (k : ℕ) {n : ℕ} (hn : 0 < n) :
    (orderedFactorTuples (k + 1) n).card = ∑ d ∈ n.divisors, (orderedFactorTuples k d).card := by
  have hcard : (orderedFactorTuples (k + 1) n).card = (headTailCarrier k n).card :=
    Finset.card_nbij' (splitHeadTail k) (joinHeadTail k)
      (fun a ha => splitHeadTail_mem hn ha)
      (fun p hp => joinHeadTail_mem hn hp)
      (fun a _ha => join_splitHeadTail k a)
      (fun p hp => split_joinHeadTail hp)
  calc
    (orderedFactorTuples (k + 1) n).card = (headTailCarrier k n).card := hcard
    _ = ∑ p ∈ n.divisorsAntidiagonal, (orderedFactorTuples k p.2).card := by
      rw [headTailCarrier, Finset.card_sigma]
    _ = ∑ d ∈ n.divisors, (orderedFactorTuples k d).card :=
      Nat.sum_divisorsAntidiagonal' (fun _ d => (orderedFactorTuples k d).card)

/-- Every order, including zero, counts the exact current Fin-function carrier. -/
theorem card_orderedFactorTuples_eq_fouvryTau (k n : ℕ) (hn : 0 < n) :
    (orderedFactorTuples k n).card = fouvryTau k n := by
  induction k generalizing n with
  | zero =>
      by_cases hn1 : n = 1
      · simp [orderedFactorTuples_zero, fouvryTau, hn1]
      · simp [orderedFactorTuples_zero, fouvryTau, hn1]
  | succ k ih =>
      rw [card_orderedFactorTuples_succ k hn, fouvryTau_succ]
      apply Finset.sum_congr rfl
      intro d hd
      exact ih d (Nat.pos_of_mem_divisors hd)

/- END VERBATIM PRIOR CARDINALITY PROOFS. -/

section GeneralIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Updating the pivot to one leaves precisely the deleted product. -/
theorem prod_eraseAt (a : ι → ℕ) (i : ι) :
    (∏ j, eraseAt a i j) = deletedProduct a i := by
  have hdel : deletedProduct (eraseAt a i) i = deletedProduct a i := by
    apply Finset.prod_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 1 a
  have hi : eraseAt a i i = 1 := Function.update_self i 1 a
  have hp := deletedProduct_mul (eraseAt a i) i
  rw [hdel, hi, mul_one] at hp
  exact hp.symm

/-- These are properties of the actual deletion IMAGE, for an arbitrary S. -/
theorem deletionFiber_normalized (S : Finset (ι → ℕ)) {i : ι} {d : ℕ} {b : ι → ℕ}
    (hb : b ∈ deletionFiber S i d) : b i = 1 ∧ (∏ j, b j) = d := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  have had : deletedProduct a i = d := (Finset.mem_filter.mp ha).2
  exact ⟨Function.update_self i 1 a, (prod_eraseAt a i).trans had⟩

end GeneralIndex

/-- Read the remaining coordinates in their original Fin order, skipping i. -/
def compressDeleted (k : ℕ) (i : Fin (k + 1)) (b : Fin (k + 1) → ℕ) : Fin k → ℕ :=
  fun j => b (i.succAbove j)

theorem compressDeleted_prod {k : ℕ} (S : Finset (Fin (k + 1) → ℕ))
    {i : Fin (k + 1)} {d : ℕ} {b : Fin (k + 1) → ℕ}
    (hb : b ∈ deletionFiber S i d) : (∏ j, compressDeleted k i b j) = d := by
  have hinfo := deletionFiber_normalized S hb
  have hp := Fin.prod_univ_succAbove b i
  rw [hinfo.1, one_mul] at hp
  exact hp.symm.trans hinfo.2

/-- Every compressed coordinate divides d, with its original position preserved. -/
theorem compressDeleted_dvd {k : ℕ} (S : Finset (Fin (k + 1) → ℕ))
    {i : Fin (k + 1)} {d : ℕ} {b : Fin (k + 1) → ℕ}
    (hb : b ∈ deletionFiber S i d) (j : Fin k) : compressDeleted k i b j ∣ d := by
  have hp := compressDeleted_prod S hb
  have hdiv : compressDeleted k i b j ∣ ∏ r, compressDeleted k i b r :=
    Finset.dvd_prod_of_mem (compressDeleted k i b) (Finset.mem_univ j)
  simpa only [hp] using hdiv

/-- Explicit product-and-divisor verification for the full current tuple carrier. -/
theorem compressDeleted_mapsTo {k : ℕ} (S : Finset (Fin (k + 1) → ℕ))
    (i : Fin (k + 1)) {d : ℕ} (hd : 0 < d) :
    Set.MapsTo (compressDeleted k i) (deletionFiber S i d) (orderedFactorTuples k d) := by
  intro b hb
  apply Finset.mem_filter.mpr
  refine ⟨Fintype.mem_piFinset.mpr ?_, compressDeleted_prod S hb⟩
  intro j
  exact Nat.mem_divisors.mpr ⟨compressDeleted_dvd S hb j, hd.ne'⟩

/-- Normalization recovers the pivot, and succAbove recovers every other coordinate. -/
theorem compressDeleted_injective_of_normalized {k : ℕ} (i : Fin (k + 1))
    {b c : Fin (k + 1) → ℕ} (hb : b i = 1) (hc : c i = 1)
    (hbc : compressDeleted k i b = compressDeleted k i c) : b = c := by
  funext j
  by_cases hji : j = i
  · subst j
    exact hb.trans hc.symm
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hji
    have heval := congrFun hbc r
    simpa only [compressDeleted, hr] using heval

/-- A genuine injection of finite deletion images, without any fixed-product supplier. -/
theorem card_deletionFiber_le_orderedFactorTuples {k : ℕ}
    (S : Finset (Fin (k + 1) → ℕ)) (i : Fin (k + 1)) {d : ℕ} (hd : 0 < d) :
    (deletionFiber S i d).card ≤ (orderedFactorTuples k d).card := by
  refine Finset.card_le_card_of_injOn (compressDeleted k i) (compressDeleted_mapsTo S i hd) ?_
  intro b hb c hc hbc
  exact compressDeleted_injective_of_normalized i
    (deletionFiber_normalized S hb).1 (deletionFiber_normalized S hc).1 hbc

theorem card_deletionFiber_le_fouvryTau_succ {k : ℕ}
    (S : Finset (Fin (k + 1) → ℕ)) (i : Fin (k + 1)) {d : ℕ} (hd : 0 < d) :
    (deletionFiber S i d).card ≤ fouvryTau k d := by
  calc
    (deletionFiber S i d).card ≤ (orderedFactorTuples k d).card :=
      card_deletionFiber_le_orderedFactorTuples S i hd
    _ = fouvryTau k d := card_orderedFactorTuples_eq_fouvryTau k d hd

/-- The requested native K-1 fiber bound, with the exact original ordered carrier. -/
theorem card_deletionFiber_orderedFactorTuples_le_fouvryTau {K n d : ℕ}
    (hK : 2 ≤ K) (hn : 0 < n) (hd : d ∈ n.divisors) (i : Fin K) :
    (deletionFiber (orderedFactorTuples K n) i d).card ≤ fouvryTau (K - 1) d := by
  cases K with
  | zero => omega
  | succ k =>
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        (card_deletionFiber_le_fouvryTau_succ (orderedFactorTuples (k + 1) n) i
          (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn))

/-- Exact finite tau truncation; no interval, analytic, or kappa hypothesis is added. -/
theorem fouvryTau_le_truncated_divisor_sum {K n D : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) (hcut : n ^ (K - 1) ≤ D ^ K) :
    fouvryTau K n ≤ K *
      (∑ d ∈ n.divisors.filter (fun d => d ≤ D), fouvryTau (K - 1) d) := by
  calc
    fouvryTau K n = (orderedFactorTuples K n).card :=
      (card_orderedFactorTuples_eq_fouvryTau K n (by omega)).symm
    _ ≤ ∑ i : Fin K, ∑ d ∈ truncatedDivisors n D,
        (deletionFiber (orderedFactorTuples K n) i d).card :=
      card_orderedFactorTuples_truncated hK hn hcut
    _ ≤ ∑ _i : Fin K, ∑ d ∈ truncatedDivisors n D, fouvryTau (K - 1) d := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro d hd
      exact card_deletionFiber_orderedFactorTuples_le_fouvryTau hK (by omega)
        (Finset.mem_filter.mp hd).1 i
    _ = K * (∑ d ∈ n.divisors.filter (fun d => d ≤ D), fouvryTau (K - 1) d) := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
        truncatedDivisors]

end

end ImbalancedChen.Part3.ElementaryTauTruncation
