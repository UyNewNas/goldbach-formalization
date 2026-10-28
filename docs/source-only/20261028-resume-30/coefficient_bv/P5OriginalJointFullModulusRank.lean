import ImbalancedChen.P5OriginalJointPresievedArithmeticSupport
import Mathlib.Data.Nat.PrimeFin

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The four original marked primes belong to the full physical modulus q.
Its prime-factor count is four PLUS the residual count.  Low rank in the
residual cannot be substituted for low total rank in a BV argument.

This file proves the exact arithmetic classification on the actual joint
support, and then specializes it to the manuscript's common-beta choice.
It proves no below-half bound and does not introduce a filtered BV licence.
-/

namespace ImbalancedChen.P5Z.OriginalJointFullModulusRank

noncomputable section
open Classical
open scoped BigOperators
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open OriginalJointCommonBetaModel OriginalCommonBetaActualParameters

/-- The original four prime labels, in the existing decreasing slot order. -/
def prefixPrimes (t : Four) : Finset ℕ := Finset.univ.image (slots t)

theorem prefixPrimes_card {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) : (prefixPrimes t).card = 4 := by
  rw [prefixPrimes, Finset.card_image_of_injective _ (slots_strictAnti ht).injective]
  simp

theorem prefixPrimes_prod {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) : (prefixPrimes t).prod id = fullPrefix t := by
  rw [prefixPrimes, Finset.prod_image]
  exact fun _ _ _ _ h => (slots_strictAnti ht).injective h

/-- No loss of marked primes occurs in prime-factor normalization. -/
theorem fullPrefix_primeFactors {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) : (fullPrefix t).primeFactors = prefixPrimes t := by
  rw [← prefixPrimes_prod ht]
  exact Nat.primeFactors_prod (fun p hp => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact slots_prime ht i)

theorem fullPrefix_rank {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) : (fullPrefix t).primeFactors.card = 4 := by
  rw [fullPrefix_primeFactors ht, prefixPrimes_card ht]

/-- Exact full-q rank at an actual original joint mark.  Coprimality is
proved by the existing physical row/prime-ceiling theorem, not assumed. -/
theorem joint_mark_full_rank {n N r : ℕ} {eta : ℚ} {w : ℝ}
    {E : ℕ × ℕ → Prop} (hN : 1 < N) (heta : 0 < eta) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hw : w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hr : r ∈ rowSupport n N eta w t) :
    (fullPrefix t * r).primeFactors.card = 4 + r.primeFactors.card := by
  have hs : t ∈ jointSelector N E := (Finset.mem_filter.mp ht).1
  have hpref : fullPrefix t ≠ 0 := by
    rw [fullPrefix_eq_multiplier]
    exact (joint_multiplier_pos hs).ne'
  have hres : r ≠ 0 := (rowSupport_smallPrimeSupportedAt hw hr).1
  have hcop := joint_row_coprime_prefix hN heta ht hw hr
  have hdis : Disjoint (fullPrefix t).primeFactors r.primeFactors :=
    (Nat.disjoint_primeFactors hpref hres).mpr hcop
  rw [Nat.primeFactors_mul hpref hres, Finset.card_union_of_disjoint hdis,
    fullPrefix_rank hs]

/-- The concrete row witness and its rank identity stay together. -/
theorem joint_support_rank_witness {n N q : ℕ} {eta : ℚ} {w : ℝ}
    {E : ℕ × ℕ → Prop} (hN : 1 < N) (heta : 0 < eta)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hq : q ∈ jointSupport n N eta w E) :
    ∃ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      ∃ r ∈ rowSupport n N eta w t,
        q = fullPrefix t * r ∧ q.primeFactors.card = 4 + r.primeFactors.card := by
  obtain ⟨m, hm, hmq⟩ := Finset.mem_image.mp hq
  obtain ⟨ht, hr⟩ := Finset.mem_sigma.mp hm
  have heq : q = fullPrefix m.1 * m.2 := hmq.symm
  refine ⟨m.1, ht, m.2, hr, heq, ?_⟩
  rw [heq]
  exact joint_mark_full_rank hN heta ht (hw m.1 ht) hr

/-- Every nonzero coefficient in the actual common-beta model has at
least four distinct prime factors in its FULL physical modulus. -/
theorem actual_nonzero_full_rank {n N q : ℕ} {eta : ℚ} {nu0 epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu0 : 0 < nu0) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0) (E : ℕ × ℕ → Prop)
    (hq : jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) E q ≠ 0) :
    4 ≤ q.primeFactors.card := by
  have hmem : q ∈ jointSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) E := by
    by_contra hnq
    exact hq (jointSigma_zero_off_support n N eta _ _ E hnq)
  obtain ⟨t, ht, r, hr, _, hcard⟩ := joint_support_rank_witness hN heta
    (fun t ht => (parameters_on_joint_row hN heta hnu0 he heBudget ht).1) hmem
  omega

/-- In particular the actual joint coefficient vanishes identically on
all total-rank-zero/one/two/three moduli. This is an exclusion, not BV. -/
theorem actual_joint_zero_of_total_rank_lt_four
    {n N q : ℕ} {eta : ℚ} {nu0 epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu0 : 0 < nu0) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0) (E : ℕ × ℕ → Prop)
    (hrank : q.primeFactors.card < 4) :
    jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) E q = 0 := by
  by_contra hq
  exact (not_le_of_gt hrank)
    (actual_nonzero_full_rank hN heta hnu0 he heBudget E hq)

/-- Exact emptiness of the attempted total-rank-two discrepancy class,
with arbitrary arithmetic test and arbitrary finite query set. -/
theorem actual_total_rank_two_signed_sum_eq_zero
    {n N : ℕ} {eta : ℚ} {nu0 epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu0 : 0 < nu0) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0) (E : ℕ × ℕ → Prop)
    (Q : Finset ℕ) (F : ℕ → ℝ) :
    (∑ q ∈ Q.filter (fun q => q.primeFactors.card ≤ 2),
      jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        ((N : ℝ) ^ (nu0 * epsilon)) E q * F q) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hrank : q.primeFactors.card < 4 := by
    have h := (Finset.mem_filter.mp hq).2
    omega
  rw [actual_joint_zero_of_total_rank_lt_four hN heta hnu0 he heBudget E hrank,
    zero_mul]

/-- A residual rank-k condition corresponds to total rank 4+k, never k. -/
theorem joint_mark_rank_cutoff_iff {n N r k : ℕ} {eta : ℚ} {w : ℝ}
    {E : ℕ × ℕ → Prop} (hN : 1 < N) (heta : 0 < eta) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hw : w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hr : r ∈ rowSupport n N eta w t) :
    (fullPrefix t * r).primeFactors.card ≤ 4 + k ↔ r.primeFactors.card ≤ k := by
  rw [joint_mark_full_rank hN heta ht hw hr]
  omega

end
end ImbalancedChen.P5Z.OriginalJointFullModulusRank
