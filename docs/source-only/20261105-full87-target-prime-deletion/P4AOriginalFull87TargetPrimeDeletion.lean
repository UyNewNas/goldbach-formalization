import ImbalancedChen.P4AOriginalFull87TerminalDensitySplit

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED / ZERO KERNEL CREDIT.

A real, manuscript-internal target-prime deletion estimate for the SAME
raw parity exit-series density. At a fixed rank, the paper's square tests
supply a positive lower last-prime cutoff. This file handles exactly the
omitted target-dividing primes in [lo,hi), with
g0(p) = 1/(p-1) on p>2.

The bound uses the ACTUAL prime factors of N, not an independent prime
set, and obtains a power/cardinality bound from their product dividing N.
It does NOT assert the missing square-test lower cutoff, uniform infinite
exit-series convergence, ordinary-density asymptotics or either reserve.
-/

namespace ImbalancedChen.P4AOriginalFull87TargetPrimeDeletion
noncomputable section
open scoped Classical BigOperators

/-- The literal target-dividing primes in a rank-j last-prime to y interval.
This is the factor set appearing in manuscript eq:current-raw-density. -/
def targetPrimeInterval (N lo hi : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun p => lo ≤ p ∧ p < hi)

/-- The EXACT target deletion multiplier for g0(p)=1/(p-1), provided
lo>=3; the lo>=3 constraint is a hypothesis of the estimates below. -/
def targetDeletionFactor (N lo hi : ℕ) : ℝ :=
  ∏ p ∈ targetPrimeInterval N lo hi, (1 - 1 / ((p : ℝ) - 1))

theorem mem_targetPrimeInterval (N lo hi p : ℕ) (hN : N ≠ 0) :
    p ∈ targetPrimeInterval N lo hi ↔
      p.Prime ∧ p ∣ N ∧ lo ≤ p ∧ p < hi := by
  rw [targetPrimeInterval, Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hd, _⟩, hlo, hhi⟩
    exact ⟨hp, hd, hlo, hhi⟩
  · rintro ⟨hp, hd, hlo, hhi⟩
    exact ⟨⟨hp, hd, hN⟩, hlo, hhi⟩

/-- A crucial target-UNIFORM finite-rank fact: the product of the
distinct omitted target primes is at most N. It is not enough to know
that each prime divides N separately. -/
theorem target_interval_power_card_le (N lo hi : ℕ) (hN : 0 < N) :
    lo ^ (targetPrimeInterval N lo hi).card ≤ N := by
  let S := targetPrimeInterval N lo hi
  have hsub : S ⊆ N.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hpow : lo ^ S.card ≤ ∏ p ∈ S, p := by
    calc
      lo ^ S.card = ∏ _p ∈ S, lo := by simp
      _ ≤ ∏ p ∈ S, p := by
        apply Finset.prod_le_prod
        intro p hp
        exact (Finset.mem_filter.mp hp).2.1
  have hsubsetprod :
      (∏ p ∈ S, p) ≤ ∏ p ∈ N.primeFactors, p := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsub
    intro p hp _
    exact (Nat.prime_of_mem_primeFactors hp).one_le
  exact hpow.trans (hsubsetprod.trans
    (Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)))

/-- For the fixed-rank lower cutoff, a single explicit power gap bounds
the number of deleted target factors, uniformly in the target N. -/
theorem target_interval_card_le_of_power_gap
    (N lo hi k : ℕ) (hN : 0 < N) (hlo : 1 ≤ lo)
    (hgap : N < lo ^ (k + 1)) :
    (targetPrimeInterval N lo hi).card ≤ k := by
  by_contra hcard
  have hksucc : k + 1 ≤ (targetPrimeInterval N lo hi).card := by omega
  have hpowers :
      lo ^ (k + 1) ≤ lo ^ (targetPrimeInterval N lo hi).card :=
    pow_right_mono₀ hlo hksucc
  have hsmall := target_interval_power_card_le N lo hi hN
  omega

/-- First Bonferroni inequality, proved for the finite product itself.
It does not use signed sieve monotonicity. -/
private theorem finite_product_one_sub_lower
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (h0 : ∀ p ∈ s, 0 ≤ f p) (h1 : ∀ p ∈ s, f p ≤ 1) :
    1 - ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1 - f p) := by
  classical
  revert h0 h1
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      simp
  | @insert p s hnot ih =>
      intro h0 h1
      have hp0 : 0 ≤ f p := h0 p (Finset.mem_insert_self p s)
      have hp1 : f p ≤ 1 := h1 p (Finset.mem_insert_self p s)
      have hs0 : ∀ q ∈ s, 0 ≤ f q := by
        intro q hq
        exact h0 q (Finset.mem_insert_of_mem hq)
      have hs1 : ∀ q ∈ s, f q ≤ 1 := by
        intro q hq
        exact h1 q (Finset.mem_insert_of_mem hq)
      have hi := ih hs0 hs1
      have hsum : 0 ≤ ∑ q ∈ s, f q := Finset.sum_nonneg hs0
      have hscaled := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hp1)
      simp only [Finset.sum_insert hnot, Finset.prod_insert hnot]
      nlinarith [mul_nonneg hp0 hsum]

/-- Exact finite estimate for the paper's omitted target factor. On every
fixed rank, any positive power lower cutoff lo has a small correction
as soon as its count is bounded; no PNT or Mertens theorem is used. -/
theorem target_deletion_card_sandwich (N lo hi : ℕ) (hlo : 3 ≤ lo) :
    0 ≤ targetDeletionFactor N lo hi ∧
    targetDeletionFactor N lo hi ≤ 1 ∧
    1 - ((targetPrimeInterval N lo hi).card : ℝ) /
      ((lo : ℝ) - 1) ≤ targetDeletionFactor N lo hi := by
  let S := targetPrimeInterval N lo hi
  let f : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1)
  have hlarge : ∀ p ∈ S, lo ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  have hloReal : (0 : ℝ) < (lo : ℝ) - 1 := by
    have hcast : (3 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
    linarith
  have hden : ∀ p ∈ S, (1 : ℝ) ≤ (p : ℝ) - 1 := by
    intro p hp
    have hnat : 2 ≤ p := (by omega : 2 ≤ lo).trans (hlarge p hp)
    have hcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hnat
    linarith
  have hf0 : ∀ p ∈ S, 0 ≤ f p := by
    intro p hp
    dsimp [f]
    exact div_nonneg (by norm_num) (by linarith [hden p hp])
  have hf1 : ∀ p ∈ S, f p ≤ 1 := by
    intro p hp
    dsimp [f]
    simpa using (one_div_le_one_div_of_le
      (show (0 : ℝ) < 1 by norm_num) (hden p hp))
  have hfsmall : ∀ p ∈ S, f p ≤ 1 / ((lo : ℝ) - 1) := by
    intro p hp
    have hcast : (lo : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hlarge p hp)
    have hdenle : (lo : ℝ) - 1 ≤ (p : ℝ) - 1 := by linarith
    exact one_div_le_one_div_of_le hloReal hdenle
  have hsum :
      (∑ p ∈ S, f p) ≤ (S.card : ℝ) / ((lo : ℝ) - 1) := by
    calc
      (∑ p ∈ S, f p) ≤
          ∑ _p ∈ S, (1 / ((lo : ℝ) - 1) : ℝ) :=
        Finset.sum_le_sum hfsmall
      _ = (S.card : ℝ) / ((lo : ℝ) - 1) := by
        simp [div_eq_mul_inv]
  have hfactor0 : ∀ p ∈ S, 0 ≤ 1 - f p := by
    intro p hp
    linarith [hf1 p hp]
  have hfactor1 : ∀ p ∈ S, 1 - f p ≤ 1 := by
    intro p hp
    linarith [hf0 p hp]
  have hprod0 : 0 ≤ ∏ p ∈ S, (1 - f p) :=
    Finset.prod_nonneg hfactor0
  have hprod1 : (∏ p ∈ S, (1 - f p)) ≤ 1 :=
    Finset.prod_le_one hfactor0 hfactor1
  have hbon := finite_product_one_sub_lower S f hf0 hf1
  change 0 ≤ (∏ p ∈ S, (1 - f p)) ∧
      (∏ p ∈ S, (1 - f p)) ≤ 1 ∧
      1 - (S.card : ℝ) / ((lo : ℝ) - 1) ≤
        (∏ p ∈ S, (1 - f p))
  exact ⟨hprod0, hprod1, by linarith⟩

/-- The actual uniform, finite-rank deletion payment.  The later
paper-specific square-test adapter must establish N < lo^(k+1);
this is an explicit arithmetic inequality, not an axiom or a requested
sieve-density asymptotic supplied as a hypothesis. -/
theorem target_deletion_power_gap_sandwich
    (N lo hi k : ℕ) (hN : 0 < N) (hlo : 3 ≤ lo)
    (hgap : N < lo ^ (k + 1)) :
    0 ≤ targetDeletionFactor N lo hi ∧
    targetDeletionFactor N lo hi ≤ 1 ∧
    1 - (k : ℝ) / ((lo : ℝ) - 1) ≤ targetDeletionFactor N lo hi := by
  have hbase := target_deletion_card_sandwich N lo hi hlo
  have hcard := target_interval_card_le_of_power_gap
    N lo hi k hN (by omega) hgap
  have hcast : ((targetPrimeInterval N lo hi).card : ℝ) ≤ k := by
    exact_mod_cast hcard
  have hden : (0 : ℝ) ≤ 1 / ((lo : ℝ) - 1) := by
    have hR : (3 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcast hden
  refine ⟨hbase.1, hbase.2.1, ?_⟩
  dsimp only at hmul
  have hbound :
      ((targetPrimeInterval N lo hi).card : ℝ) / ((lo : ℝ) - 1) ≤
        (k : ℝ) / ((lo : ℝ) - 1) := by
    simpa only [div_eq_mul_inv] using hmul
  linarith [hbase.2.2]

end
end ImbalancedChen.P4AOriginalFull87TargetPrimeDeletion
