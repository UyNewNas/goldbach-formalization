import ImbalancedChen.P5OriginalU5FrozenSource
import ImbalancedChen.P2AllW2ImmutableCountRecursion
import ImbalancedChen.ChenQuotientCentreBudget
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

J identifies the original prime receiver as E_N(ell) = Coprime ell N.
The complement costs left by I's actual W2 recursion therefore count
centre primes, with their literal divisible source and strict cutoff.
This file pools those costs BEFORE taking bounds.  A pair family costs
three logarithms, independently of the number of primes in its windows,
its cutoffs, the old prefix and the full-square predicate.

This is a bound on a specific unpaid source cost.  It assumes neither an
enhanced seed, a W2 analytic bound, an H247 licence, nor a count error.
It does not assert the same estimate for arbitrary frozen receivers.
-/
namespace ImbalancedChen.P2OriginalW2CentreIncidence

noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions P2W2PhysicalChildFeedback
open P5OriginalU5FrozenSource (receiver)
open scoped Classical BigOperators

def logRank (N : ℕ) : ℝ := Real.log (N : ℝ) / Real.log 2

theorem logRank_nonnegative (N : ℕ) : 0 ≤ logRank N :=
  div_nonneg (Real.log_natCast_nonneg N) (Real.log_pos (by norm_num)).le

/-- The retained complement consists exactly of centre-prime labels
with the old complete divisibility and sifting tests. -/
theorem complement_carrier (N d : ℕ) (z : ℝ) :
    frozenCarrier N d (fun ell => ¬ receiver N ell) z =
      (chenCentrePrimeCarrier N).filter
        (fun ell => d ∣ N-ell ∧ Sifted (d*N) (N-ell) z) := by
  ext ell
  simp only [frozenCarrier, sourceSieveCarrier, receiver, mem_filter,
    mem_range, Nat.lt_succ_iff, mem_chenCentrePrimeCarrier]
  constructor
  · rintro ⟨⟨hle, hp, hd, hs⟩, hnot⟩
    have hdiv : ell ∣ N := by
      by_contra hn
      exact hnot (hp.coprime_iff_not_dvd.mpr hn)
    exact ⟨⟨hle, hp, hdiv⟩, hd, hs⟩
  · rintro ⟨⟨hle, hp, hdiv⟩, hd, hs⟩
    refine ⟨⟨hle, hp, hd, hs⟩, ?_⟩
    intro hc
    exact (hp.coprime_iff_not_dvd.mp hc) hdiv

theorem complement_nonnegative (N d : ℕ) (z : ℝ) :
    0 ≤ complementCount N d (receiver N) z := by
  unfold complementCount frozenCount
  positivity

/-- No cutoff or mask equality is assumed: forgetting sifting only
enlarges the actual deleted-prime incidence. -/
theorem complement_le_centre (N d : ℕ) (z : ℝ) :
    complementCount N d (receiver N) z ≤ chenCentrePrimeAPCount N N d := by
  rw [chenCentrePrimeAPCount_eq_filter_dvd]
  have hs : frozenCarrier N d (fun ell => ¬ receiver N ell) z ⊆
      (chenCentrePrimeCarrier N).filter (fun ell => d ∣ N-ell) := by
    rw [complement_carrier]
    intro ell hell
    exact mem_filter.mpr ⟨(mem_filter.mp hell).1, (mem_filter.mp hell).2.1⟩
  change ((frozenCarrier N d (fun ell => ¬ receiver N ell) z).card : ℝ) ≤ _
  exact_mod_cast card_le_card hs

theorem complement_le_logRank {N : ℕ} (hN : 0<N) (d : ℕ) (z : ℝ) :
    complementCount N d (receiver N) z ≤ logRank N := by
  have hs : (chenCentrePrimeCarrier N).filter (fun ell => d ∣ N-ell) ⊆
      chenCentrePrimeCarrier N := filter_subset _ _
  have hc : chenCentrePrimeAPCount N N d ≤ chenPrimeDivisorCount N N := by
    rw [chenCentrePrimeAPCount_eq_filter_dvd]
    change (((chenCentrePrimeCarrier N).filter (fun ell => d ∣ N-ell)).card : ℝ) ≤
      ((chenCentrePrimeCarrier N).card : ℝ)
    exact_mod_cast card_le_card hs
  exact (complement_le_centre N d z).trans
    (hc.trans (chenPrimeDivisorCount_le_log N hN))

/-- A finite prime-pair incidence lemma, retaining both ordered labels.
No injectivity of their product and no squarefree receiver is required. -/
theorem pair_incidence_card {n : ℕ} (hn : n≠0) (P R : Finset ℕ)
    (hP : ∀ p∈P, p.Prime) (hR : ∀ q∈R, q.Prime) :
    ((P ×ˢ R).filter (fun t => t.1*t.2 ∣ n)).card ≤ n.primeFactors.card^2 := by
  have hs : (P ×ˢ R).filter (fun t => t.1*t.2 ∣ n) ⊆
      n.primeFactors ×ˢ n.primeFactors := by
    intro t ht
    obtain ⟨ht, hd⟩ := mem_filter.mp ht
    obtain ⟨hp,hq⟩ := mem_product.mp ht
    exact mem_product.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hP _ hp, (dvd_mul_right t.1 t.2).trans hd, hn⟩,
        Nat.mem_primeFactors.mpr ⟨hR _ hq, (dvd_mul_left t.2 t.1).trans hd, hn⟩⟩
  simpa only [card_product, pow_two] using card_le_card hs

theorem pair_centre_mass_le {N : ℕ} (hN : 0<N) (hNP : ¬N.Prime)
    (P R : Finset ℕ) (hP : ∀ p∈P, p.Prime) (hR : ∀ q∈R, q.Prime) :
    (∑ p∈P, ∑ q∈R, chenCentrePrimeAPCount N N (p*q)) ≤ logRank N^3 := by
  have hinc : ∀ ell∈chenCentrePrimeCarrier N,
      (((P ×ˢ R).filter (fun t => t.1*t.2 ∣ N-ell)).card : ℝ) ≤ logRank N^2 := by
    intro ell hell
    have hn := chenCentrePrimeCarrier_sub_pos hNP hell
    have hc : (((P ×ˢ R).filter (fun t => t.1*t.2 ∣ N-ell)).card : ℝ) ≤
        ((N-ell).primeFactors.card : ℝ)^2 := by
      exact_mod_cast pair_incidence_card hn.ne' P R hP hR
    exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (chen_primeFactors_card_le_log_of_le hn (Nat.sub_le N ell)) 2)
  calc
    _ = chenSelectedCentreMass N (P ×ˢ R) (fun t => t.1*t.2) := by
      simp only [chenSelectedCentreMass, sum_product]
    _ ≤ chenPrimeDivisorCount N N * logRank N^2 :=
      chenSelectedCentreMass_le_of_incidence_bound N _ _ _ hinc
    _ ≤ logRank N * logRank N^2 :=
      mul_le_mul_of_nonneg_right (chenPrimeDivisorCount_le_log N hN) (sq_nonneg _)
    _ = _ := by ring

/-- Arbitrary genuine gates and row-dependent cutoffs can only reduce
the nonnegative complement mass. The old d is removed by divisibility,
not by assuming it coprime to either selected prime. -/
theorem gated_pair_complements_le {N : ℕ} (hN : 0<N) (hNP : ¬N.Prime)
    (d : ℕ) (P R : Finset ℕ) (hP : ∀ p∈P, p.Prime) (hR : ∀ q∈R, q.Prime)
    (gate : ℕ → ℕ → Prop) (z : ℕ → ℕ → ℝ) :
    (∑ p∈P, ∑ q∈R, if gate p q then
      complementCount N (d*p*q) (receiver N) (z p q) else 0) ≤ logRank N^3 := by
  apply le_trans _ (pair_centre_mass_le hN hNP P R hP hR)
  apply sum_le_sum
  intro p hp
  apply sum_le_sum
  intro q hq
  split_ifs
  · exact (complement_le_centre N (d*p*q) (z p q)).trans (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        chenCentrePrimeAPCount_mul_le N (p*q) d)
  · exact chenCentrePrimeAPCount_nonneg N N (p*q)

end
end ImbalancedChen.P2OriginalW2CentreIncidence
