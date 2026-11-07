import ImbalancedChen.U9RadicalReciprocalMass

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
At the actual strict sieve cap L<z, the normalizer's indices are exactly
the squarefree integers e≤L coprime to D. Grouping each positive coprime
harmonic index by its actual product of distinct prime factors and using
the genuine finite-prime Euler mass gives G_D(L)≥H_D(L).
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

def coprimeHarmonic (D L : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 L).filter (fun n => Nat.Coprime n D), 1 / (n : ℝ)

def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

private theorem primeFactors_subset_sieve {D L z n : ℕ} (hLz : L < z)
    (hn : n ∈ Finset.Icc 1 L) (hcop : Nat.Coprime n D) :
    n.primeFactors ⊆ sievePrimes D z := by
  intro p hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  apply mem_sievePrimes.mpr
  refine ⟨(Nat.le_of_dvd hnpos hpd).trans_lt ((Finset.mem_Icc.mp hn).2.trans_lt hLz), hpp, ?_⟩
  exact hpp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpd)

theorem ordinaryG_indices (D L z : ℕ) (hLz : L < z) :
    ((sieveProduct D z).divisors.filter fun e => e ≤ L) =
      (Finset.Icc 1 L).filter (fun e => Squarefree e ∧ Nat.Coprime e D) := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, heL⟩ := Finset.mem_filter.mp he
    have hd := Nat.dvd_of_mem_divisors heP
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors heP, heL⟩,
      (sieveProduct_squarefree D z).squarefree_of_dvd hd, coprime_of_dvd_sieveProduct hd⟩
  · intro he
    obtain ⟨heI, hesq, hecop⟩ := Finset.mem_filter.mp he
    have hs := primeFactors_subset_sieve hLz heI hecop
    have hd : e ∣ sieveProduct D z := by
      rw [← Nat.prod_primeFactors_of_squarefree hesq]
      exact Finset.prod_dvd_prod_of_subset _ _ id hs
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hd, (sieveProduct_squarefree D z).ne_zero⟩, (Finset.mem_Icc.mp heI).2⟩

theorem ordinaryG_eq_squarefree_sum (D L z : ℕ) (hLz : L < z) :
    ordinaryG D z L = ∑ e ∈ (Finset.Icc 1 L).filter
      (fun e => Squarefree e ∧ Nat.Coprime e D), 1 / (Nat.totient e : ℝ) := by
  rw [ordinaryG, ordinaryG_indices D L z hLz]

/-- The complete finite harmonic sum is grouped by actual radical fibres;
no coprimality or prime-power mass is supplied as an assumption. -/
theorem coprimeHarmonic_le_ordinaryG (D L z : ℕ) (hLz : L < z) :
    coprimeHarmonic D L ≤ ordinaryG D z L := by
  let S := (Finset.Icc 1 L).filter (fun n => Nat.Coprime n D)
  let E := (sieveProduct D z).divisors.filter (fun e => e ≤ L)
  have hmap : ∀ n ∈ S, radical n ∈ E := by
    intro n hn
    obtain ⟨hnI, hnCop⟩ := Finset.mem_filter.mp hn
    have hs := primeFactors_subset_sieve hLz hnI hnCop
    have hd : radical n ∣ sieveProduct D z := Finset.prod_dvd_prod_of_subset _ _ id hs
    have hnpos : 0 < n := (Finset.mem_Icc.mp hnI).1
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨hd, (sieveProduct_squarefree D z).ne_zero⟩,
      (Nat.le_of_dvd hnpos (Nat.prod_primeFactors_dvd n)).trans (Finset.mem_Icc.mp hnI).2⟩
  have hf := Finset.sum_fiberwise_of_maps_to (s := S) (t := E) (g := radical) hmap
    (fun n => 1 / (n : ℝ))
  change (∑ n ∈ S, 1 / (n : ℝ)) ≤ ∑ e ∈ E, 1 / (Nat.totient e : ℝ)
  rw [← hf]
  apply Finset.sum_le_sum
  intro e he
  have hepos := Nat.pos_of_mem_divisors (Finset.mem_filter.mp he).1
  apply finite_primeSupport_reciprocal_mass e hepos
  · intro n hn
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1
  · intro n hn
    have heq := (Finset.mem_filter.mp hn).2
    rw [← heq]
    exact Nat.prod_primeFactors_dvd n
  · intro n hn
    have heq := congrArg Nat.primeFactors (Finset.mem_filter.mp hn).2
    have hp : n.primeFactors = e.primeFactors := by
      simpa only [radical, Nat.primeFactors_prod_primeFactors] using heq
    intro p hpN
    simpa only [hp] using hpN

end
end ImbalancedChen.U9SemiprimeSwitch
