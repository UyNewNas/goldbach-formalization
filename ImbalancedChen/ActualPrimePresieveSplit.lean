import ImbalancedChen.ActualSmallRosserFiniteDensity
import ImbalancedChen.FixedRoughCoefficients

/-!
# Exact ordered prime split for presieving

The decreasing actual prime carrier below `z` is the rough carrier
`[w,z)` followed by the small carrier below `w`. Both cutoffs are literal
real endpoints, and the same target exclusions and enumeration cap occur
on both sides. The corresponding retained polynomial is identified with
its fixed reciprocal-totient density before any projection estimate.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Splitting at a real cutoff preserves the exact decreasing scan order. -/
theorem roughPrimeUniverse_split (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    roughPrimeUniverse N cap 0 z =
      roughPrimeUniverse N cap w z ++ roughPrimeUniverse N cap 0 w := by
  classical
  have hcross : ∀ p ∈ roughPrimeUniverse N cap w z,
      ∀ q ∈ roughPrimeUniverse N cap 0 w, p > q := by
    intro p hp q hq
    have hpw := mem_roughPrimeUniverse_lower hp
    have hqw := mem_roughPrimeUniverse_upper hq
    have hqp : (q : ℝ) < p := hqw.trans_le hpw
    exact_mod_cast hqp
  have hgt : (roughPrimeUniverse N cap w z ++
      roughPrimeUniverse N cap 0 w).Pairwise (· > ·) := by
    rw [List.pairwise_append]
    exact ⟨roughPrimeUniverse_pairwise_gt N cap w z,
      roughPrimeUniverse_pairwise_gt N cap 0 w, hcross⟩
  have hcarrier : (roughPrimeUniverse N cap w z ++
      roughPrimeUniverse N cap 0 w).toFinset = roughPrimeFinset N cap 0 z := by
    ext p
    simp only [List.mem_toFinset, List.mem_append,
      mem_roughPrimeUniverse, mem_roughPrimeFinset]
    constructor
    · rintro (hp | hp)
      · exact ⟨hp.1, hp.2.1, hp.2.2.1, Nat.cast_nonneg _, hp.2.2.2.2⟩
      · exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
          hp.2.2.2.2.trans_le hwz⟩
    · intro hp
      by_cases hpw : (p : ℝ) < w
      · exact Or.inr ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hpw⟩
      · exact Or.inl ⟨hp.1, hp.2.1, hp.2.2.1,
          le_of_not_gt hpw, hp.2.2.2.2⟩
  change (roughPrimeFinset N cap 0 z).sort (· ≥ ·) = _
  rw [← hcarrier]
  exact (List.toFinset_sort (r := (· ≥ ·)) hgt.nodup).mpr
    (hgt.imp fun h => h.le)

/-- The small continuation product is the same target-deleted Euler product. -/
theorem roughPrimeUniverse_small_eulerProduct (N cap : ℕ) (w : ℝ) :
    ((roughPrimeUniverse N cap 0 w).map
      (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1))).prod =
        actualSmallEulerProduct N cap w := by
  unfold actualSmallEulerProduct actualSmallPrimeFinset
  rw [← roughPrimeUniverse_toFinset N cap 0 w]
  exact (List.prod_toFinset (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))
    (roughPrimeUniverse_nodup N cap 0 w)).symm

/-- Every actual prime reciprocal-totient local weight is in `[0,1]`.
This finite statement does not require evenness of the target. -/
theorem reciprocalTotientPrimeWeight_mem_Icc {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 : ℝ) / ((p : ℝ) - 1) ∧
      (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  exact ⟨div_nonneg zero_le_one hden.le, (div_le_one hden).mpr (by linarith)⟩

/-- Multiplicativity on the squarefree support, including the unit modulus. -/
theorem primeFactors_prod_reciprocalTotient {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) =
      1 / (Nat.totient d : ℝ) := by
  have ht : Nat.totient d = ∏ p ∈ d.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hd,
      Nat.div_self (Nat.pos_of_ne_zero hd.ne_zero), one_mul]
  rw [ht, Nat.cast_prod, Finset.prod_div_distrib]
  simp only [Finset.prod_const_one]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) (Nat.one_le_iff_ne_zero.mpr
    (Nat.prime_of_mem_primeFactors hp).ne_zero)).symm

/-- The actual retained polynomial has exactly the density of its fixed
modulus coefficient; no absolute values or changed support are introduced. -/
theorem oddFirstExitRetainedPolynomial_eq_fixedRoughDensity
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    oddFirstExitRetainedPolynomial retainOdd
        (fun p => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap w z) =
      reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
        (fixedRoughCoefficient retainOdd N cap w z) := by
  rw [oddFirstExitRetainedPolynomial_eq_leaves_sum,
    roughPrimeRetainedLeaves_sum_eq_retainedModuli_sum,
    oddFirstExitRetainedModuli_independent retainOdd
      (fun p => 1 / ((p : ℝ) - 1)) (fun _ => 1)]
  unfold reciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_reciprocalTotient
    (fixedRoughSupport_squarefree retainOdd N cap w z hd),
    oddFirstExitRetainedCoefficient_independent retainOdd
      (fun p => 1 / ((p : ℝ) - 1)) (fun _ => 1)]
  simp only [fixedRoughCoefficient, div_eq_mul_inv, one_mul]

end

end ImbalancedChen
