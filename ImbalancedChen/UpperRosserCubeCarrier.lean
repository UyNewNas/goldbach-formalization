import ImbalancedChen.ActualSmallRosser

/-!
# Exact first-cube truncation of the upper Rosser carrier

The first odd-prefix test forces every prime in an active upper coefficient
to satisfy the strict inequality `p^3 < R`. Removing the other carrier primes
therefore leaves the arithmetic function itself unchanged, including at an
integer real level and at levels at most one.

The density identity below explicitly restricts the divisor summation to the
smaller product. It holds for every test function, without an analytic or
multiplicativity assumption. It supplies no fixed-coordinate density limit.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

open MathlibNt.SieveTheory.LiLiuPrereqWF

/-- The largest selected natural number has a singleton first prefix, so
its strict cubic test bounds every member of an upper-admissible set. -/
theorem upperAdmissibleSet_mem_cube_lt
    {R : ℝ} {s : Finset ℕ} (hadm : SmallRosser.UpperAdmissibleSet R s)
    {p : ℕ} (hp : p ∈ s) : (p : ℝ) ^ 3 < R := by
  have hs : s.Nonempty := ⟨p, hp⟩
  let q := s.max' hs
  have hq : q ∈ s := Finset.max'_mem s hs
  have hfilter : s.filter (fun r => q ≤ r) = {q} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hqr⟩
      exact le_antisymm (Finset.le_max' s r hr) hqr
    · rintro rfl
      exact ⟨hq, le_rfl⟩
  have htest := hadm q hq (by simp [hfilter])
  rw [hfilter] at htest
  have hqCube : (q : ℝ) ^ 3 < R := by
    simpa [pow_succ, mul_assoc] using htest
  have hpq : (p : ℝ) ≤ q := by exact_mod_cast Finset.le_max' s p hp
  exact (pow_le_pow_left₀ (Nat.cast_nonneg p) hpq 3).trans_lt hqCube

/-- Every prime factor of a nonzero upper coefficient lies strictly below
the cubic level. This statement does not require a squarefree carrier. -/
theorem upperWeight_active_prime_cube_lt
    {M d : ℕ} {R : ℝ} (hd : SmallRosser.upperWeight M R d ≠ 0)
    {p : ℕ} (hp : p ∈ d.primeFactors) : (p : ℝ) ^ 3 < R :=
  upperAdmissibleSet_mem_cube_lt (SmallRosser.upperWeight_active hd).2.2 hp

/-- An admissible divisor of a finite prime product already divides the
product of its primes satisfying the strict cubic cutoff. -/
theorem mem_cubeFilter_divisors_of_upperAdmissibleSet
    (P : Finset ℕ) (R : ℝ) (hP : ∀ p ∈ P, p.Prime)
    {d : ℕ} (hd : d ∈ (P.prod id).divisors)
    (hadm : SmallRosser.UpperAdmissibleSet R d.primeFactors) :
    d ∈ ((P.filter fun p : ℕ => (p : ℝ) ^ 3 < R).prod id).divisors := by
  have hM := SmallRosser.primeProduct_squarefree P hP
  have hdM : d ∣ P.prod id := (Nat.mem_divisors.mp hd).1
  have hdsf : Squarefree d := Squarefree.squarefree_of_dvd hdM hM
  have hsub : d.primeFactors ⊆ P.filter (fun p : ℕ => (p : ℝ) ^ 3 < R) := by
    intro p hp
    have hpP : p ∈ P := by
      have h := Nat.primeFactors_mono hdM hM.ne_zero hp
      simpa only [id_eq, Nat.primeFactors_prod hP] using h
    exact Finset.mem_filter.mpr ⟨hpP, upperAdmissibleSet_mem_cube_lt hadm hp⟩
  rw [Nat.mem_divisors]
  refine ⟨?_, (SmallRosser.primeProduct_squarefree _
    (fun p hp => hP p (Finset.mem_filter.mp hp).1)).ne_zero⟩
  rw [← Nat.prod_primeFactors_of_squarefree hdsf]
  exact Finset.prod_dvd_prod_of_subset _ _ id hsub

/-- Divisors of the cubic subcarrier remain divisors of the original
nonzero prime product. -/
theorem cubeFilter_divisors_subset
    (P : Finset ℕ) (R : ℝ) (hP : ∀ p ∈ P, p.Prime) :
    ((P.filter fun p : ℕ => (p : ℝ) ^ 3 < R).prod id).divisors ⊆
      (P.prod id).divisors := by
  intro d hd
  rw [Nat.mem_divisors] at hd ⊢
  exact ⟨hd.1.trans (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)),
    (SmallRosser.primeProduct_squarefree P hP).ne_zero⟩

/-- Exact equality of the upper arithmetic functions after the first-cube
truncation. No lower bound on the real level is assumed. -/
theorem upperWeight_eq_cubeFilter
    (P : Finset ℕ) (R : ℝ) (hP : ∀ p ∈ P, p.Prime) :
    SmallRosser.upperWeight (P.prod id) R =
      SmallRosser.upperWeight
        ((P.filter fun p : ℕ => (p : ℝ) ^ 3 < R).prod id) R := by
  ext d
  have hcondition :
      (d ∈ (P.prod id).divisors ∧ (d : ℝ) < R ∧
        SmallRosser.UpperAdmissibleSet R d.primeFactors) ↔
      (d ∈ ((P.filter fun p : ℕ => (p : ℝ) ^ 3 < R).prod id).divisors ∧
        (d : ℝ) < R ∧ SmallRosser.UpperAdmissibleSet R d.primeFactors) := by
    constructor
    · rintro ⟨hd, hlevel, hadm⟩
      exact ⟨mem_cubeFilter_divisors_of_upperAdmissibleSet P R hP hd hadm,
        hlevel, hadm⟩
    · rintro ⟨hd, hlevel, hadm⟩
      exact ⟨cubeFilter_divisors_subset P R hP hd, hlevel, hadm⟩
  simp only [SmallRosser.upperWeight_apply]
  by_cases h : d ∈ (P.prod id).divisors ∧ (d : ℝ) < R ∧
      SmallRosser.UpperAdmissibleSet R d.primeFactors
  · rw [if_pos h, if_pos (hcondition.mp h)]
  · rw [if_neg h, if_neg (mt hcondition.mpr h)]

/-- The same exact truncation for weighted divisor densities. The two
divisor carriers are explicitly related by inclusion, and every omitted
coefficient vanishes. The test function can be arbitrary. -/
theorem upperWeight_density_eq_cubeFilter
    (P : Finset ℕ) (R : ℝ) (hP : ∀ p ∈ P, p.Prime) (g : ℕ → ℝ) :
    (∑ d ∈ (P.prod id).divisors,
      SmallRosser.upperWeight (P.prod id) R d * g d) =
    ∑ d ∈ ((P.filter fun p : ℕ => (p : ℝ) ^ 3 < R).prod id).divisors,
      SmallRosser.upperWeight
        ((P.filter fun p : ℕ => (p : ℝ) ^ 3 < R).prod id) R d * g d := by
  rw [upperWeight_eq_cubeFilter P R hP]
  symm
  apply Finset.sum_subset (cubeFilter_divisors_subset P R hP)
  intro d _hd hnot
  simp only [SmallRosser.upperWeight_apply, hnot, false_and, if_false, zero_mul]

end

end ImbalancedChen
