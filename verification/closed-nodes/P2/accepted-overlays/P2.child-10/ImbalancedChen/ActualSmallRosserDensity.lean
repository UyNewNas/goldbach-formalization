import ImbalancedChen.ActualSmallRosser
import ImbalancedChen.SmallRoughMainTerm
import MathlibNt.SieveTheory.LiLiuPrereqWFFundamentalLemma
import MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensityDimension

/-!
# Density of the same actual small-prime Rosser coefficients

The carrier is the literal set used by `ActualSmallRosser`: primes below
the presieve cutoff that do not divide the target. Thus this module does
not replace excluded primes merely by zero local densities while leaving
them in the physical coefficient.

The fixed dependency's proved fundamental lemma is applied to exactly
these lower and upper coefficients. Multiplicativity, prime-density bounds,
and one uniform dimension-one constant are supplied by proved theorems for
the actual progression density, rather than assumed as analytic premises.

The level is `D ^ epsilon` and the presieve cutoff is `D ^ (epsilon ^ 2)`.
Consequently the unrounded sieve coordinate is `1 / epsilon > 8`. For
fixed epsilon the exponential part of the displayed relative error is
constant in D; no fixed-epsilon little-o assertion is made here. This is
the small-weight density supplier, not the sharp density of the complete
causal rough-prime policy.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- The reciprocal-totient density of the same literal lower coefficient
whose pointwise polynomial is used in the physical majorant. -/
def actualSmallRosserMinusDensity (N cap : ℕ) (w L : ℝ) : ℝ :=
  reciprocalTotientDensity (actualSmallRosserSupport N cap w)
    (actualSmallRosserMinus N cap w L)

/-- The reciprocal-totient density of the same literal upper coefficient. -/
def actualSmallRosserPlusDensity (N cap : ℕ) (w L : ℝ) : ℝ :=
  reciprocalTotientDensity (actualSmallRosserSupport N cap w)
    (actualSmallRosserPlus N cap w L)

/-- The actual target-prime-deleted Goldbach Euler product. For even
targets the carrier automatically excludes the prime two. -/
def actualSmallEulerProduct (N cap : ℕ) (w : ℝ) : ℝ :=
  ∏ p ∈ actualSmallPrimeFinset N cap w, (1 - 1 / ((p : ℝ) - 1))

theorem actualSmallPrimeFinset_odd_of_even {N cap : ℕ} {w : ℝ}
    (hN : Even N) {p : ℕ} (hp : p ∈ actualSmallPrimeFinset N cap w) :
    Nat.Prime p ∧ 2 < p := by
  obtain ⟨_, hprime, hnot, _⟩ := mem_actualSmallPrimeFinset.mp hp
  have h2N : 2 ∣ N := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by omega⟩
  have hp2 := hprime.two_le
  have hne : p ≠ 2 := by
    intro heq
    subst p
    exact hnot h2N
  exact ⟨hprime, by omega⟩

/-- The provider's small-prime filter is exactly the already fixed physical
carrier, including its exclusion of primes dividing the target. -/
theorem geometricSmallPrimes_actualSmallPrimeFinset
    (N cap : ℕ) (D epsilon : ℝ) :
    geometricSmallPrimes (actualSmallPrimeFinset N cap (D ^ (epsilon ^ 2))) D epsilon =
      actualSmallPrimeFinset N cap (D ^ (epsilon ^ 2)) := by
  classical
  unfold geometricSmallPrimes
  apply Finset.filter_eq_self.mpr
  intro p hp
  have h := mem_actualSmallPrimeFinset.mp hp
  exact ⟨h.2.1, h.2.2.2⟩

theorem lowerSmallWeight_actualSmallPrimeFinset (N cap : ℕ) (D epsilon : ℝ) :
    (lowerSmallWeight (actualSmallPrimeFinset N cap (D ^ (epsilon ^ 2))) D epsilon :
        ℕ → ℝ) =
      actualSmallRosserMinus N cap (D ^ (epsilon ^ 2)) (D ^ epsilon) := by
  rw [lowerSmallWeight, geometricSmallPrimes_actualSmallPrimeFinset]
  rfl

theorem upperSmallWeight_actualSmallPrimeFinset (N cap : ℕ) (D epsilon : ℝ) :
    (upperSmallWeight (actualSmallPrimeFinset N cap (D ^ (epsilon ^ 2))) D epsilon :
        ℕ → ℝ) =
      actualSmallRosserPlus N cap (D ^ (epsilon ^ 2)) (D ^ epsilon) := by
  rw [upperSmallWeight, geometricSmallPrimes_actualSmallPrimeFinset]
  rfl

/-- On the actual physical divisor support every divisor is coprime to N,
so the supplied progression density is exactly the reciprocal totient. -/
theorem actualSmallRosserSupport_sourceDensity_eq
    (N cap : ℕ) (w : ℝ) (beta : ℕ → ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap w,
        beta d * (progressionOmega N d / (d : ℝ))) =
      reciprocalTotientDensity (actualSmallRosserSupport N cap w) beta := by
  classical
  unfold reciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro d hd
  have hcop := actualSmallRosserSupport_coprime_target N cap w hd
  rw [← primeDensity_apply, primeDensity_progressionOmega_apply]
  change beta d * (if d.Coprime N then (Nat.totient d : ℝ)⁻¹ else 0) =
    beta d / (Nat.totient d : ℝ)
  rw [if_pos hcop, div_eq_mul_inv]

theorem actualSmallEulerProduct_eq_source (N cap : ℕ) (w : ℝ) :
    (∏ p ∈ actualSmallPrimeFinset N cap w,
        (1 - progressionOmega N p / (p : ℝ))) =
      actualSmallEulerProduct N cap w := by
  classical
  unfold actualSmallEulerProduct
  apply Finset.prod_congr rfl
  intro p hp
  have h := mem_actualSmallPrimeFinset.mp hp
  have hcop : p.Coprime N := h.2.1.coprime_iff_not_dvd.mpr h.2.2.1
  rw [← primeDensity_apply, primeDensity_progressionOmega_apply,
    progressionDensity_prime N h.2.1, if_pos hcop]

/-- The exact relative error from the proved fundamental lemma. Its first
term is small when epsilon is chosen small, but does not decay with D. -/
def actualSmallRosserDensityError (C K D epsilon : ℝ) : ℝ :=
  C * (Real.exp (-(1 / epsilon)) +
    Real.exp (Real.sqrt K - 1 / epsilon) *
      (epsilon * Real.log D) ^ (-(1 / 3 : ℝ)))

/-- One absolute constant and one dimension constant work for every even
target and every enumeration cap. The threshold is chosen after epsilon
and before D, N, and cap. All analytic input hypotheses of the imported
fundamental lemma are discharged for the actual target-prime-deleted
carrier and the actual reciprocal-totient densities.

To cover all primes strictly below the presieve cutoff, choose `cap` with
`D ^ (epsilon ^ 2) ≤ cap`, as in the pointwise carrier theorem. The estimate
is also valid for a smaller finite carrier, so that condition is unnecessary
in this statement. The two densities are those of the same fixed weights. -/
theorem exists_actualSmallRosser_density_sandwich :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
          ∀ N cap : ℕ, Even N →
            let w := D ^ (epsilon ^ 2)
            let L := D ^ epsilon
            let V := actualSmallEulerProduct N cap w
            let E := actualSmallRosserDensityError C K D epsilon
            let lo := actualSmallRosserMinusDensity N cap w L
            let hi := actualSmallRosserPlusDensity N cap w L
            V * (1 - E) ≤ lo ∧ lo ≤ V ∧ V ≤ hi ∧
              hi ≤ V * (1 + E) ∧ hi - lo ≤ 2 * V * E := by
  classical
  obtain ⟨C, hC, hsource⟩ := exists_smallWeight_source_density_sandwich
  obtain ⟨K, hK, hdimension⟩ := exists_progressionOmega_dimensionOneProductBound
  refine ⟨C, K, hC, hK, ?_⟩
  intro epsilon hepsilon hepsilon8
  obtain ⟨D₀, hD₀, hsource⟩ := hsource epsilon hepsilon hepsilon8
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD N cap hN
  let P := actualSmallPrimeFinset N cap (D ^ (epsilon ^ 2))
  have hP : ∀ p ∈ P, Nat.Prime p ∧ 2 < p := by
    intro p hp
    exact actualSmallPrimeFinset_odd_of_even hN hp
  have hB : geometricSmallPrimes P D epsilon = P :=
    geometricSmallPrimes_actualSmallPrimeFinset N cap D epsilon
  have hprime : ∀ p ∈ geometricSmallPrimes P D epsilon,
      0 ≤ progressionOmega N p / (p : ℝ) ∧
        progressionOmega N p / (p : ℝ) < 1 := by
    intro p hp
    rw [hB] at hp
    exact progressionOmega_prime_nonneg_lt_one N (hP p hp).1 (hP p hp).2
  have h := hsource D hD P (progressionOmega N)
    (progressionOmega_isMultiplicative N) hprime K (by linarith)
    (hdimension N P hP)
  dsimp only at h ⊢
  rw [hB] at h
  have hlo : (∑ d ∈ (P.prod id).divisors,
      lowerSmallWeight P D epsilon d * (progressionOmega N d / (d : ℝ))) =
      actualSmallRosserMinusDensity N cap (D ^ (epsilon ^ 2)) (D ^ epsilon) := by
    change (∑ d ∈ actualSmallRosserSupport N cap (D ^ (epsilon ^ 2)),
      (lowerSmallWeight P D epsilon : ℕ → ℝ) d *
        (progressionOmega N d / (d : ℝ))) = _
    rw [show (lowerSmallWeight P D epsilon : ℕ → ℝ) =
      actualSmallRosserMinus N cap (D ^ (epsilon ^ 2)) (D ^ epsilon) from
        lowerSmallWeight_actualSmallPrimeFinset N cap D epsilon]
    exact actualSmallRosserSupport_sourceDensity_eq _ _ _ _
  have hhi : (∑ d ∈ (P.prod id).divisors,
      upperSmallWeight P D epsilon d * (progressionOmega N d / (d : ℝ))) =
      actualSmallRosserPlusDensity N cap (D ^ (epsilon ^ 2)) (D ^ epsilon) := by
    change (∑ d ∈ actualSmallRosserSupport N cap (D ^ (epsilon ^ 2)),
      (upperSmallWeight P D epsilon : ℕ → ℝ) d *
        (progressionOmega N d / (d : ℝ))) = _
    rw [show (upperSmallWeight P D epsilon : ℕ → ℝ) =
      actualSmallRosserPlus N cap (D ^ (epsilon ^ 2)) (D ^ epsilon) from
        upperSmallWeight_actualSmallPrimeFinset N cap D epsilon]
    exact actualSmallRosserSupport_sourceDensity_eq _ _ _ _
  have hV : (∏ p ∈ P, (1 - progressionOmega N p / (p : ℝ))) =
      actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) :=
    actualSmallEulerProduct_eq_source N cap (D ^ (epsilon ^ 2))
  rw [hlo, hhi, hV] at h
  exact h

end

end ImbalancedChen
