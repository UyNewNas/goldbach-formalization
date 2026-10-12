import ImbalancedChen.ActualPrimeBoxMass
import ImbalancedChen.FullPowerEulerNormalization
import ImbalancedChen.RoughPowerParameters
import ImbalancedChen.SieveDimensionComparison

/-!
# Lower mass of actual prime boxes with a boundary Euler ratio

The sum below is over actual prime tuples, with the same target exclusions
as the one-prime mass supplier. A specified coordinate supplies the strict
lower Euler cutoff. Monotonicity bounds this ratio throughout the box by
its value at that coordinate's upper endpoint. The full power Euler ratio
and the proved tuple mass then give one eventual lower bound, uniformly in
every enumeration cap covering the outer cutoff.

This does not assert that the box satisfies the Rosser boundary predicate.
That finite geometric inclusion must be proved when inserting such a box
into the exact positive boundary expansion.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Filter Topology

/-- A covered actual Euler product decreases as its strict cutoff grows. -/
theorem actualSmallEulerProduct_antitone_cutoff
    (N cap : ℕ) (hEven : Even N) (x y : ℝ)
    (hxy : x ≤ y) (hycap : y ≤ (cap : ℝ)) :
    actualSmallEulerProduct N cap y ≤ actualSmallEulerProduct N cap x := by
  rw [actualSmallEulerProduct_eq_finiteSieveDensity N cap y hycap,
    actualSmallEulerProduct_eq_finiteSieveDensity N cap x (hxy.trans hycap)]
  exact finiteSieveDensity_antitone hEven (Nat.ceil_mono hxy)

/-- The actual tuple mass weighted by the strict Euler ratio at one
coordinate. To use it as a Rosser boundary contribution, this coordinate
must separately be shown to be the least selected prime. -/
def actualPrimeBoxEulerMass {k : ℕ} (N cap : ℕ) (a b : Fin k → ℝ)
    (u : ℝ) (j : Fin k) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N a b,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (actualSmallEulerProduct N cap (p j : ℝ) /
        actualSmallEulerProduct N cap ((N : ℝ) ^ u))

/-- The ratio at the coordinate's upper endpoint is a simultaneous lower
bound throughout the actual box. Only that coordinate needs to lie below
the outer cutoff for this numerical inequality. -/
theorem actualPrimeBoxEulerMass_ge_endpoint_ratio
    {k : ℕ} (N cap : ℕ) (hN : 1 < N) (hEven : Even N)
    (a b : Fin k → ℝ) (u : ℝ) (j : Fin k)
    (hbu : b j ≤ u) (hcap : (N : ℝ) ^ u ≤ (cap : ℝ)) :
    (actualSmallEulerProduct N cap ((N : ℝ) ^ b j) /
        actualSmallEulerProduct N cap ((N : ℝ) ^ u)) *
      actualPrimeBoxMass N a b ≤ actualPrimeBoxEulerMass N cap a b u j := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbcap : (N : ℝ) ^ b j ≤ (cap : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN1 hbu).trans hcap
  rw [actualPrimeBoxMass, actualPrimeBoxEulerMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpb : (p j : ℝ) ≤ (N : ℝ) ^ b j :=
    ((mem_actualPrimeBoxTuples_iff.mp hp) j).2.2.2.le
  have hV := actualSmallEulerProduct_antitone_cutoff N cap hEven
    (p j : ℝ) ((N : ℝ) ^ b j) hpb hbcap
  have hratio := div_le_div_of_nonneg_right hV
    (actualSmallEulerProduct_pos N cap ((N : ℝ) ^ u) hEven).le
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hratio (actualPrimeBoxWeight_nonneg hp)

/-- A genuine lower asymptotic for the weighted actual box. The threshold
is chosen before the varying even target and every covering natural cap.
The only analytic inputs are the proved Euler-ratio and prime-tuple limits. -/
theorem exists_actualPrimeBoxEulerMass_lower_threshold
    {k : ℕ} (a b : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (u : ℝ) (hu : 0 < u) (j : Fin k) (hbu : b j ≤ u)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        (u / b j) * (∏ i, Real.log (b i / a i)) - eta ≤
          actualPrimeBoxEulerMass N cap a b u j := by
  have hbj : 0 < b j := (ha j).trans (hab j)
  have hratio := tendsto_finiteSieveDensity_power_ratio hbj hu
  have hmass := (tendsto_actualPrimeBoxMass a b ha hab).mono_left
    (inf_le_left :
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N} ≤ atTop)
  have hlim := hratio.mul hmass
  have hnear : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (u / b j) * (∏ i, Real.log (b i / a i)) - eta <
        (finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ b j)) /
          finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ u))) *
          actualPrimeBoxMass N a b :=
    (tendsto_order.mp hlim).1 _ (by linarith)
  rw [Filter.eventually_inf_principal] at hnear
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hnear
  refine ⟨max N1 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap hcap
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbcap : (N : ℝ) ^ b j ≤ (cap : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hNreal hbu).trans hcap
  have hbound := actualPrimeBoxEulerMass_ge_endpoint_ratio N cap (by omega)
    hEven a b u j hbu hcap
  rw [actualSmallEulerProduct_eq_finiteSieveDensity N cap ((N : ℝ) ^ b j) hbcap,
    actualSmallEulerProduct_eq_finiteSieveDensity N cap ((N : ℝ) ^ u) hcap] at hbound
  exact (hN1 N ((le_max_left _ _).trans hN) ⟨hNpos, hEven⟩).le.trans hbound

end

end ImbalancedChen
