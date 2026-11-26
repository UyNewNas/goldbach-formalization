import ImbalancedChen.ActualSmallRosserDensity
import ImbalancedChen.RoughAbsoluteDensity

/-!
# Power-scale parameters for the actual small/rough density error

The Euler product belongs to the actual target-prime-deleted small carrier.
Its positivity follows from exclusion of the prime two for even targets.
The rough mass bound is specialized to the literal cutoffs
`w = D ^ (epsilon ^ 2)` and `z = D ^ r`, with the logarithmic denominator
retained exactly. No density or absolute-mass bound is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Every factor of the actual small Euler product is strictly positive
for an even target; the empty carrier has product one. -/
theorem actualSmallEulerProduct_pos (N cap : ℕ) (w : ℝ) (hN : Even N) :
    0 < actualSmallEulerProduct N cap w := by
  unfold actualSmallEulerProduct
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) < p := by
    exact_mod_cast (actualSmallPrimeFinset_odd_of_even hN hp).2
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

theorem actualSmallEulerProduct_nonneg (N cap : ℕ) (w : ℝ) (hN : Even N) :
    0 ≤ actualSmallEulerProduct N cap w :=
  (actualSmallEulerProduct_pos N cap w hN).le

/-- These hypotheses place the literal power cutoffs in the range of the
uniform rough-prime mass theorem, including equality of the cutoffs. -/
theorem roughPower_cutoffs {D epsilon r : ℝ}
    (hD : 1 < D) (hepsilon : 0 < epsilon) (hepsilonr : epsilon ^ 2 ≤ r) :
    1 < D ^ (epsilon ^ 2) ∧ D ^ (epsilon ^ 2) ≤ D ^ r :=
  ⟨Real.one_lt_rpow hD (sq_pos_of_pos hepsilon),
    Real.rpow_le_rpow_of_exponent_le hD.le hepsilonr⟩

/-- Exact cancellation of the common logarithmic scale. Both nonzero
conditions are explicit; the numerator exponent may be any real number. -/
theorem roughPower_log_ratio {D epsilon r : ℝ}
    (hD : 0 < D) (hlogD : Real.log D ≠ 0) (hepsilon : epsilon ≠ 0) :
    Real.log (D ^ r) / Real.log (D ^ (epsilon ^ 2)) = r / epsilon ^ 2 := by
  rw [Real.log_rpow hD, Real.log_rpow hD]
  field_simp [hlogD, hepsilon]

/-- The actual absolute rough mass on power-scale cutoffs, with one
constant independent of D, epsilon, r, target, cap, and retention policy.
The estimate also applies to truncated enumeration caps. -/
theorem exists_fixedRoughAbsoluteDensity_le_powerParameters :
    ∃ Krough : ℝ, 1 < Krough ∧
      ∀ (retainOdd : List ℕ → Bool) (N cap : ℕ), Even N →
        ∀ D epsilon r : ℝ, 1 < D → 0 < epsilon → epsilon ^ 2 ≤ r →
          reciprocalTotientDensity
              (fixedRoughSupport retainOdd N cap (D ^ (epsilon ^ 2)) (D ^ r))
              (fun d => |fixedRoughCoefficient retainOdd N cap
                (D ^ (epsilon ^ 2)) (D ^ r) d|) ≤
            (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)) := by
  obtain ⟨Krough, hKrough, hbound⟩ := exists_fixedRoughAbsoluteDensity_le_logRatio
  refine ⟨Krough, hKrough, ?_⟩
  intro retainOdd N cap hN D epsilon r hD hepsilon hepsilonr
  have hcut := roughPower_cutoffs hD hepsilon hepsilonr
  have h := hbound retainOdd N cap hN (D ^ (epsilon ^ 2)) (D ^ r) hcut.1 hcut.2
  have hDpos : 0 < D := lt_trans zero_lt_one hD
  rw [roughPower_log_ratio hDpos (ne_of_gt (Real.log_pos hD)) (ne_of_gt hepsilon),
    Real.log_rpow hDpos] at h
  exact h

end

end ImbalancedChen
