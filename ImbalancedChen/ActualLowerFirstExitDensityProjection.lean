import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.ActualLowerNormalizedRhoError

/-!
# The same lower physical coefficient and its full-policy density reserve

The even-first-exit projection bounds the full raw density from above by
the presieved rough density. The actual lower attachment loses at most an
arbitrarily prescribed singular-series reserve. Combining those proved
inequalities gives a lower bound for the same physical coefficient used
in the pointwise minorant, without assuming its divisor sum is nonnegative.

The unrestricted full policy density is not evaluated here. Causal box
compilation, sharp constants, support exponents and distribution remain open.
-/

namespace ImbalancedChen

noncomputable section

theorem fixedEvenRoughDensity_presieveProjection
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap 0 z)
        (fixedEvenRoughCoefficient retainEven N cap 0 z) ≤
      actualSmallEulerProduct N cap w *
        reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap w z)
          (fixedEvenRoughCoefficient retainEven N cap w z) := by
  have h := actualFirstExitPresieveProjection_lower (evenFirstExitPolicy retainEven)
    N cap w z hwz [] true 1 (evenFirstExitPolicy_odd retainEven) zero_le_one
  change evenFirstExitRetainedPolynomial retainEven _ _ ≤
    evenFirstExitRetainedPolynomial retainEven _ _ * _ at h
  rw [evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity,
    evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity] at h
  simpa only [mul_comm] using h

theorem exists_actualLowerSmallRoughRho_density_ge_full_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ retainEven : List ℕ → Bool,
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap 0 z)
                (fixedEvenRoughCoefficient retainEven N cap 0 z) -
                  eta * singularSeries N / Real.log (N : ℝ) ≤
              physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
                (actualLowerSmallRoughRho retainEven N cap w z L) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ :=
    exists_actualLowerSmallRoughRho_density_error_le_target_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap retainEven
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwz : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (N : ℝ) ^ (nu * r) :=
    Real.rpow_le_rpow_of_exponent_le hN1
      (mul_le_mul_of_nonneg_left hepsilonr hnu.le)
  have herror := (hbound N hN hEven cap hcap retainEven).2
  have hprojection := fixedEvenRoughDensity_presieveProjection retainEven N cap
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) hwz
  dsimp only at herror ⊢
  linarith

/-- One fixed precision and threshold give both the pointwise lower
inequality and the full-density reserve for the exact same physical rho.
Its unit coefficient bound is included, with no assertion of positivity. -/
theorem exists_actualLowerSmallRoughRho_full_density_minorant
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ retainEven : List ℕ → Bool,
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            let S := actualLowerSmallRoughModuli retainEven N cap w z
            let rho := actualLowerSmallRoughRho retainEven N cap w z L
            (∀ n : ℤ, physicalDivisorSum S rho n.natAbs ≤ actualSmallRoughIndicator N z n) ∧
              (∀ q : ℕ, |rho q| ≤ 1) ∧
              reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap 0 z)
                  (fixedEvenRoughCoefficient retainEven N cap 0 z) -
                    eta * singularSeries N / Real.log (N : ℝ) ≤
                physicalDensitySum S rho := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ :=
    exists_actualLowerSmallRoughRho_density_ge_full_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap retainEven
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : (1 : ℝ) < (N : ℝ) ^ (nu * epsilon) :=
    Real.one_lt_rpow hN1 (mul_pos hnu hepsilon)
  have hepssq : epsilon ^ 2 ≤ epsilon := by nlinarith
  have hwL : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (N : ℝ) ^ (nu * epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le
      (mul_le_mul_of_nonneg_left hepssq hnu.le)
  have hwz : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (N : ℝ) ^ (nu * r) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le
      (mul_le_mul_of_nonneg_left hepsilonr hnu.le)
  refine ⟨?_, ?_, hbound N hN hEven cap hcap retainEven⟩
  · intro n
    exact actualLowerSmallRoughRho_minorant retainEven N cap _ _ _ hL hwL hwz hcap n
  · intro q
    exact actualLowerSmallRoughRho_abs_le_one retainEven N cap _ _ _ q

end

end ImbalancedChen
