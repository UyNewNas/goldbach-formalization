import ImbalancedChen.ActualPrimePresieveSplit
import ImbalancedChen.FirstExitPresieveProjection
import ImbalancedChen.ActualNormalizedRhoError

/-!
# Presieve projection for the same actual first-exit density

The finite projection keeps the complete retention predicate on the actual
decreasing prime carrier. It is an upper inequality for odd first exits
and a lower inequality for even first exits. The upper fixed-coefficient
density is identified exactly with the tree polynomial.

The already constructed physical upper coefficient has density at most
the full retained density plus any prescribed normalized attachment reserve.
This does not yet evaluate the full density of the manuscript's causal policy,
prove its support exponent, or supply its signed distribution estimate.
-/

namespace ImbalancedChen

noncomputable section

/-- Actual upper projection with arbitrary incoming history and sign. -/
theorem actualFirstExitPresieveProjection_upper
    (retained : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hwz : w ≤ z) (selectedPrefix : List ℕ) (positive : Bool) (mass : ℝ)
    (heven : ∀ pre, retained true pre = true) (hmass : 0 ≤ mass) :
    firstExitRetainedPolynomial retained (fun p => 1 / ((p : ℝ) - 1))
        selectedPrefix positive mass (roughPrimeUniverse N cap w z) *
        actualSmallEulerProduct N cap w ≤
      firstExitRetainedPolynomial retained (fun p => 1 / ((p : ℝ) - 1))
        selectedPrefix positive mass (roughPrimeUniverse N cap 0 z) := by
  have h := firstExitPresieveProjection_upper_of_even_retained retained
    (fun p => 1 / ((p : ℝ) - 1)) selectedPrefix
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse N cap 0 w)
    positive mass heven hmass
    (fun _ hp => (reciprocalTotientPrimeWeight_mem_Icc
      (mem_roughPrimeUniverse_prime hp)).1)
    (fun _ hp => reciprocalTotientPrimeWeight_mem_Icc
      (mem_roughPrimeUniverse_prime hp))
  rw [roughPrimeUniverse_small_eulerProduct,
    ← roughPrimeUniverse_split N cap w z hwz] at h
  exact h

/-- Actual lower projection; no nonnegativity of the signed polynomial is used. -/
theorem actualFirstExitPresieveProjection_lower
    (retained : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hwz : w ≤ z) (selectedPrefix : List ℕ) (positive : Bool) (mass : ℝ)
    (hodd : ∀ pre, retained false pre = true) (hmass : 0 ≤ mass) :
    firstExitRetainedPolynomial retained (fun p => 1 / ((p : ℝ) - 1))
        selectedPrefix positive mass (roughPrimeUniverse N cap 0 z) ≤
      firstExitRetainedPolynomial retained (fun p => 1 / ((p : ℝ) - 1))
        selectedPrefix positive mass (roughPrimeUniverse N cap w z) *
        actualSmallEulerProduct N cap w := by
  have h := firstExitPresieveProjection_lower_of_odd_retained retained
    (fun p => 1 / ((p : ℝ) - 1)) selectedPrefix
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse N cap 0 w)
    positive mass hodd hmass
    (fun _ hp => (reciprocalTotientPrimeWeight_mem_Icc
      (mem_roughPrimeUniverse_prime hp)).1)
    (fun _ hp => reciprocalTotientPrimeWeight_mem_Icc
      (mem_roughPrimeUniverse_prime hp))
  rw [roughPrimeUniverse_small_eulerProduct,
    ← roughPrimeUniverse_split N cap w z hwz] at h
  exact h

/-- The upper projection on the literal fixed modulus densities. -/
theorem fixedRoughDensity_presieveProjection
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    actualSmallEulerProduct N cap w *
        reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
          (fixedRoughCoefficient retainOdd N cap w z) ≤
      reciprocalTotientDensity (fixedRoughSupport retainOdd N cap 0 z)
        (fixedRoughCoefficient retainOdd N cap 0 z) := by
  have h := actualFirstExitPresieveProjection_upper (oddFirstExitPolicy retainOdd)
    N cap w z hwz [] true 1 (oddFirstExitPolicy_even retainOdd) zero_le_one
  change oddFirstExitRetainedPolynomial retainOdd _ _ * _ ≤
    oddFirstExitRetainedPolynomial retainOdd _ _ at h
  rw [oddFirstExitRetainedPolynomial_eq_fixedRoughDensity,
    oddFirstExitRetainedPolynomial_eq_fixedRoughDensity] at h
  simpa only [mul_comm] using h

/-- One choice of precision and threshold controls the physical density
for every later target, covering cap and retention policy. The comparison
uses that exact policy's full raw density, with only the proved attachment
reserve added. No value of the full policy density is assumed or inferred. -/
theorem exists_actualSmallRoughRho_density_le_full_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ retainOdd : List ℕ → Bool,
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
                (actualSmallRoughRho retainOdd N cap w z L) ≤
              reciprocalTotientDensity (fixedRoughSupport retainOdd N cap 0 z)
                (fixedRoughCoefficient retainOdd N cap 0 z) +
                  eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap retainOdd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwz : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (N : ℝ) ^ (nu * r) :=
    Real.rpow_le_rpow_of_exponent_le hN1
      (mul_le_mul_of_nonneg_left hepsilonr hnu.le)
  have herror := (hbound N hN hEven cap hcap retainOdd).2
  have hprojection := fixedRoughDensity_presieveProjection retainOdd N cap
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) hwz
  dsimp only at herror ⊢
  linarith

end

end ImbalancedChen
