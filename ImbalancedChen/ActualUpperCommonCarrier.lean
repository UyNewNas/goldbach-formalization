import ImbalancedChen.FiniteUpperCarrierCore
import ImbalancedChen.ActualCompilerDensityReserve
import ImbalancedChen.RealPhysicalUpperWeightBridge

/-!
# The raw upper coefficient on the compiler's common finite carrier

The raw retained-tree coefficient is zero outside its own finite support.
Enlarging that support to include a compiler carrier therefore leaves the
raw physical coefficient itself, and every signed weighted sum of it,
unchanged. This is an exact carrier identification, not a density or
distribution assumption. The final estimate applies the existing proved
small-weight reserve to the literal actual raw density on its original
carrier. A compiler still owes its actual coefficient-error bound.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The proved compiler reserve now compares the compiled density on a
common carrier with the literal raw density on its own retained support.
The coefficient-error mass is still charged on the whole common carrier,
including compiler-only moduli. No sharp error estimate is assumed or
asserted here, and the scale retains its exact factor `1 / nu`. -/
theorem exists_actualUpperCommonCarrier_target_density_difference_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ nu : ℝ, 0 < nu →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ cap : ℕ, (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
            ∀ (retainOdd : List ℕ → Bool) (z : ℝ) (rough : Finset ℕ),
              fixedRoughSupport retainOdd N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) z ⊆ rough →
              (∀ d ∈ rough, RoughPrimeSupportedAt ((N : ℝ) ^ (nu * epsilon ^ 2)) d) →
                ∀ compiled : ℕ → ℝ,
                  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
                  let L := (N : ℝ) ^ (nu * epsilon)
                  let raw := fixedRoughCoefficient retainOdd N cap w z
                  |physicalDensitySum (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
                      (smallRoughRho (actualSmallRosserSupport N cap w) rough compiled
                        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) -
                    physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
                      (actualSmallRoughRho retainOdd N cap w z L)| ≤
                    ((B / (nu * epsilon ^ 2)) *
                      reciprocalTotientDensity rough (fun d => |compiled d - raw d|)) *
                        (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actualCompiledRho_target_density_difference_bound
  refine ⟨B, hB, ?_⟩
  intro nu hnu epsilon hepsilon hepsilon8
  obtain ⟨N₀, hN₀, hsupply⟩ := hsupply nu hnu epsilon hepsilon hepsilon8
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap retainOdd z rough hcover hrough compiled
  have h := hsupply N hN hEven cap hcap rough hrough compiled
    (fixedRoughCoefficient retainOdd N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) z)
  dsimp only at h ⊢
  rw [actualSmallRoughRho_density_eq_on_common_carrier retainOdd N cap
    ((N : ℝ) ^ (nu * epsilon ^ 2)) z ((N : ℝ) ^ (nu * epsilon)) rough hcover] at h
  exact h

end

end ImbalancedChen
