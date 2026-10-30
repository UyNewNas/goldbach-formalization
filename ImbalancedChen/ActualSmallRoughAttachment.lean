import ImbalancedChen.ActualSmallRoughFiniteAttachment
import ImbalancedChen.FiniteUpperCarrierCore
import ImbalancedChen.ActualSmallRosser
import ImbalancedChen.FixedRoughCoefficients
import ImbalancedChen.SmallRoughMainTerm
import ImbalancedChen.ActualSmallRosserDensity
import ImbalancedChen.SmallRoughDensityError

/-!
# The actual small weights attached to fixed rough coefficients

The resulting physical coefficient is fixed before the integer argument is
evaluated. Its pointwise majorant and one-bound use proved properties of
the literal Rosser weights and odd-first-exit tree; neither property is an
input hypothesis. The retention policy remains a parameter: the current
manuscript's causal caps, density constant, and distribution theorem are
separate obligations.
-/

namespace ImbalancedChen

noncomputable section

/-- The density of this very same coefficient factors into the actual two
small-weight densities. This is an identity, not yet the sharp K bound. -/
theorem actualSmallRoughRho_density_eq
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) =
      signSensitiveReciprocalTotientDensity
        (fixedRoughSupport retainOdd N cap w z)
        (fixedRoughCoefficient retainOdd N cap w z)
        (reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserMinus N cap w L))
        (reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserPlus N cap w L)) :=
  physicalDensitySum_smallRoughRho_eq_signSensitive
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hd)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

/-- The genuine small-weight density supplier controls the density error
of the actual physical coefficient, uniformly in the even target and
retention policy. The absolute rough mass remains visible: this does not
claim the sharp complete density constant of the current manuscript. -/
theorem exists_actualSmallRoughRho_density_error :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
          ∀ N cap : ℕ, Even N → ∀ (retainOdd : List ℕ → Bool) (z : ℝ),
            let w := D ^ (epsilon ^ 2)
            let L := D ^ epsilon
            let V := actualSmallEulerProduct N cap w
            let E := actualSmallRosserDensityError C K D epsilon
            let S := fixedRoughSupport retainOdd N cap w z
            let c := fixedRoughCoefficient retainOdd N cap w z
            let density := physicalDensitySum
              (actualSmallRoughModuli retainOdd N cap w z)
              (actualSmallRoughRho retainOdd N cap w z L)
            0 ≤ density - V * reciprocalTotientDensity S c ∧
              density - V * reciprocalTotientDensity S c ≤
                (V * E) * reciprocalTotientDensity S (fun d => |c d|) := by
  obtain ⟨C, K, hC, hK, hsupply⟩ := exists_actualSmallRosser_density_sandwich
  refine ⟨C, K, hC, hK, ?_⟩
  intro epsilon hepsilon hepsilon8
  obtain ⟨D₀, hD₀, hsupply⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD N cap hN retainOdd z
  have h := hsupply D hD N cap hN
  dsimp only at h ⊢
  apply physicalDensitySum_smallRoughRho_error
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap _ z hd)
    (fixedRoughCoefficient retainOdd N cap _ z)
    (actualSmallRosserMinus N cap _ _) (actualSmallRosserPlus N cap _ _)
  · simpa only [mul_sub, mul_one, actualSmallRosserMinusDensity] using h.1
  · exact h.2.1
  · exact h.2.2.1
  · simpa only [mul_add, mul_one, actualSmallRosserPlusDensity] using h.2.2.2.1

end

end ImbalancedChen
