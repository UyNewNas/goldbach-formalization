import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.RoughPowerParameters
import ImbalancedChen.SmallRosserErrorLimit

/-!
# Uniform absorption of the actual small/rough density error

The small parameter is chosen before the large threshold, even target,
finite prime cap and retained rough policy. The actual physical coefficient
is the same one whose integer majorant and finite density identity were
proved earlier. Its small-weight attachment error is at most any prescribed
multiple of the literal small-prime Euler product.

The proof discharges the absolute rough-mass bound and scalar limit; neither
is a hypothesis of the final theorem. This is an Euler-product-relative
reserve, not the sharp signed rough density or the manuscript's final K.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- First choose epsilon, then one large threshold, uniformly in the even
target, prime-enumeration cap and fixed rough retention policy. The error is
for the very same physical rho and its actual signed rough main density. -/
theorem exists_actualSmallRoughRho_density_error_le_euler_reserve
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon ^ 2 ≤ r ∧
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ N cap : ℕ, Even N → ∀ retainOdd : List ℕ → Bool,
          let w := D ^ (epsilon ^ 2)
          let z := D ^ r
          let L := D ^ epsilon
          let V := actualSmallEulerProduct N cap w
          let S := fixedRoughSupport retainOdd N cap w z
          let c := fixedRoughCoefficient retainOdd N cap w z
          let density := physicalDensitySum
            (actualSmallRoughModuli retainOdd N cap w z)
            (actualSmallRoughRho retainOdd N cap w z L)
          0 ≤ density - V * reciprocalTotientDensity S c ∧
            density - V * reciprocalTotientDensity S c ≤ eta * V := by
  obtain ⟨C, K, hC, _hK, hsupply⟩ := exists_actualSmallRoughRho_density_error
  obtain ⟨Krough, _hKrough, hrough⟩ :=
    exists_fixedRoughAbsoluteDensity_le_powerParameters
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonr, hfloor⟩ :=
    exists_smallRosser_epsilon_absorbing C r eta hr heta
  have hlimit := tendsto_actualSmallRosserDensityError_mul_roughMassEnvelope
    C K Krough r epsilon hepsilon
  have hsmall : ∀ᶠ D : ℝ in atTop,
      actualSmallRosserDensityError C K D epsilon * (r / epsilon ^ 2) *
        (1 + Krough / (epsilon ^ 2 * Real.log D)) < eta :=
    (tendsto_order.1 hlimit).2 eta hfloor
  obtain ⟨Dsmall, hDsmall⟩ := eventually_atTop.mp hsmall
  obtain ⟨Dsieve, hDsieve, hsieve⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonr,
    max Dsieve Dsmall, hDsieve.trans (le_max_left _ _), ?_⟩
  intro D hD N cap hN retainOdd
  have hDs : Dsieve ≤ D := (le_max_left _ _).trans hD
  have hDt : Dsmall ≤ D := (le_max_right _ _).trans hD
  have hD1 : 1 < D := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hV := actualSmallEulerProduct_pos N cap (D ^ (epsilon ^ 2)) hN
  have hE : 0 ≤ actualSmallRosserDensityError C K D epsilon := by
    unfold actualSmallRosserDensityError
    positivity
  have herror := hsieve D hDs N cap hN retainOdd (D ^ r)
  have hmass := hrough retainOdd N cap hN D epsilon r hD1 hepsilon hepsilonr
  have hscalar := hDsmall D hDt
  dsimp only at herror ⊢
  refine ⟨herror.1, herror.2.trans ?_⟩
  calc
    (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        actualSmallRosserDensityError C K D epsilon) *
        reciprocalTotientDensity
          (fixedRoughSupport retainOdd N cap (D ^ (epsilon ^ 2)) (D ^ r))
          (fun d => |fixedRoughCoefficient retainOdd N cap
            (D ^ (epsilon ^ 2)) (D ^ r) d|) ≤
      (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        actualSmallRosserDensityError C K D epsilon) *
          ((r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D))) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hV.le hE)
    _ = actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        (actualSmallRosserDensityError C K D epsilon * (r / epsilon ^ 2) *
          (1 + Krough / (epsilon ^ 2 * Real.log D))) := by ring
    _ ≤ actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) * eta :=
      mul_le_mul_of_nonneg_left hscalar.le hV.le
    _ = eta * actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) := mul_comm _ _

end

end ImbalancedChen
