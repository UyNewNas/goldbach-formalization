import ImbalancedChen.ActualNormalizedRhoError
import ImbalancedChen.ActualCompilerDensityReserve

/-!
# P4A: a concrete normalized attachment/compiler error supplier

This combines the actual attachment supplier and actual compiler slope
supplier at one epsilon and one target threshold. It does not assume or
conclude a sharp K bound. The baseline is the signed rough density times
the actual small Euler product, not a different policy's integral.

The normalized compiler loss is literally B/(nu*epsilon^2) times the
reciprocal-totient absolute coefficient difference on the same rough carrier.
No cancellation of that difference is used. Equal coefficients on the
carrier have exactly zero compiler error, without an asymptotic argument.

SOURCE ONLY: no Lean invocation was made for this candidate.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- Move an absolute error onto the manuscript density normalization. -/
theorem p4a_abs_normalized_density_sub_le {N : ℕ} (hN : 2 ≤ N)
    {x y M : ℝ}
    (h : |x - y| ≤ M * (singularSeries N / Real.log (N : ℝ))) :
    |x * Real.log (N : ℝ) / singularSeries N -
      y * Real.log (N : ℝ) / singularSeries N| ≤ M := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  calc
    |x * Real.log (N : ℝ) / singularSeries N -
        y * Real.log (N : ℝ) / singularSeries N| =
      |x - y| * Real.log (N : ℝ) / singularSeries N := by
        rw [← sub_div, ← sub_mul, abs_div, abs_mul,
          abs_of_pos hlog, abs_of_pos (singularSeries_pos N)]
    _ ≤ M := (density_le_manuscriptScale_iff_normalized hN |x - y| M).mp h

/-- Compiler error is zero when the actual coefficients agree on the
carrier. Equality outside that carrier is unnecessary. -/
theorem p4a_compiler_absolute_mass_eq_zero
    (rough : Finset ℕ) (compiled raw : ℕ → ℝ)
    (hcoeff : ∀ d ∈ rough, compiled d = raw d) :
    reciprocalTotientDensity rough (fun d => |compiled d - raw d|) = 0 := by
  unfold reciprocalTotientDensity
  apply Finset.sum_eq_zero
  intro d hd
  rw [hcoeff d hd]
  simp

/-- Exact density equality follows from the same coefficient on the common
carrier, with the same small weights. No compiler reserve is consumed. -/
theorem p4a_physicalDensity_eq_of_coefficients_eq_on
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ)
    (hcoeff : ∀ d ∈ rough, compiled d = raw d) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) =
      physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus) := by
  rw [physicalDensitySum_smallRoughRho_eq_signSensitive hsmall hrough,
    physicalDensitySum_smallRoughRho_eq_signSensitive hsmall hrough]
  unfold signSensitiveReciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro d hd
  rw [hcoeff d hd]

/-- The compiler error of the normalized main term uses the same source
mass and the very same two displayed physical coefficients. This is an
exact identity, valid also at Lean's exceptional total-division arguments. -/
theorem p4a_same_source_normalized_mainTerm_error
    (N : ℕ) (mass : ℝ) (Q : Finset ℕ) (compiled raw : ℕ → ℝ) :
    |mass * physicalDensitySum Q compiled / singularNormalization N -
      mass * physicalDensitySum Q raw / singularNormalization N| =
      |mass * Real.log (N : ℝ) / (N : ℝ)| *
        |physicalDensitySum Q compiled * Real.log (N : ℝ) / singularSeries N -
          physicalDensitySum Q raw * Real.log (N : ℝ) / singularSeries N| := by
  rw [same_rho_normalized_mainTerm, same_rho_normalized_mainTerm,
    ← mul_sub, abs_mul]

/-- Equality on the carrier gives zero normalized compiler error. -/
theorem p4a_normalized_compiler_error_eq_zero
    (N : ℕ) {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ)
    (hcoeff : ∀ d ∈ rough, compiled d = raw d) :
    |physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) *
          Real.log (N : ℝ) / singularSeries N -
      physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus) *
          Real.log (N : ℝ) / singularSeries N| = 0 := by
  rw [p4a_physicalDensity_eq_of_coefficients_eq_on hsmall hrough
    compiled raw betaMinus betaPlus hcoeff]
  simp

/-- With exactly the same retention policy, the literal compiler budget
vanishes. The attachment reserve remains a separate error. -/
theorem p4a_same_policy_compiler_term_eq_zero
    (B nu epsilon : ℝ) (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) :
    (B / (nu * epsilon ^ 2)) *
      reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
        (fun d => |fixedRoughCoefficient retainOdd N cap w z d -
          fixedRoughCoefficient retainOdd N cap w z d|) = 0 := by
  rw [p4a_compiler_absolute_mass_eq_zero _ _ _ (fun _ _ => rfl)]
  simp

/-- Actual suppliers give a common admissible precision and common
threshold for the normalized absolute error of any compiled coefficient
on the fixed policy's actual rough carrier. The constant B is selected
before nu, sieveR, eta and epsilonMax; epsilon is selected before targets,
caps, retention policies and compiled coefficients.

The literal 1/nu is retained. It comes from log(N^nu)=nu*log N.
The signed rough baseline is not assumed to satisfy any K estimate. -/
theorem p4a_exists_actualCompiledRho_normalized_attachment_error :
    ∃ B : ℝ, 0 < B ∧
      ∀ nu sieveR eta epsilonMax : ℝ,
        0 < nu → 0 < sieveR → 0 < eta → 0 < epsilonMax →
        ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
          epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
          ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
            ∀ cap : ℕ, (N : ℝ) ^ (nu * sieveR) ≤ (cap : ℝ) →
              ∀ (retainOdd : List ℕ → Bool) (compiled : ℕ → ℝ),
                let w := (N : ℝ) ^ (nu * epsilon ^ 2)
                let z := (N : ℝ) ^ (nu * sieveR)
                let L := (N : ℝ) ^ (nu * epsilon)
                let small := actualSmallRosserSupport N cap w
                let rough := fixedRoughSupport retainOdd N cap w z
                let raw := fixedRoughCoefficient retainOdd N cap w z
                let density := physicalDensitySum (smallRoughModuli small rough)
                  (smallRoughRho small rough compiled
                    (actualSmallRosserMinus N cap w L)
                    (actualSmallRosserPlus N cap w L))
                let baseline := actualSmallEulerProduct N cap w *
                  reciprocalTotientDensity rough raw
                |density * Real.log (N : ℝ) / singularSeries N -
                    baseline * Real.log (N : ℝ) / singularSeries N| ≤
                  eta + (B / (nu * epsilon ^ 2)) *
                    reciprocalTotientDensity rough (fun d => |compiled d - raw d|) := by
  obtain ⟨B, hB, hCompiler⟩ :=
    exists_actualCompiledRho_target_density_difference_bound
  refine ⟨B, hB, ?_⟩
  intro nu sieveR eta epsilonMax hnu hr heta hepsilonMax
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonR,
      Nattach, hNattach, hAttach⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve
      nu sieveR eta epsilonMax hnu hr heta hepsilonMax
  obtain ⟨Ncompiler, _hNcompiler, hCompiler⟩ :=
    hCompiler nu hnu epsilon hepsilon hepsilon8
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonR,
    max Nattach Ncompiler, hNattach.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap retainOdd compiled
  have hNa : Nattach ≤ N := (le_max_left _ _).trans hN
  have hNc : Ncompiler ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNattach.trans hNa
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hwcap : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN1
      (mul_le_mul_of_nonneg_left hepsilonR hnu.le)).trans hcap
  have hA := hAttach N hNa hEven cap hcap retainOdd
  have hC := hCompiler N hNc hEven cap hwcap
    (fixedRoughSupport retainOdd N cap
      ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * sieveR)))
    (fun d hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap _ _ hd)
    compiled (fixedRoughCoefficient retainOdd N cap
      ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * sieveR)))
  dsimp only at hA hC ⊢
  have hAabs := hA.2
  rw [← abs_of_nonneg hA.1] at hAabs
  have hAnorm := p4a_abs_normalized_density_sub_le hN2
    (show |physicalDensitySum
        (actualSmallRoughModuli retainOdd N cap
          ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * sieveR)))
        (actualSmallRoughRho retainOdd N cap
          ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * sieveR))
          ((N : ℝ) ^ (nu * epsilon))) -
        actualSmallEulerProduct N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) *
          reciprocalTotientDensity
            (fixedRoughSupport retainOdd N cap
              ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * sieveR)))
            (fixedRoughCoefficient retainOdd N cap
              ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * sieveR)))| ≤
        eta * (singularSeries N / Real.log (N : ℝ)) by
      convert hAabs using 1 <;> ring)
  have hCnorm := p4a_abs_normalized_density_sub_le hN2 hC
  have htri : ∀ a b c M eta : ℝ,
      |a - b| ≤ M → |b - c| ≤ eta → |a - c| ≤ eta + M := by
    intro a b c M eta h₁ h₂
    calc
      |a - c| = |(a - b) + (b - c)| := by congr 1; ring
      _ ≤ |a - b| + |b - c| := abs_add _ _
      _ ≤ M + eta := add_le_add h₁ h₂
      _ = eta + M := add_comm _ _
  exact htri _ _ _ _ _ hCnorm hAnorm

end
end ImbalancedChen
