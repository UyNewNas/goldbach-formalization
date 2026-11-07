import ImbalancedChen.P2LowerFiniteCellBetaCompiler
import ImbalancedChen.ActualLowerFirstExitDensityProjection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite-cell compiler's actual output now receives a RAW FULL-POLICY
density reserve. Both error terms are explicit functions of that output:
the exact signed rounding loss and the absolute rounded rough density.
The beta fundamental-lemma sandwich and the correctly oriented lower
presieve projection are supplied by existing actual theorems.

This is not a claim that the gate-strip rounding loss tends to zero, nor
a sharp evaluation of the original lower policy density. Those analytic
tasks and the signed distribution of this same rho remain OPEN.
-/

namespace ImbalancedChen.P2LowerFiniteCellRawDensityReserve

noncomputable section
open scoped Classical BigOperators
open P2LowerFiniteCellRounding P2LowerFiniteCellBetaCompiler

/-- One actual beta supplier threshold precedes every target, raw policy,
fine mesh and cutoff. No final density estimate is supplied as an input. -/
theorem exists_actual_compiled_raw_density_reserve :
    ∃C K : ℝ,0<C ∧ 1<K ∧ ∀epsilon : ℝ,0<epsilon → epsilon<1/8 →
      ∃D0 : ℝ,2≤D0 ∧ ∀D : ℝ,D0≤D → ∀N cap : ℕ,Even N →
        ∀(retainEven : List ℕ → Bool) (z tau : ℝ),D^(epsilon^2)≤z →
          let w := D^(epsilon^2)
          let L := D^epsilon
          let V := actualSmallEulerProduct N cap w
          let E := actualSmallRosserDensityError C K D epsilon
          reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap 0 z)
            (fixedEvenRoughCoefficient retainEven N cap 0 z)-
              V*roundingLoss retainEven N cap w z tau-
              (V*E)*reciprocalTotientDensity (universe N cap w z)
                (fun d=>|coefficient retainEven N cap w z tau d|)≤
            physicalDensitySum (support N cap w z) (rho retainEven N cap w z tau L) := by
  obtain ⟨C,K,hC,hK,hsupply⟩ := exists_actualSmallRosser_density_sandwich
  refine ⟨C,K,hC,hK,?_⟩
  intro epsilon he he8
  obtain ⟨D0,hD0,hsupply⟩ := hsupply epsilon he he8
  refine ⟨D0,hD0,?_⟩
  intro D hD N cap hEven retainEven z tau hwz
  have hs := hsupply D hD N cap hEven
  have hbeta :
      actualSmallEulerProduct N cap (D^(epsilon^2))*
        reciprocalTotientDensity (universe N cap (D^(epsilon^2)) z)
          (coefficient retainEven N cap (D^(epsilon^2)) z tau)-
        physicalDensitySum (support N cap (D^(epsilon^2)) z)
          (rho retainEven N cap (D^(epsilon^2)) z tau (D^epsilon))≤
      (actualSmallEulerProduct N cap (D^(epsilon^2))*
        actualSmallRosserDensityError C K D epsilon)*
          reciprocalTotientDensity (universe N cap (D^(epsilon^2)) z)
            (fun d=>|coefficient retainEven N cap (D^(epsilon^2)) z tau d|) := by
    apply (physicalDensitySum_smallRoughRho_lower_error
      (fun _ hd=>actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hd)
      (fun _ hd=>universe_rough N cap _ z hd)
      (coefficient retainEven N cap (D^(epsilon^2)) z tau)
      (actualSmallRosserMinus N cap (D^(epsilon^2)) (D^epsilon))
      (actualSmallRosserPlus N cap (D^(epsilon^2)) (D^epsilon)) ?_ ?_ ?_ ?_).2
    · simpa only [mul_sub,mul_one,actualSmallRosserMinusDensity] using hs.1
    · exact hs.2.1
    · exact hs.2.2.1
    · simpa only [mul_add,mul_one,actualSmallRosserPlusDensity] using hs.2.2.2.1
  have hround := roundingLoss_exact retainEven N cap (D^(epsilon^2)) z tau
  rw [raw_density_on_universe] at hround
  have hroundV := congrArg (fun x=>actualSmallEulerProduct N cap (D^(epsilon^2))*x) hround
  have hprojection := fixedEvenRoughDensity_presieveProjection retainEven N cap
    (D^(epsilon^2)) z hwz
  dsimp only at ⊢
  change reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap 0 z)
      (fixedEvenRoughCoefficient retainEven N cap 0 z)≤
    actualSmallEulerProduct N cap (D^(epsilon^2))*
      reciprocalTotientDensity (rawSupport retainEven N cap (D^(epsilon^2)) z)
        (raw retainEven N cap (D^(epsilon^2)) z) at hprojection
  nlinarith only [hprojection,hroundV,hbeta]

end
end ImbalancedChen.P2LowerFiniteCellRawDensityReserve
