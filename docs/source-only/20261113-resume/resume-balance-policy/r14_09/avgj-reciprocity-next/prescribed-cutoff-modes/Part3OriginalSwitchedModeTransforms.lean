import ImbalancedChen.Part3OriginalSwitchedCutoffModes
import ImbalancedChen.Part3ActualPositiveHolomorphicDiagonal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Batteries.Tactic.OpenPrivate

/-! Exchange the literal period test series under the individual
positive spectral transforms, including the removable weight at zero. -/
namespace ImbalancedChen.Part3.OriginalSwitchedModeTransforms20261113
noncomputable section
open Set MeasureTheory Complex
open OriginalSwitchedCutoffFamily20261113 OriginalSwitchedCutoffModes20261113
open ActualPositiveJRotationPair20261112 ActualPrescribedPositiveJ20261112
open ActualPositiveHolomorphicWeights20261112 ActualPositiveHolomorphicDiagonal20261112
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode e norm_e)
open private raw_integrable from ImbalancedChen.Part3ActualPositiveHolomorphicDiagonal

private abbrev μ : Measure ℝ := volume.restrict (Ioi 0)

private theorem identical_norm (n : ℤ) (Y x : ℝ) :
    ‖spectralTest (mode n) Y x‖=‖spectralTest (mode 0) Y x‖ := by
  simp only [spectralTest,spectralMode,norm_mul,norm_e,mul_one]

private theorem kernel_modes (K : ℝ→ℂ) (s : Bool) (L Y : ℝ) (yp : 0<Y)
    (int : ∀ n : ℤ,Integrable (fun x => K x*spectralTest (mode n) Y⁻¹ x) μ) :
    HasSum (fun n : ℤ => coefficient s L n*∫ x,K x*spectralTest (mode n) Y⁻¹ x ∂μ)
      (∫ x,K x*profile s L (Y*x) ∂μ) := by
  let f (n : ℤ) (x : ℝ) := K x*spectralTest (mode n) Y⁻¹ x
  let c := coefficient s L
  obtain ⟨_,_,h⟩ := mode_budget 0
  have S : Summable (fun n : ℤ => ‖c n‖) := by simpa [c] using (h s L).1
  have E := hasSum_integral_of_dominated_convergence (μ:=μ)
    (F:=fun n x => c n*f n x) (f:=fun x => K x*profile s L (Y*x))
    (fun n x => ‖c n‖*‖f 0 x‖)
    (fun n => ((int n).const_mul (c n)).aestronglyMeasurable)
    (fun n => ae_of_all _ fun x => by
      simp only [norm_mul,f,identical_norm n Y⁻¹ x,le_rfl])
    (ae_of_all _ fun x => S.mul_right _)
    (by simpa only [tsum_mul_right] using (int 0).norm.const_mul (∑' n : ℤ,‖c n‖))
    (ae_of_all _ fun x => ((prescribed_modes s L Y x yp).mul_left (K x)).congr_fun (fun n => by
      dsimp only [c,f];ring))
  simpa only [integral_const_mul,c,f] using E

/-- Exact complex values, for every real t (including zero), every
complementary a in [0,1/2), and every integer-order holomorphic moment.
No summability over the native spectral indices is assumed here. -/
theorem tested_transforms (s : Bool) (L Y : ℝ) (yp : 0<Y) :
    let Φ := fun x => profile s L (Y*x)
    (∀ t : ℝ,HasSum (fun n : ℤ => coefficient s L n*positiveWeight (spectralTest (mode n) Y⁻¹) t)
      (positiveWeight Φ t)) ∧
    (∀ a : ℝ,0≤a → a<1/2 → HasSum (fun n : ℤ =>
      coefficient s L n*exceptionalWeight (spectralTest (mode n) Y⁻¹) a) (exceptionalWeight Φ a)) ∧
    (∀ j : ℕ,HasSum (fun n : ℤ => coefficient s L n*holWeight j (spectralTest (mode n) Y⁻¹))
      (holWeight j Φ)) ∧
    (∀ j : ℕ,HasSum (fun n : ℤ => coefficient s L n*diagonalMoment j (spectralTest (mode n) Y⁻¹))
      (diagonalMoment j Φ)) := by
  dsimp only
  have factor (a b d : ℂ) : a/d*b=a*b/d := by ring
  refine ⟨fun t => ?_,fun a lo hi => ?_,fun j => ?_,fun j => ?_⟩
  · have T := kernel_modes (fun x => regularKernel x t/(x:ℂ)) s L Y yp (fun n => by
      simpa only [factor] using (regular_transform (mode n) (inv_pos.mpr yp) t).1)
    simpa only [factor,positiveWeight] using T
  · have T := kernel_modes (fun x => complementaryKernel x a/(x:ℂ)) s L Y yp (fun n => by
      simpa only [factor] using (exceptional_transform (mode n) (inv_pos.mpr yp) lo hi).1)
    simpa only [factor,exceptionalWeight] using T
  · have T := kernel_modes (fun x => intJ (2*j+1) x/(x:ℂ)) s L Y yp (fun n => by
      simpa only [factor] using moment_L1 (2*j+1) (mode n) (inv_pos.mpr yp))
    simp only [factor] at T
    have U : HasSum (fun n : ℤ => coefficient s L n*moment (2*j+1) (spectralTest (mode n) Y⁻¹))
        (moment (2*j+1) (fun x => profile s L (Y*x))) := T
    exact (U.mul_left (4*I^(2*(j+1)))).congr_fun (fun n => by unfold holWeight;ring)
  · exact kernel_modes (intJ j) s L Y yp (fun n => raw_integrable j (mode n) (inv_pos.mpr yp))

end
end ImbalancedChen.Part3.OriginalSwitchedModeTransforms20261113
