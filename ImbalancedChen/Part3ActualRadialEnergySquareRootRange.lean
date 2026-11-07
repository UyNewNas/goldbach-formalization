import ImbalancedChen.Part3ActualRadialCyclicEnergyIdentity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The actual radial completed form is unitarily identified with physical
L2 by the polar factor of its original injective dense embedding J.
The construction extends J* along the dense range of the ACTUAL
positive square root sqrt(R1), using the proved equality of norms.
It proves range(J)=range(sqrt(R1)) and the exact shifted form norm.
No polar decomposition, form-domain equality or range identity is an
input. Turning this physical square-root range into scalar maximal
sqrt(lambda) multiplication is a separate remaining step.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open Set
open GenericHilbertAdjointSquare20261025a

def radialResolventSquareRoot : RadialL2 →L[ℂ] RadialL2 :=
  CFC.sqrt radialUnitShiftResolvent

theorem radialResolventSquareRoot_nonneg : 0 ≤ radialResolventSquareRoot :=
  CFC.sqrt_nonneg radialUnitShiftResolvent

theorem radialResolventSquareRoot_selfAdjoint : IsSelfAdjoint radialResolventSquareRoot :=
  radialResolventSquareRoot_nonneg.isSelfAdjoint

theorem radialResolventSquareRoot_square :
    radialResolventSquareRoot * radialResolventSquareRoot = radialUnitShiftResolvent :=
  CFC.sqrt_mul_sqrt_self radialUnitShiftResolvent radialUnitShiftResolvent_nonneg

theorem radialResolventSquareRoot_injective :
    Function.Injective radialResolventSquareRoot := by
  intro F G hFG
  apply radialUnitShiftResolvent_injective
  have h := congrArg radialResolventSquareRoot hFG
  simpa only [← ContinuousLinearMap.mul_apply, radialResolventSquareRoot_square] using h

theorem radialResolventSquareRoot_denseRange : DenseRange radialResolventSquareRoot := by
  change Dense (radialResolventSquareRoot.range : Set RadialL2)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply radialResolventSquareRoot.range.topologicalClosure_eq_top_iff.mpr
  rw [ContinuousLinearMap.orthogonal_range,
    radialResolventSquareRoot_selfAdjoint.adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr radialResolventSquareRoot_injective

theorem radialRieszLift_norm_eq_squareRoot (F : RadialL2) :
    ‖radialFormRieszSolution 1 F‖ = ‖radialResolventSquareRoot F‖ := by
  have hq := adjointSquare_quadratic (radialPhysicalEmbedding 1) F
  have hi := radialResolventSquareRoot_selfAdjoint.isSymmetric F
    (radialResolventSquareRoot F)
  rw [← ContinuousLinearMap.mul_apply, radialResolventSquareRoot_square] at hi
  have hn : ‖radialResolventSquareRoot F‖ ^ 2 =
      (inner ℂ F (radialUnitShiftResolvent F)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hi]
  change (inner ℂ F (radialUnitShiftResolvent F)).re =
    ‖radialFormRieszSolution 1 F‖ ^ 2 at hq
  nlinarith [norm_nonneg (radialFormRieszSolution 1 F),
    norm_nonneg (radialResolventSquareRoot F)]

private theorem radialRieszLift_squareRoot_bound :
    ∀ F : RadialL2, ‖radialFormRieszSolution 1 F‖ ≤
      1 * ‖radialResolventSquareRoot F‖ := by
  intro F
  rw [radialRieszLift_norm_eq_squareRoot, one_mul]

def radialEnergyPolarExtension : RadialL2 →L[ℂ] radialClosedEnergyDomain 1 :=
  (radialFormRieszSolution 1).toLinearMap.extendOfNorm
    radialResolventSquareRoot.toLinearMap

theorem radialEnergyPolarExtension_apply_squareRoot (F : RadialL2) :
    radialEnergyPolarExtension (radialResolventSquareRoot F) =
      radialFormRieszSolution 1 F :=
  LinearMap.extendOfNorm_eq radialResolventSquareRoot_denseRange
    ⟨1, radialRieszLift_squareRoot_bound⟩ F

theorem radialEnergyPolarExtension_norm (F : RadialL2) :
    ‖radialEnergyPolarExtension F‖ = ‖F‖ := by
  have heq : (fun G : RadialL2 => ‖radialEnergyPolarExtension G‖) =
      (fun G : RadialL2 => ‖G‖) := by
    apply (continuous_norm.comp radialEnergyPolarExtension.continuous).ext_on
      radialResolventSquareRoot_denseRange continuous_norm
    rintro _ ⟨G, rfl⟩
    rw [radialEnergyPolarExtension_apply_squareRoot, radialRieszLift_norm_eq_squareRoot]
  exact congrFun heq F

def radialEnergyPolarIsometry : RadialL2 →ₗᵢ[ℂ] radialClosedEnergyDomain 1 where
  toLinearMap := radialEnergyPolarExtension.toLinearMap
  norm_map' := radialEnergyPolarExtension_norm

theorem radialEnergyPolarIsometry_surjective :
    Function.Surjective radialEnergyPolarIsometry := by
  have hc : IsClosed (Set.range radialEnergyPolarIsometry) :=
    radialEnergyPolarIsometry.isometry.isClosedEmbedding.isClosed_range
  have hd : Dense (Set.range radialEnergyPolarIsometry) := by
    apply radialFormRieszSolution_one_denseRange.mono
    rintro e ⟨F, rfl⟩
    exact ⟨radialResolventSquareRoot F, radialEnergyPolarExtension_apply_squareRoot F⟩
  intro e
  have he : e ∈ Set.range radialEnergyPolarIsometry := by
    rw [← hc.closure_eq]
    exact hd e
  exact he

def radialEnergyPolarUnitary : RadialL2 ≃ₗᵢ[ℂ] radialClosedEnergyDomain 1 :=
  LinearIsometryEquiv.ofSurjective radialEnergyPolarIsometry
    radialEnergyPolarIsometry_surjective

theorem radialPhysicalEmbedding_polar (F : RadialL2) :
    radialPhysicalEmbedding 1 (radialEnergyPolarUnitary F) =
      radialResolventSquareRoot F := by
  have heq : (fun G : RadialL2 => radialPhysicalEmbedding 1
      (radialEnergyPolarUnitary G)) = radialResolventSquareRoot := by
    apply ((radialPhysicalEmbedding 1).continuous.comp
      radialEnergyPolarUnitary.continuous).ext_on
      radialResolventSquareRoot_denseRange radialResolventSquareRoot.continuous
    rintro _ ⟨G, rfl⟩
    change radialPhysicalEmbedding 1
      (radialEnergyPolarExtension (radialResolventSquareRoot G)) = _
    rw [radialEnergyPolarExtension_apply_squareRoot]
    change radialUnitShiftResolvent G =
      radialResolventSquareRoot (radialResolventSquareRoot G)
    rw [← ContinuousLinearMap.mul_apply, radialResolventSquareRoot_square]
  exact congrFun heq F

/-- Exact physical range of the original closed radial form. -/
theorem radialPhysicalEmbedding_range_eq_squareRoot_range :
    (radialPhysicalEmbedding 1).range = radialResolventSquareRoot.range := by
  apply le_antisymm
  · rintro F ⟨e, rfl⟩
    refine ⟨radialEnergyPolarUnitary.symm e, ?_⟩
    rw [← radialPhysicalEmbedding_polar, radialEnergyPolarUnitary.apply_symm_apply]
  · rintro F ⟨G, rfl⟩
    exact ⟨radialEnergyPolarUnitary G, radialPhysicalEmbedding_polar G⟩

theorem radialClosedEnergyDomain_physical_iff_squareRoot_range (F : RadialL2) :
    (∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e = F) ↔
      ∃ G : RadialL2, radialResolventSquareRoot G = F := by
  change F ∈ (radialPhysicalEmbedding 1).range ↔ F ∈ radialResolventSquareRoot.range
  rw [radialPhysicalEmbedding_range_eq_squareRoot_range]

/-- All three actual coordinates retain their ORIGINAL full energy norm. -/
theorem radialEnergyPolarUnitary_full_norm (G : RadialL2) :
    ‖radialResolventSquareRoot G‖ ^ 2 +
      ‖radialClosedDerivative 1 (radialEnergyPolarUnitary G)‖ ^ 2 +
      ‖radialClosedExponential 1 (radialEnergyPolarUnitary G)‖ ^ 2 = ‖G‖ ^ 2 := by
  have he := congrArg Complex.re (radialClosedEnergy_inner 1 (by norm_num)
    (radialEnergyPolarUnitary G) (radialEnergyPolarUnitary G))
  simp only [Complex.add_re, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
    Complex.ofReal_re] at he
  norm_num at he
  rw [radialPhysicalEmbedding_polar, radialEnergyPolarUnitary.norm_map] at he
  exact he.symm

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
