import ImbalancedChen.Part3ActualNormalizedEigenFrameWeakPDE
import ImbalancedChen.Part3WeakEigenCompactClassicalEstimate
import ImbalancedChen.Part3ActualSmoothFrameCompactMassBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Uniform compact mixed-derivative bounds in the ORIGINAL normalized cusp
frame. The constant is fixed before lambda, f and its SAME-AE classical
representative. The profile solves the generic weak inverse-square PDE;
its fixed outer ordinary L2 mass is controlled by the genuine compact
frame quotient estimate. Thus no high-order Mobius derivative bound is
assumed and no profile-dependent constant is substituted for the result.
-/

namespace ImbalancedChen.Part3.UniformNormalizedEigenFrameClassicalBound20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane ContDiff
open ProductConvolutionSecondDerivatives20261026a
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeakOperatorCore20261024zz
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0QuotientCellPushforward20261025a
open ActualEigenNormalizedSmoothFrame20261026b
open ActualNormalizedEigenFrameWeakPDE20261026b WeakEigenCompactClassicalEstimate20261026b
open ActualSmoothFrameCompactMassBudget20261026b
open PlanarLocalPoissonH1Regularity20261026b PlanarQuantitativePoissonRectangle20261026b
open PlanarWeakDifferentialMultiindex20261026b
open GammaActualEigenSmoothRepresentative20261026b

/-- Constants depend on the actual fixed frame and compact set only.
All derivative orders up to k share this ONE constant. -/
theorem exists_uniform_normalized_frame_classical_bound (N : ℕ) [NeZero N]
    (hN : 0<N) (g : SL(2,ℤ)) (k : ℕ) (K : Set Plane)
    (hK : IsCompact K) (hKpos : K⊆upperChart) :
    ∃ C : ℝ,0≤C ∧ ∀ (lambda : ℝ) (f : QuotientL2 N) (Phi : UpperHalfPlane → ℂ),
      ContDiffOn ℝ ∞ (extendUpper Phi) upperChart →
      (Phi =ᵐ[(volume : Measure UpperHalfPlane)] fun z => f (orbitProjection N z)) →
      (∀ z,upperMaass Phi z=(lambda : ℂ)*Phi z) →
      ∀ α : MultiIndex,α.1+α.2≤k → ∀ p∈K,
        ‖testPartial α (smoothFrame N g Phi) p‖ ≤ C*(1+|lambda|)^(k+2)*‖f‖ := by
  obtain ⟨Kout,hKout,hKKout,hKoutpos,A,hA,hestimate⟩ :=
    exists_weak_eigen_compact_classical_bound k K hK hKpos
  obtain ⟨B,hB,hmass⟩ := exists_uniform_smoothFrame_compact_mass N hN g hKout hKoutpos
  refine ⟨A*Real.sqrt B,mul_nonneg hA (Real.sqrt_nonneg _),?_⟩
  intro lambda f Phi hPhi hAE hPDE
  have hlocal : LocallyL2On upperChart (smoothFrame N g Phi) := by
    intro S hS hSpos
    obtain ⟨B',hB',hSbudget⟩ := exists_uniform_smoothFrame_compact_mass N hN g hS hSpos
    exact (hSbudget f Phi hAE).1
  have hweak := actual_normalized_smooth_frame_hasWeakPoisson N hN g Phi hPhi lambda hPDE
  have hclassical := smoothFrame_contDiffOn N hN g Phi hPhi
  have hsquare := (hmass f Phi hAE).2
  have hsqrt : Real.sqrt (localSquareMass Kout (smoothFrame N g Phi)) ≤ Real.sqrt B*‖f‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt hB,
      Real.sq_sqrt (localSquareMass_nonneg Kout (smoothFrame N g Phi))] using hsquare
  intro α hα p hp
  calc
    _ ≤ A*(1+|lambda|)^(k+2)*Real.sqrt (localSquareMass Kout (smoothFrame N g Phi)) :=
      hestimate lambda (smoothFrame N g Phi) (smoothFrame N g Phi) hlocal hweak hclassical
        Filter.EventuallyEq.rfl α hα p hp
    _ ≤ A*(1+|lambda|)^(k+2)*(Real.sqrt B*‖f‖) :=
      mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hA (by positivity))
    _ = _ := by ring

/-- The actual native eigenpair produces the representative to which
the preceding universal constant applies; no classical eigenfunction
or derivative budget is assumed by this endpoint. -/
theorem actual_native_eigen_normalized_frame_compact_bound (N : ℕ) [NeZero N]
    (hN : 0<N) (g : SL(2,ℤ)) (k : ℕ) (K : Set Plane)
    (hK : IsCompact K) (hKpos : K⊆upperChart) :
    ∃ C : ℝ,0≤C ∧ ∀ (lambda : ℝ) (f : QuotientL2 N),
      (f,(lambda : ℂ) • f)∈(actualClosedGammaMaass N).graph →
      ∃ Phi : UpperHalfPlane → ℂ,
        (Phi =ᵐ[(volume : Measure UpperHalfPlane)] fun z => f (orbitProjection N z)) ∧
        ContDiffOn ℝ ∞ (extendUpper Phi) upperChart ∧
        GammaSmoothMultiplierPeriodization20261026a.IsGammaInvariant N Phi ∧
        (∀ z,upperMaass Phi z=(lambda : ℂ)*Phi z) ∧
        ∀ α : MultiIndex,α.1+α.2≤k → ∀ p∈K,
          ‖testPartial α (smoothFrame N g Phi) p‖ ≤ C*(1+|lambda|)^(k+2)*‖f‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_normalized_frame_classical_bound N hN g k K hK hKpos
  refine ⟨C,hC,?_⟩
  intro lambda f hEigen
  obtain ⟨Phi,hPhi,hAE,hGamma,hPDE⟩ :=
    actual_native_eigen_has_smooth_upper_representative N lambda f hEigen
  exact ⟨Phi,hAE,hPhi,hGamma,hPDE,hbound lambda f Phi hPhi hAE hPDE⟩

end
end ImbalancedChen.Part3.UniformNormalizedEigenFrameClassicalBound20261026b
