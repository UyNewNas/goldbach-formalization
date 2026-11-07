import ImbalancedChen.Part3GammaMeanCenteredScalarMeasure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An actual native Gamma0 Friedrichs eigenvector is localized at its true
real Laplace coordinate for every Borel projection. The proof starts
from the already proved actual native graph/fiberwise lambda graph
equivalence. It removes the null zero resolvent fiber and cancels the
scalar multiplier away from the given eigenvalue. No cusp condition,
spectral expansion, spectral gap, or localization premise is assumed.
-/
namespace ImbalancedChen.Part3.GammaNativeEigenBorelLocalization20261026b

noncomputable section
open Set MeasureTheory
open GenericResolventScalarMeasure20261025a
open GenericResolventScalarZeroAtom20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventUnboundedMultiplication20261025a
open GenericResolventUnboundedScalarMeasure20261025a
open GenericResolventGlobalSpectralAssembly20261025a
open GenericResolventGlobalUnboundedMultiplication20261025a
open GenericCyclicBorelProjection20261025a
open GenericGlobalBorelProjection20261025a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualGlobalLambdaDomain20261025a
open GammaMeanCenteredScalarMeasure20261026b

section Fiber
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (hRinj : Function.Injective R)

/-- The two existing total lambda conventions coincide away from r=0. -/
theorem lambdaCoordinate_eq_spectralLambda_of_ne_zero (r : ResolventSpectrum R)
    (hr : (r : ℝ) ≠ 0) : lambdaCoordinate R r = spectralLambda R r := by
  unfold lambdaCoordinate spectralLambda
  field_simp [hr]
  <;> ring

/-- A genuine scalar multiplication eigen equation forces the actual L2
representative to vanish away from that eigenvalue. -/
theorem native_eigen_fiber_support (f : H) (a : ScalarL2 R hSA f) (λ : ℝ)
    (ha : ((λ : ℂ) • a) =ᵐ[scalarMeasure R hSA f] lambdaProduct R hSA f a) :
    ∀ᵐ r ∂scalarMeasure R hSA f, spectralLambda R r ≠ λ → a r = 0 := by
  filter_upwards [ha, Lp.coeFn_smul (λ : ℂ) a,
    scalarMeasure_ae_coordinate_ne_zero R hSA hRinj f] with r he hs hr
  intro hne
  rw [hs] at he
  change (λ : ℂ) * a r = (lambdaCoordinate R r : ℂ) * a r at he
  rw [lambdaCoordinate_eq_spectralLambda_of_ne_zero R r hr] at he
  have hmul : ((λ : ℂ) - (spectralLambda R r : ℂ)) * a r = 0 := by
    linear_combination he
  have hc : (λ : ℂ) - (spectralLambda R r : ℂ) ≠ 0 := by
    intro hz
    exact hne (Complex.ofReal_injective (sub_eq_zero.mp hz)).symm
  exact (mul_eq_zero.mp hmul).resolve_left hc

/-- Every real Borel multiplier on a native eigenfiber is the corresponding
zero-or-one scalar, proved on the actual scalar-measure L2 quotient. -/
theorem native_eigen_fiber_borel_apply (f : H) (a : ScalarL2 R hSA f) (λ : ℝ)
    (ha : ((λ : ℂ) • a) =ᵐ[scalarMeasure R hSA f] lambdaProduct R hSA f a)
    (B : Set ℝ) (hB : MeasurableSet B) :
    borelMultiplier R hSA f (spectralLambda R ⁻¹' B) ((measurable_spectralLambda R) hB) a =
      if λ ∈ B then a else 0 := by
  have hs := native_eigen_fiber_support R hSA hRinj f a λ ha
  by_cases hλ : λ ∈ B
  · rw [if_pos hλ]
    apply Lp.ext
    filter_upwards [hs, borelMultiplier_coe_ae R hSA f
      (spectralLambda R ⁻¹' B) ((measurable_spectralLambda R) hB) a] with r hr hproj
    rw [hproj]
    by_cases hmem : spectralLambda R r ∈ B
    · exact Set.indicator_of_mem hmem _
    · have hne : spectralLambda R r ≠ λ := by
        intro heq
        exact hmem (heq.symm ▸ hλ)
      simp only [Set.mem_preimage, hmem, not_false_eq_true, Set.indicator_of_notMem,
        hr hne]
  · rw [if_neg hλ]
    apply Lp.ext
    filter_upwards [hs, borelMultiplier_coe_ae R hSA f
      (spectralLambda R ⁻¹' B) ((measurable_spectralLambda R) hB) a,
      Lp.coeFn_zero ℂ (2 : ℝ≥0∞) (scalarMeasure R hSA f)] with r hr hproj hz
    rw [hproj, hz]
    by_cases hmem : spectralLambda R r ∈ B
    · have hne : spectralLambda R r ≠ λ := by
        intro heq
        exact hλ (heq ▸ hmem)
      simp only [Set.mem_preimage, hmem, Set.indicator_of_mem, hr hne]
    · exact Set.indicator_of_notMem hmem _
end Fiber

/-- Actual physical native graph membership, rather than a supplied
spectral action, determines every real-lambda Borel projection. -/
theorem actual_native_eigenvector_borel_apply (N : ℕ) [NeZero N]
    (u : QuotientL2 N) (λ : ℝ)
    (hu : (u, (λ : ℂ) • u) ∈ (actualGammaFriedrichs N).graph)
    (B : Set ℝ) (hB : MeasurableSet B) :
    actualLaplaceBorelProjection N B hB u = if λ ∈ B then u else 0 := by
  let U := spectralUnitary (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
  let a := U.symm u
  have hg := (actualGammaFriedrichs_global_graph_iff_lambda N u ((λ : ℂ) • u)).mp hu
  change FamilyLambdaGraph (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    a (U.symm ((λ : ℂ) • u)) at hg
  rw [map_smul] at hg
  have hD : diagonalBorel (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
      (spectralLambda (actualGammaResolvent N) ⁻¹' B)
      ((measurable_spectralLambda (actualGammaResolvent N)) hB) a =
      if λ ∈ B then a else 0 := by
    by_cases hλ : λ ∈ B
    · rw [if_pos hλ]
      apply lp.ext
      intro i
      simpa only [if_pos hλ] using native_eigen_fiber_borel_apply
        (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        (actualGammaResolvent_injective N) (i : QuotientL2 N) (a i) λ (hg i) B hB
    · rw [if_neg hλ]
      apply lp.ext
      intro i
      simpa only [if_neg hλ] using native_eigen_fiber_borel_apply
        (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        (actualGammaResolvent_injective N) (i : QuotientL2 N) (a i) λ (hg i) B hB
  change U (diagonalBorel (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (spectralLambda (actualGammaResolvent N) ⁻¹' B)
    ((measurable_spectralLambda (actualGammaResolvent N)) hB) a) = _
  rw [hD]
  by_cases hλ : λ ∈ B
  · simp only [if_pos hλ, a, U.apply_symm_apply]
  · simp only [if_neg hλ, map_zero]

end
end ImbalancedChen.Part3.GammaNativeEigenBorelLocalization20261026b
