import ImbalancedChen.Part3Gamma0ActualSigmaPlancherel
import ImbalancedChen.Part3GenericResolventContinuousMultipliers

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The FULL bounded continuous functional calculus of the ACTUAL Gamma0
resolvent acts by literal spectrum-function multiplication in the true
single-Sigma-measure Plancherel model. The multiplier is constructed on
the whole (possibly infinite-mass) Sigma measure, with uniform bound
norm phi inherited on every fiber. Full-H CFC intertwining comes from
the genuine generic cyclic density argument and convergent Hilbert sums.

This gives an operator identity, all-vector AE action, mixed Parseval
coefficient integral and weighted norm identity. No hIntertwine,
hNormMatch or spectral-representation premise is accepted. The measure
is abstract; no standard cusp/Eisenstein normalization is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0ActualSigmaContinuousCFC20261025a

noncomputable section
open Set MeasureTheory Filter
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualGlobalFriedrichsGraph20261025a
open Gamma0ActualGlobalLambdaDomain20261025a
open Gamma0ActualSigmaPlancherel20261025a
open GenericResolventScalarMeasure20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventContinuousMultipliers20261025a
open CountableSigmaMeasureBundle20261025a

def actualGammaContinuousCFC (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) :
    QuotientL2 N→L[ℂ]QuotientL2 N :=
  complexResolventCFC (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) φ

def actualSigmaContinuousProduct (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (g : ActualSigmaL2 N) :
    ActualSigmaSpectrum N→ℂ := fun s => φ s.2*g s

theorem actualSigmaContinuousProduct_memLp (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (g : ActualSigmaL2 N) :
    MemLp (actualSigmaContinuousProduct N φ g) 2 (actualSigmaMeasure N) := by
  have hmeas : AEStronglyMeasurable (actualSigmaContinuousProduct N φ g)
      (actualSigmaMeasure N) := by
    apply (bundle_aestronglyMeasurable_iff (actualSigmaFiberMeasure N) _).mpr
    intro i
    exact φ.continuous.aestronglyMeasurable.mul
      ((bundle_aestronglyMeasurable_iff (actualSigmaFiberMeasure N) g).mp
        (Lp.aestronglyMeasurable g) i)
  apply (Lp.memLp g).of_le_mul hmeas
  exact Filter.Eventually.of_forall fun s => by
    rw [actualSigmaContinuousProduct,norm_mul]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm s.2) (norm_nonneg _)

def actualSigmaContinuousMultiply (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (g : ActualSigmaL2 N) :
    ActualSigmaL2 N :=
  (actualSigmaContinuousProduct_memLp N φ g).toLp (actualSigmaContinuousProduct N φ g)

theorem actualSigmaContinuousMultiply_coe_ae (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (g : ActualSigmaL2 N) :
    actualSigmaContinuousMultiply N φ g=ᵐ[actualSigmaMeasure N]
      actualSigmaContinuousProduct N φ g :=
  (actualSigmaContinuousProduct_memLp N φ g).coeFn_toLp

def actualSigmaContinuousMultiplyLinear (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) :
    ActualSigmaL2 N→ₗ[ℂ]ActualSigmaL2 N where
  toFun := actualSigmaContinuousMultiply N φ
  map_add' g h := by
    apply Lp.ext
    filter_upwards [actualSigmaContinuousMultiply_coe_ae N φ (g+h),Lp.coeFn_add g h,
      Lp.coeFn_add (actualSigmaContinuousMultiply N φ g) (actualSigmaContinuousMultiply N φ h),
      actualSigmaContinuousMultiply_coe_ae N φ g,actualSigmaContinuousMultiply_coe_ae N φ h]
      with s hleft hin hright hg hh
    simp only [actualSigmaContinuousProduct] at hleft hg hh
    rw [hleft,hright,hg,hh,hin]
    ring
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [actualSigmaContinuousMultiply_coe_ae N φ (c•g),Lp.coeFn_smul c g,
      Lp.coeFn_smul c (actualSigmaContinuousMultiply N φ g),actualSigmaContinuousMultiply_coe_ae N φ g]
      with s hleft hin hright hg
    simp only [actualSigmaContinuousProduct] at hleft hg
    rw [hleft,hright,hg,hin]
    simp only [smul_eq_mul]
    ring

theorem actualSigmaContinuousMultiply_norm_le (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (g : ActualSigmaL2 N) :
    ‖actualSigmaContinuousMultiply N φ g‖≤‖φ‖*‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [actualSigmaContinuousMultiply_coe_ae N φ g] with s hs
  rw [hs,actualSigmaContinuousProduct,norm_mul]
  exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm s.2) (norm_nonneg _)

def actualSigmaContinuousMultiplier (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) :
    ActualSigmaL2 N→L[ℂ]ActualSigmaL2 N :=
  (actualSigmaContinuousMultiplyLinear N φ).mkContinuous ‖φ‖
    (actualSigmaContinuousMultiply_norm_le N φ)

theorem actualSigmaContinuousMultiplier_opNorm_le (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) :
    ‖actualSigmaContinuousMultiplier N φ‖≤‖φ‖ :=
  (actualSigmaContinuousMultiplier N φ).opNorm_le_bound (norm_nonneg φ)
    (actualSigmaContinuousMultiply_norm_le N φ)

/-- ALL actual physical vectors, not just continuous cyclic core data.
This uses the genuine generic all-H CFC coordinates, then the literal
Sigma fiber AE decomposition and actual Plancherel fiber identity. -/
theorem actualSigmaPlancherel_cfc_ae (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (u : QuotientL2 N) :
    actualSigmaPlancherel N (actualGammaContinuousCFC N φ u)=ᵐ[actualSigmaMeasure N]
      actualSigmaContinuousProduct N φ (actualSigmaPlancherel N u) := by
  have hcoords : actualGlobalSpectralCoordinates N (actualGammaContinuousCFC N φ u)=
      diagonalContinuousMultiplier (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) φ
        (actualGlobalSpectralCoordinates N u) :=
    cfc_spectral_coordinates (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) φ u
  apply (bundle_ae_iff (actualSigmaFiberMeasure N) _).mpr
  intro i
  have hleft := actualSigmaPlancherel_fiber N (actualGammaContinuousCFC N φ u) i
  have hin := actualSigmaPlancherel_fiber N u i
  have hmul := continuousMultiplier_coe_ae (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) φ (i:QuotientL2 N)
      (actualGlobalSpectralCoordinates N u i)
  rw [hcoords] at hleft
  filter_upwards [hleft,hin,hmul] with t hlt hint hmult
  change actualSigmaPlancherel N (actualGammaContinuousCFC N φ u) ⟨i,t⟩=
    φ t*actualSigmaPlancherel N u ⟨i,t⟩
  calc
    _ = diagonalContinuousMultiplier (actualGammaResolvent N)
        (actualGammaResolvent_selfAdjoint N) φ (actualGlobalSpectralCoordinates N u) i t := hlt
    _ = φ t*actualGlobalSpectralCoordinates N u i t := hmult
    _ = _ := by rw [hint]

theorem actualSigmaPlancherel_cfc (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (u : QuotientL2 N) :
    actualSigmaPlancherel N (actualGammaContinuousCFC N φ u)=
      actualSigmaContinuousMultiplier N φ (actualSigmaPlancherel N u) := by
  apply Lp.ext
  exact (actualSigmaPlancherel_cfc_ae N φ u).trans
    (actualSigmaContinuousMultiply_coe_ae N φ (actualSigmaPlancherel N u)).symm

/-- A full bounded-operator conjugacy on the physical Gamma0 Hilbert
space, not an alias for the coordinate resolvent. -/
theorem actualGammaContinuousCFC_sigma_conjugacy (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) :
    actualGammaContinuousCFC N φ=
      (actualSigmaPlancherel N).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((actualSigmaContinuousMultiplier N φ).comp
          (actualSigmaPlancherel N).toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext u
  apply (actualSigmaPlancherel N).injective
  change actualSigmaPlancherel N (actualGammaContinuousCFC N φ u)=
    actualSigmaPlancherel N ((actualSigmaPlancherel N).symm
      (actualSigmaContinuousMultiplier N φ (actualSigmaPlancherel N u)))
  rw [LinearIsometryEquiv.apply_symm_apply,actualSigmaPlancherel_cfc]

theorem actualSigmaCFC_coefficient_integrable (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (u v : QuotientL2 N) :
    Integrable (fun s => star (actualSigmaPlancherel N u s)*φ s.2*
      actualSigmaPlancherel N v s) (actualSigmaMeasure N) := by
  apply (L2.integrable_inner (actualSigmaPlancherel N u)
    (actualSigmaPlancherel N (actualGammaContinuousCFC N φ v))).congr
  filter_upwards [actualSigmaPlancherel_cfc_ae N φ v] with s hs
  simp only [actualSigmaContinuousProduct] at hs
  simp only [RCLike.inner_apply',hs]
  ring

/-- Exact mixed Parseval coefficient integral for all physical vectors.
The measure is the genuine abstract Sigma scalar spectral bundle. -/
theorem actualGammaContinuousCFC_sigma_coefficient (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (u v : QuotientL2 N) :
    inner ℂ u (actualGammaContinuousCFC N φ v)=
      ∫ s,star (actualSigmaPlancherel N u s)*φ s.2*actualSigmaPlancherel N v s
        ∂actualSigmaMeasure N := by
  rw [← (actualSigmaPlancherel N).inner_map_map u (actualGammaContinuousCFC N φ v),L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actualSigmaPlancherel_cfc_ae N φ v] with s hs
  simp only [actualSigmaContinuousProduct] at hs
  simp only [RCLike.inner_apply',hs]
  ring

theorem actualGammaContinuousCFC_sigma_norm_sq (N : ℕ) [NeZero N]
    (φ : C(ResolventSpectrum (actualGammaResolvent N),ℂ)) (u : QuotientL2 N) :
    ‖actualGammaContinuousCFC N φ u‖^2=
      ∫ s,‖φ s.2‖^2*‖actualSigmaPlancherel N u s‖^2∂actualSigmaMeasure N := by
  rw [← actualSigmaPlancherel_integral N (actualGammaContinuousCFC N φ u)]
  apply integral_congr_ae
  filter_upwards [actualSigmaPlancherel_cfc_ae N φ u] with s hs
  simp only [actualSigmaContinuousProduct] at hs
  rw [hs,norm_mul,mul_pow]

end
end ImbalancedChen.Part3.Gamma0ActualSigmaContinuousCFC20261025a
