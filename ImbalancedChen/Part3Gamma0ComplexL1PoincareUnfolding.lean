import ImbalancedChen.Part3Gamma0NonnegativePoincareUnfolding
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Complex L1 Poincare unfolding for the ACTUAL effective Gamma0 action.
The only analytic input is that the seed is integrable for canonical
hyperbolic volume on H. The exact norm-mass decomposition over the actual
disjoint conull cells proves a.e. absolute convergence and the finite
norm-integral premise required for Bochner tsum interchange. It is not
supplied as hAbsSum. The complex quotient series uses the existing actual
measurable reduced-carrier section and counts the full central kernel once.
No pointwise-everywhere convergence, proper-action/local-finiteness,
Fourier-Bessel coefficient, or spectral/Kuznetsov theorem is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0NonnegativePoincareUnfolding20261025a

/-- The actual matrix-translated complex seed. -/
def translatedSeed (N : ℕ) (f : UpperHalfPlane → ℂ)
    (q : effectiveGamma0 N) (z : UpperHalfPlane) : ℂ :=
  f (effectiveMatrixAction N q z)

theorem translatedSeed_aestronglyMeasurable (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane))
    (q : effectiveGamma0 N) :
    AEStronglyMeasurable (translatedSeed N f q)
      ((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)) :=
  (hf.aestronglyMeasurable.comp_measurePreserving
    (effectiveMatrixAction_measurePreserving N q)).restrict

/-- Exact absolute-mass partition for the actual translated seeds. Its
right side is the ORIGINAL seed norm mass, not an assumed series bound. -/
theorem translatedSeed_norm_mass (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) :
    (∑' q : effectiveGamma0 N,
      ∫⁻ z in reducedCarrier N, ‖translatedSeed N f q z‖ₑ) =
        ∫⁻ z, ‖f z‖ₑ ∂(volume : Measure UpperHalfPlane) := by
  letI : Countable (effectiveGamma0 N) := inferInstance
  have hdisj : Pairwise (Disjoint on effectiveCell N) := by
    intro q r hqr
    exact effectiveCell_disjoint N hqr
  calc
    _ = ∑' q : effectiveGamma0 N, ∫⁻ z in effectiveCell N q, ‖f z‖ₑ := by
      apply tsum_congr
      intro q
      exact (lintegral_effectiveCell N q (fun z => ‖f z‖ₑ)).symm
    _ = ∫⁻ z in allEffectiveCells N, ‖f z‖ₑ :=
      (lintegral_iUnion (effectiveCell_measurable N) hdisj _).symm
    _ = _ := by rw [Measure.restrict_eq_self_of_ae_mem (allEffectiveCells_ae N)]

theorem translatedSeed_norm_mass_finite (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    (∑' q : effectiveGamma0 N,
      ∫⁻ z in reducedCarrier N, ‖translatedSeed N f q z‖ₑ) ≠ ∞ := by
  rw [translatedSeed_norm_mass]
  exact hf.hasFiniteIntegral.ne

/-- Actual effective Gamma0 Poincare terms are absolutely summable for
almost every representative, derived solely from the integrable seed. -/
theorem absolute_convergence_carrier (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)),
      Summable (fun q : effectiveGamma0 N => ‖translatedSeed N f q z‖) := by
  letI : Countable (effectiveGamma0 N) := inferInstance
  have hmeas (q : effectiveGamma0 N) :
      AEMeasurable (fun z => ‖translatedSeed N f q z‖ₑ)
        ((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)) :=
    (translatedSeed_aestronglyMeasurable N f hf q).enorm
  have hfinite :
      (∫⁻ z in reducedCarrier N,
        ∑' q : effectiveGamma0 N, ‖translatedSeed N f q z‖ₑ) ≠ ∞ := by
    rw [lintegral_tsum hmeas]
    exact translatedSeed_norm_mass_finite N f hf
  have h := ae_lt_top' (AEMeasurable.tsum hmeas) hfinite
  filter_upwards [h] with z hz
  exact tsum_enorm_ne_top_iff_summable_norm.mp hz.ne

/-- The actual full complex trace, with the conventional zero value only
on the exceptional points where its series is not summable. -/
def complexSeedTrace (N : ℕ) (f : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) : ℂ := ∑' q : effectiveGamma0 N, translatedSeed N f q z

/-- The trace itself is integrable, so the unfolding below cannot be an
identity of divergent Bochner integrals with default zero values. -/
theorem complexSeedTrace_integrable (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    Integrable (complexSeedTrace N f)
      ((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)) := by
  letI : Countable (effectiveGamma0 N) := inferInstance
  have hterm := translatedSeed_aestronglyMeasurable N f hf
  have hmeas : AEStronglyMeasurable (complexSeedTrace N f)
      ((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)) :=
    (AEMeasurable.tsum (fun q => (hterm q).aemeasurable)).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  change (∫⁻ z in reducedCarrier N, ‖complexSeedTrace N f z‖ₑ) < ∞
  calc
    (∫⁻ z in reducedCarrier N, ‖complexSeedTrace N f z‖ₑ) ≤
        ∫⁻ z in reducedCarrier N,
          ∑' q : effectiveGamma0 N, ‖translatedSeed N f q z‖ₑ := by
      apply lintegral_mono
      intro z
      exact enorm_tsum_le_tsum_enorm
    _ = ∑' q : effectiveGamma0 N,
        ∫⁻ z in reducedCarrier N, ‖translatedSeed N f q z‖ₑ :=
      lintegral_tsum (fun q => (hterm q).enorm)
    _ < ∞ := (translatedSeed_norm_mass_finite N f hf).lt_top

/-- Bochner change of variables on one actual canonical-volume cell. -/
theorem integral_effectiveCell (N : ℕ) [NeZero N]
    (q : effectiveGamma0 N) (f : UpperHalfPlane → ℂ) :
    (∫ z in effectiveCell N q, f z) =
      ∫ z in reducedCarrier N, translatedSeed N f q z := by
  have h := (effectiveMatrixAction_measurableEmbedding N q).setIntegral_map
    (μ := (volume : Measure UpperHalfPlane)) f
    (effectiveMatrixAction N q '' reducedCarrier N)
  rw [(effectiveMatrixAction_measurePreserving N q).map_eq] at h
  simpa only [Set.preimage_image_eq _
    (effectiveMatrixAction_measurableEmbedding N q).injective] using h

/-- Actual complex carrier unfolding, with the Bochner tsum condition
PROVED by the seed norm-mass identity. -/
theorem complex_carrier_unfolding (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    (∫ z in reducedCarrier N, complexSeedTrace N f z) =
      ∫ z, f z ∂(volume : Measure UpperHalfPlane) := by
  letI : Countable (effectiveGamma0 N) := inferInstance
  have hdisj : Pairwise (Disjoint on effectiveCell N) := by
    intro q r hqr
    exact effectiveCell_disjoint N hqr
  calc
    _ = ∑' q : effectiveGamma0 N,
        ∫ z in reducedCarrier N, translatedSeed N f q z :=
      integral_tsum (translatedSeed_aestronglyMeasurable N f hf)
        (translatedSeed_norm_mass_finite N f hf)
    _ = ∑' q : effectiveGamma0 N, ∫ z in effectiveCell N q, f z := by
      apply tsum_congr
      intro q
      exact (integral_effectiveCell N q f).symm
    _ = ∫ z in allEffectiveCells N, f z :=
      (integral_iUnion (effectiveCell_measurable N) hdisj hf.integrableOn).symm
    _ = _ := by rw [Measure.restrict_eq_self_of_ae_mem (allEffectiveCells_ae N)]

/-- Each complex quotient term uses the SAME actual reduced section. -/
def quotientSeedTerm (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (q : effectiveGamma0 N) : Gamma0OrbitSpace N → ℂ :=
  Function.extend (reducedProjection N)
    (fun z : reducedCarrier N => translatedSeed N f q z) (fun _ => 0)

theorem quotientSeedTerm_projection (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (q : effectiveGamma0 N) (z : reducedCarrier N) :
    quotientSeedTerm N f q (reducedProjection N z) = translatedSeed N f q z :=
  (reducedProjection_measurableEmbedding N).injective.extend_apply _ _ z

/-- The actual complex quotient Poincare series, term by term. -/
def complexPoincare (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (u : Gamma0OrbitSpace N) : ℂ :=
  ∑' q : effectiveGamma0 N, quotientSeedTerm N f q u

theorem complexPoincare_projection (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (z : reducedCarrier N) :
    complexPoincare N f (reducedProjection N z) = complexSeedTrace N f z := by
  apply tsum_congr
  intro q
  exact quotientSeedTerm_projection N f q z

/-- Actual quotient a.e. absolute convergence, transported through the
proved canonical measure map rather than assumed as hAbsSum. -/
theorem absolute_convergence_quotient (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    ∀ᵐ u ∂carrierPushforward N,
      Summable (fun q : effectiveGamma0 N => ‖quotientSeedTerm N f q u‖) := by
  have hcarrier := absolute_convergence_carrier N f hf
  have hsubMap : (reducedCarrierMeasure N).map
      (Subtype.val : reducedCarrier N → UpperHalfPlane) =
        (volume : Measure UpperHalfPlane).restrict (reducedCarrier N) :=
    Measure.map_comap_subtype_coe (reducedCarrier_measurable N) _
  rw [← hsubMap,
    (MeasurableEmbedding.subtype_coe (reducedCarrier_measurable N)).ae_map_iff] at hcarrier
  rw [← reducedProjection_map_measure N,
    (reducedProjection_measurableEmbedding N).ae_map_iff]
  simpa only [quotientSeedTerm_projection] using hcarrier

/-- L1 integrability of the actual complex quotient series. -/
theorem complexPoincare_integrable (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    Integrable (complexPoincare N f) (carrierPushforward N) := by
  rw [← reducedProjection_map_measure N,
    (reducedProjection_measurableEmbedding N).integrable_map_iff]
  have htrace : Integrable
      (fun z : reducedCarrier N => complexSeedTrace N f z) (reducedCarrierMeasure N) :=
    (integrableOn_iff_comap_subtypeVal (reducedCarrier_measurable N)).mp
      (complexSeedTrace_integrable N f hf)
  have hcomp : complexPoincare N f ∘ reducedProjection N =
      fun z : reducedCarrier N => complexSeedTrace N f z := by
    funext z
    exact complexPoincare_projection N f z
  rw [hcomp]
  exact htrace

/-- Actual complex L1 Poincare unfolding against the canonical spatial
quotient measure. Both the series' absolute convergence a.e. and its L1
integrability were proved from Integrable seed on H. -/
theorem complex_poincare_unfolding (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    (∫ u, complexPoincare N f u ∂carrierPushforward N) =
      ∫ z, f z ∂(volume : Measure UpperHalfPlane) := by
  calc
    _ = ∫ z : reducedCarrier N, complexSeedTrace N f z ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (complexPoincare_projection N f)
    _ = ∫ z in reducedCarrier N, complexSeedTrace N f z :=
      integral_subtype_comap (reducedCarrier_measurable N) _
    _ = _ := complex_carrier_unfolding N f hf

end
end ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a