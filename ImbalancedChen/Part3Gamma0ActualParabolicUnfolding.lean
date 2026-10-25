import ImbalancedChen.Part3Gamma0ParabolicEffectiveDecomposition

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Genuine GammaInfinity\Gamma0 Poincare unfolding from the proved actual
effectiveGamma0/integer-by-parabolic-coset bijection. For a periodic cusp
seed F, the H seed used by full-Gamma0 unfolding is strip.indicator F.
It is H-L1 precisely from the given STRIP-L1 condition; F itself is never
assumed H-L1. The exact integer-strip recovery and actual coset reindex
identify the resulting series with the actual parabolic Poincare trace.
Norm convergence and Bochner exchange are derived from the true norm
partition, not supplied as hAbsSum. The quotient function uses the actual
canonical reduced-carrier section and actual canonical quotient measure.
-/

namespace ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0NonnegativePoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a

private theorem parabolicAction_measurable (N : ℕ) (q : GammaInfinityCosets N) :
    Measurable (fun z : UpperHalfPlane => parabolicRepresentative N q • z) := by
  change Measurable (fun z : UpperHalfPlane =>
    (SpecialLinearGroup.mapGL ℝ (parabolicRepresentative N q : SL(2, ℤ))) • z)
  exact (continuous_const_smul _).measurable

/-- A true nonnegative sum over ACTUAL GammaInfinity-leftcosets. -/
def parabolicTraceNN (N : ℕ) (F : UpperHalfPlane → ℝ≥0∞)
    (z : UpperHalfPlane) : ℝ≥0∞ :=
  ∑' q : GammaInfinityCosets N, F (parabolicRepresentative N q • z)

theorem parabolicTraceNN_measurable (N : ℕ) (F : UpperHalfPlane → ℝ≥0∞)
    (hF : Measurable F) : Measurable (parabolicTraceNN N F) := by
  letI : Countable (GammaInfinityCosets N) := inferInstance
  exact Measurable.tsum (fun q => hF.comp (parabolicAction_measurable N q))

/-- Actual nonnegative parabolic unfolding on the true Gamma0 carrier,
with the periodic cusp seed integrated only on its translation strip. -/
theorem nonnegative_parabolic_carrier_unfolding (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℝ≥0∞)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z) (hF : Measurable F) :
    (∫⁻ z in reducedCarrier N, parabolicTraceNN N F z) = ∫⁻ z in strip, F z := by
  calc
    _ = ∫⁻ z in reducedCarrier N, fullSeedTrace N (strip.indicator F) z := by
      apply lintegral_congr
      intro z
      exact (nonnegative_effective_trace_eq_parabolic N F hperiod z).symm
    _ = ∫⁻ z, strip.indicator F z ∂(volume : Measure UpperHalfPlane) :=
      (lintegral_fullSeedTrace N (strip.indicator F) (hF.indicator strip_measurable)).symm
    _ = _ := lintegral_indicator strip_measurable F

def parabolicNonnegativePoincare (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℝ≥0∞) : Gamma0OrbitSpace N → ℝ≥0∞ :=
  Function.extend (reducedProjection N)
    (fun z : reducedCarrier N => parabolicTraceNN N F z) (fun _ => 0)

theorem parabolicNonnegativePoincare_projection (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℝ≥0∞) (z : reducedCarrier N) :
    parabolicNonnegativePoincare N F (reducedProjection N z) = parabolicTraceNN N F z :=
  (reducedProjection_measurableEmbedding N).injective.extend_apply _ _ z

/-- Genuine actual quotient/parabolic-strip integral identity. -/
theorem nonnegative_parabolic_quotient_unfolding (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℝ≥0∞)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z) (hF : Measurable F) :
    (∫⁻ u, parabolicNonnegativePoincare N F u ∂carrierPushforward N) =
      ∫⁻ z in strip, F z := by
  calc
    _ = ∫⁻ z : reducedCarrier N, parabolicTraceNN N F z ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).lintegral_map]
      apply lintegral_congr
      intro z
      exact parabolicNonnegativePoincare_projection N F z
    _ = ∫⁻ z in reducedCarrier N, parabolicTraceNN N F z :=
      lintegral_subtype_comap (reducedCarrier_measurable N) _
    _ = _ := nonnegative_parabolic_carrier_unfolding N F hperiod hF

/-- The literal complex parabolic coset sum, rather than an H-L1 sum of F. -/
def parabolicTraceComplex (N : ℕ) (F : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) : ℂ :=
  ∑' q : GammaInfinityCosets N, F (parabolicRepresentative N q • z)

theorem parabolicTraceComplex_measurable (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : Measurable F) : Measurable (parabolicTraceComplex N F) := by
  letI : Countable (GammaInfinityCosets N) := inferInstance
  exact Measurable.tsum (fun q => hF.comp (parabolicAction_measurable N q))

/-- The true parabolic series is absolutely summable a.e. on the genuine
Gamma0 carrier, derived from STRIP-L1 of the periodic seed. -/
theorem parabolic_absolute_convergence_carrier (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z)
    (hF : Measurable F) (hstrip : IntegrableOn F strip) :
    ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)),
      Summable (fun q : GammaInfinityCosets N => ‖F (parabolicRepresentative N q • z)‖) := by
  letI : Countable (GammaInfinityCosets N) := inferInstance
  have hnormperiod : ∀ k : ℤ, ∀ z,
      ‖F (translate k z)‖ₑ = ‖F z‖ₑ := by intro k z; rw [hperiod]
  have hfinite :
      (∫⁻ z in reducedCarrier N, parabolicTraceNN N (fun z => ‖F z‖ₑ) z) ≠ ∞ := by
    rw [nonnegative_parabolic_carrier_unfolding N _ hnormperiod hF.enorm]
    exact hstrip.hasFiniteIntegral.ne
  have h := ae_lt_top' (parabolicTraceNN_measurable N (fun z => ‖F z‖ₑ)
    hF.enorm).aemeasurable hfinite
  filter_upwards [h] with z hz
  exact tsum_enorm_ne_top_iff_summable_norm.mp hz.ne

/-- The complex series itself is L1 on the actual carrier, as its norm
is bounded by the actual unfolded norm series. -/
theorem parabolicTraceComplex_integrableOn_carrier (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z)
    (hF : Measurable F) (hstrip : IntegrableOn F strip) :
    IntegrableOn (parabolicTraceComplex N F) (reducedCarrier N) := by
  refine ⟨(parabolicTraceComplex_measurable N F hF).aestronglyMeasurable, ?_⟩
  change (∫⁻ z in reducedCarrier N, ‖parabolicTraceComplex N F z‖ₑ) < ∞
  calc
    _ ≤ ∫⁻ z in reducedCarrier N, parabolicTraceNN N (fun z => ‖F z‖ₑ) z := by
      apply lintegral_mono
      intro z
      exact enorm_tsum_le_tsum_enorm
    _ = ∫⁻ z in strip, ‖F z‖ₑ :=
      nonnegative_parabolic_carrier_unfolding N _
        (fun k z => congrArg (fun c : ℂ => ‖c‖ₑ) (hperiod k z)) hF.enorm
    _ < ∞ := hstrip.hasFiniteIntegral

/-- Reindex of the actual complex effective trace at a point where its
summability holds. In the final theorem this premise is derived from the
strip-indicator seed's proved H-L1 norm partition. -/
private theorem complex_effective_trace_eq_parabolic (N : ℕ)
    (F : UpperHalfPlane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z) (z : UpperHalfPlane)
    (hs : Summable (fun e : effectiveGamma0 N =>
      strip.indicator F (effectiveMatrixAction N e z))) :
    complexSeedTrace N (strip.indicator F) z = parabolicTraceComplex N F z := by
  have hprod := (parabolicEffectiveEquiv N).summable_iff.mpr hs
  have hprod' : Summable (fun p : GammaInfinityCosets N × ℤ =>
      strip.indicator F (translate p.2 (parabolicRepresentative N p.1 • z))) := by
    apply hprod.congr
    rintro ⟨q, k⟩
    rw [parabolicPair_action]
  change (∑' e : effectiveGamma0 N,
      strip.indicator F (effectiveMatrixAction N e z)) = _
  calc
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        strip.indicator F (effectiveMatrixAction N (parabolicEffectiveEquiv N p) z) :=
      ((parabolicEffectiveEquiv N).tsum_eq _).symm
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        strip.indicator F (translate p.2 (parabolicRepresentative N p.1 • z)) := by
      apply tsum_congr
      rintro ⟨q, k⟩
      rw [parabolicPair_action]
    _ = ∑' q : GammaInfinityCosets N, ∑' k : ℤ,
        strip.indicator F (translate k (parabolicRepresentative N q • z)) := hprod'.tsum_prod
    _ = _ := by simp_rw [periodic_strip_indicator_tsum F hperiod]; rfl

/-- Actual complex parabolic unfolding; the seed is assumed L1 ONLY on
its true translation strip, not on H. -/
theorem complex_parabolic_carrier_unfolding (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z)
    (hF : Measurable F) (hstrip : IntegrableOn F strip) :
    (∫ z in reducedCarrier N, parabolicTraceComplex N F z) = ∫ z in strip, F z := by
  have h0 : Integrable (strip.indicator F) (volume : Measure UpperHalfPlane) :=
    (integrable_indicator_iff strip_measurable).mpr hstrip
  have hfull := absolute_convergence_carrier N (strip.indicator F) h0
  have heq : complexSeedTrace N (strip.indicator F) =ᵐ[
      (volume : Measure UpperHalfPlane).restrict (reducedCarrier N)] parabolicTraceComplex N F := by
    filter_upwards [hfull] with z hz
    exact complex_effective_trace_eq_parabolic N F hperiod z hz.of_norm
  calc
    _ = ∫ z in reducedCarrier N, complexSeedTrace N (strip.indicator F) z :=
      integral_congr_ae heq.symm
    _ = ∫ z, strip.indicator F z ∂(volume : Measure UpperHalfPlane) :=
      complex_carrier_unfolding N (strip.indicator F) h0
    _ = _ := integral_indicator strip_measurable

/-- The actual parabolic series on the true canonical Gamma0 quotient section. -/
def parabolicComplexPoincare (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ) : Gamma0OrbitSpace N → ℂ :=
  Function.extend (reducedProjection N)
    (fun z : reducedCarrier N => parabolicTraceComplex N F z) (fun _ => 0)

theorem parabolicComplexPoincare_projection (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ) (z : reducedCarrier N) :
    parabolicComplexPoincare N F (reducedProjection N z) = parabolicTraceComplex N F z :=
  (reducedProjection_measurableEmbedding N).injective.extend_apply _ _ z

theorem parabolicComplexPoincare_integrable (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z)
    (hF : Measurable F) (hstrip : IntegrableOn F strip) :
    Integrable (parabolicComplexPoincare N F) (carrierPushforward N) := by
  rw [← reducedProjection_map_measure N,
    (reducedProjection_measurableEmbedding N).integrable_map_iff]
  have hsub := (integrableOn_iff_comap_subtypeVal (reducedCarrier_measurable N)).mp
    (parabolicTraceComplex_integrableOn_carrier N F hperiod hF hstrip)
  have hcomp : parabolicComplexPoincare N F ∘ reducedProjection N =
      fun z : reducedCarrier N => parabolicTraceComplex N F z := by
    funext z
    exact parabolicComplexPoincare_projection N F z
  rw [hcomp]
  exact hsub

/-- Genuine GammaInfinity\Gamma0 complex L1 unfolding against the actual
canonical quotient measure, with all norm-convergence premises derived. -/
theorem complex_parabolic_quotient_unfolding (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z)
    (hF : Measurable F) (hstrip : IntegrableOn F strip) :
    (∫ u, parabolicComplexPoincare N F u ∂carrierPushforward N) = ∫ z in strip, F z := by
  calc
    _ = ∫ z : reducedCarrier N, parabolicTraceComplex N F z ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (parabolicComplexPoincare_projection N F)
    _ = ∫ z in reducedCarrier N, parabolicTraceComplex N F z :=
      integral_subtype_comap (reducedCarrier_measurable N) _
    _ = _ := complex_parabolic_carrier_unfolding N F hperiod hF hstrip

end
end ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
