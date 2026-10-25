import ImbalancedChen.Part3GammaInfinityTranslationStrip
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Exact nonnegative and complex L1 integer periodization unfolding on the
TRUE half-open translation strip. The actual strip cells tile H disjointly
and preserve the canonical hyperbolic volume, as proved in the imported
module. The norm-mass partition proves the Bochner interchange condition
and a.e. absolute convergence, rather than assuming hAbsSum.

The quotient is the ACTUAL GammaInfinity(N) orbit quotient on H, with
central +/- translations counted once. The L1 input in the periodization
theorem is the original nonperiodic H seed; a periodic cusp seed is only
required strip-integrable by the preceding periodicLift theorem. No
GammaInfinity\Gamma0 automorphic unfolding is claimed here.
-/

namespace ImbalancedChen.Part3.GammaInfinityStripPeriodization20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a

/-- Canonical change of variables on one actual integer strip cell. -/
theorem lintegral_stripCell (k : ℤ) (f : UpperHalfPlane → ℝ≥0∞) :
    (∫⁻ z in stripCell k, f z) = ∫⁻ z in strip, f (translate k z) :=
  ((translate_measurePreserving k).setLIntegral_comp_emb
    (translate_measurableEmbedding k) f strip).symm

def nonnegativePeriodization (f : UpperHalfPlane → ℝ≥0∞)
    (z : UpperHalfPlane) : ℝ≥0∞ := ∑' k : ℤ, f (translate k z)

theorem nonnegativePeriodization_measurable (f : UpperHalfPlane → ℝ≥0∞)
    (hf : Measurable f) : Measurable (nonnegativePeriodization f) :=
  Measurable.tsum (fun k => hf.comp (translate_measurePreserving k).measurable)

theorem nonnegativePeriodization_periodic (f : UpperHalfPlane → ℝ≥0∞)
    (j : ℤ) (z : UpperHalfPlane) :
    nonnegativePeriodization f (translate j z) = nonnegativePeriodization f z := by
  unfold nonnegativePeriodization
  calc
    _ = ∑' k : ℤ, f (translate (k + j) z) := by
      apply tsum_congr
      intro k
      rw [translate_add]
    _ = _ := (Equiv.addRight j).tsum_eq _

/-- Positive strip unfolding uses a proved all-H tiling, without a
finiteness, convergence or supplied fundamental-domain premise. -/
theorem nonnegative_strip_unfolding (f : UpperHalfPlane → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z in strip, nonnegativePeriodization f z) =
      ∫⁻ z, f z ∂(volume : Measure UpperHalfPlane) := by
  calc
    _ = ∑' k : ℤ, ∫⁻ z in strip, f (translate k z) :=
      lintegral_tsum (fun k => (hf.comp (translate_measurePreserving k).measurable).aemeasurable)
    _ = ∑' k : ℤ, ∫⁻ z in stripCell k, f z := by
      apply tsum_congr
      intro k
      exact (lintegral_stripCell k f).symm
    _ = ∫⁻ z in ⋃ k : ℤ, stripCell k, f z :=
      (lintegral_iUnion stripCell_measurable stripCell_pairwise_disjoint f).symm
    _ = _ := by rw [iUnion_stripCell, Measure.restrict_univ]

/-- Nonnegative periodization as an actual function on the parabolic orbit space. -/
def quotientNonnegativePeriodization (N : ℕ) (f : UpperHalfPlane → ℝ≥0∞) :
    InfinityOrbitSpace N → ℝ≥0∞ :=
  periodicLift N (nonnegativePeriodization f) (nonnegativePeriodization_periodic f)

theorem nonnegative_quotient_unfolding (N : ℕ) (f : UpperHalfPlane → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ q, quotientNonnegativePeriodization N f q ∂infinityQuotientMeasure N) =
      ∫⁻ z, f z ∂(volume : Measure UpperHalfPlane) :=
  (lintegral_periodicLift N (nonnegativePeriodization f)
    (nonnegativePeriodization_periodic f) (nonnegativePeriodization_measurable f hf)).trans
      (nonnegative_strip_unfolding f hf)

/-- Exact absolute mass partition, valid before imposing an L1 assumption. -/
theorem translated_seed_norm_mass (f : UpperHalfPlane → ℂ) :
    (∑' k : ℤ, ∫⁻ z in strip, ‖f (translate k z)‖ₑ) =
      ∫⁻ z, ‖f z‖ₑ ∂(volume : Measure UpperHalfPlane) := by
  calc
    _ = ∑' k : ℤ, ∫⁻ z in stripCell k, ‖f z‖ₑ := by
      apply tsum_congr
      intro k
      exact (lintegral_stripCell k (fun z => ‖f z‖ₑ)).symm
    _ = ∫⁻ z in ⋃ k : ℤ, stripCell k, ‖f z‖ₑ :=
      (lintegral_iUnion stripCell_measurable stripCell_pairwise_disjoint _).symm
    _ = _ := by rw [iUnion_stripCell, Measure.restrict_univ]

private theorem translated_seed_aestronglyMeasurable (f : UpperHalfPlane → ℂ)
    (hf : Integrable f (volume : Measure UpperHalfPlane)) (k : ℤ) :
    AEStronglyMeasurable (fun z => f (translate k z))
      ((volume : Measure UpperHalfPlane).restrict strip) :=
  (hf.aestronglyMeasurable.comp_measurePreserving (translate_measurePreserving k)).restrict

/-- Absolute convergence a.e. on the true strip is proved from the actual
norm-mass identity and original seed integrability. -/
theorem complex_periodization_absolute_ae (f : UpperHalfPlane → ℂ)
    (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict strip),
      Summable (fun k : ℤ => ‖f (translate k z)‖) := by
  have hm (k : ℤ) : AEMeasurable (fun z => ‖f (translate k z)‖ₑ)
      ((volume : Measure UpperHalfPlane).restrict strip) :=
    (translated_seed_aestronglyMeasurable f hf k).enorm
  have hfinite : (∫⁻ z in strip, ∑' k : ℤ, ‖f (translate k z)‖ₑ) ≠ ∞ := by
    rw [lintegral_tsum hm, translated_seed_norm_mass]
    exact hf.hasFiniteIntegral.ne
  have h := ae_lt_top' (AEMeasurable.tsum hm) hfinite
  filter_upwards [h] with z hz
  exact tsum_enorm_ne_top_iff_summable_norm.mp hz.ne

def complexPeriodization (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' k : ℤ, f (translate k z)

theorem complexPeriodization_measurable (f : UpperHalfPlane → ℂ) (hf : Measurable f) :
    Measurable (complexPeriodization f) :=
  Measurable.tsum (fun k => hf.comp (translate_measurePreserving k).measurable)

theorem complexPeriodization_periodic (f : UpperHalfPlane → ℂ)
    (j : ℤ) (z : UpperHalfPlane) :
    complexPeriodization f (translate j z) = complexPeriodization f z := by
  unfold complexPeriodization
  calc
    _ = ∑' k : ℤ, f (translate (k + j) z) := by
      apply tsum_congr
      intro k
      rw [translate_add]
    _ = _ := (Equiv.addRight j).tsum_eq _

/-- The actual complex periodized function is integrable on the strip;
its Bochner unfolding cannot be an identity of divergent default zeros. -/
theorem complexPeriodization_integrableOn_strip (f : UpperHalfPlane → ℂ)
    (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    IntegrableOn (complexPeriodization f) strip := by
  have hm := translated_seed_aestronglyMeasurable f hf
  refine ⟨(AEMeasurable.tsum (fun k => (hm k).aemeasurable)).aestronglyMeasurable, ?_⟩
  change (∫⁻ z in strip, ‖complexPeriodization f z‖ₑ) < ∞
  calc
    _ ≤ ∫⁻ z in strip, ∑' k : ℤ, ‖f (translate k z)‖ₑ := by
      apply lintegral_mono
      intro z
      exact enorm_tsum_le_tsum_enorm
    _ = ∑' k : ℤ, ∫⁻ z in strip, ‖f (translate k z)‖ₑ :=
      lintegral_tsum (fun k => (hm k).enorm)
    _ = ∫⁻ z, ‖f z‖ₑ ∂(volume : Measure UpperHalfPlane) := translated_seed_norm_mass f
    _ < ∞ := hf.hasFiniteIntegral

private theorem integral_stripCell (k : ℤ) (f : UpperHalfPlane → ℂ) :
    (∫ z in stripCell k, f z) = ∫ z in strip, f (translate k z) := by
  have h := (translate_measurableEmbedding k).setIntegral_map
    (μ := (volume : Measure UpperHalfPlane)) f (translate k '' strip)
  rw [(translate_measurePreserving k).map_eq] at h
  simpa only [Set.preimage_image_eq _ (translate_measurableEmbedding k).injective] using h

/-- Complex L1 periodization unfolding, with the required norm-integral
sum proved by canonical strip partition rather than assumed. -/
theorem complex_strip_unfolding (f : UpperHalfPlane → ℂ)
    (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    (∫ z in strip, complexPeriodization f z) =
      ∫ z, f z ∂(volume : Measure UpperHalfPlane) := by
  have hfinite : (∑' k : ℤ, ∫⁻ z in strip, ‖f (translate k z)‖ₑ) ≠ ∞ := by
    rw [translated_seed_norm_mass]
    exact hf.hasFiniteIntegral.ne
  calc
    _ = ∑' k : ℤ, ∫ z in strip, f (translate k z) :=
      integral_tsum (translated_seed_aestronglyMeasurable f hf) hfinite
    _ = ∑' k : ℤ, ∫ z in stripCell k, f z := by
      apply tsum_congr
      intro k
      exact (integral_stripCell k f).symm
    _ = ∫ z in ⋃ k : ℤ, stripCell k, f z :=
      (integral_iUnion stripCell_measurable stripCell_pairwise_disjoint hf.integrableOn).symm
    _ = _ := by rw [iUnion_stripCell, Measure.restrict_univ]

def quotientComplexPeriodization (N : ℕ) (f : UpperHalfPlane → ℂ) :
    InfinityOrbitSpace N → ℂ :=
  periodicLift N (complexPeriodization f) (complexPeriodization_periodic f)

/-- The actual parabolic quotient periodization is genuinely L1. -/
theorem quotientComplexPeriodization_integrable (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hm : Measurable f) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    Integrable (quotientComplexPeriodization N f) (infinityQuotientMeasure N) :=
  periodicLift_integrable N (complexPeriodization f) (complexPeriodization_periodic f)
    (complexPeriodization_measurable f hm) (complexPeriodization_integrableOn_strip f hf)

/-- Full complex L1 integer-strip periodization on the genuine GammaInfinity
orbit quotient. This does not assume a periodic cusp seed to be L1(H). -/
theorem complex_quotient_unfolding (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hm : Measurable f) (hf : Integrable f (volume : Measure UpperHalfPlane)) :
    (∫ q, quotientComplexPeriodization N f q ∂infinityQuotientMeasure N) =
      ∫ z, f z ∂(volume : Measure UpperHalfPlane) :=
  (integral_periodicLift N (complexPeriodization f) (complexPeriodization_periodic f)
    (complexPeriodization_measurable f hm) (complexPeriodization_integrableOn_strip f hf)).trans
      (complex_strip_unfolding f hf)

end
end ImbalancedChen.Part3.GammaInfinityStripPeriodization20261025a
