import ImbalancedChen.Part3Gamma0ActualParabolicUnfolding
import ImbalancedChen.Part3ActualInfinityKloostermanSeed
import ImbalancedChen.Part3Gamma0CompactSeedSharpL2Budget
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

For the literal periodic cusp seed e(m*x)*psi(y), continuous compact
positive-height radial support gives a bounded measurable compactly
supported STRIP INDICATOR seed on H. The indicator may jump at the vertical
strip edges; no continuity of that H seed is used. Actual global compact
transporter overlap proves its effective Poincare sum uniformly bounded.
The true parabolic/effective reindex identifies the actual parabolic
quotient series with that compact-indicator series, proving MemLp2.
The sharp canonical square-mass budget is the actual compact-overlap
constant times the strip radial square mass. Neither L2 nor absolute
convergence nor periodic-seed H-L1 is a hypothesis.
-/

namespace ImbalancedChen.Part3.CompactCuspParabolicL220261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise ENNReal
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedSharpL2Budget20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a

/-- The genuine nonperiodic H seed, with the exact half-open strip cutoff. -/
def cuspStripSeed (m : ℤ) (ψ : ℝ → ℂ) : UpperHalfPlane → ℂ :=
  strip.indicator (fourierRadialSeed m ψ)

/-- A CLOSED support container for the discontinuous strip indicator. -/
def cuspSupportK (ψ : ℝ → ℂ) : Set UpperHalfPlane :=
  {z | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ tsupport ψ}

theorem cuspSupportK_isCompact (ψ : ℝ → ℂ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) : IsCompact (cuspSupportK ψ) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  have heq : ((↑) : UpperHalfPlane → ℂ) '' cuspSupportK ψ =
      (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) '' (Icc (0 : ℝ) 1 ×ˢ tsupport ψ) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(z.re, z.im), hz, ?_⟩
      ext <;> rfl
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨⟨p.1, p.2⟩, hpos hp.2⟩, hp, rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod hc).image (by fun_prop)

theorem fourierRadialSeed_continuous (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Continuous (fourierRadialSeed m ψ) := by
  have hcircle : Continuous (fun x : ℝ => (x : UnitAddCircle)) := AddCircle.continuous_mk'
  exact (((AddCircle.fourier m).continuous.comp
    (hcircle.comp UpperHalfPlane.continuous_re)).mul (hψ.comp UpperHalfPlane.continuous_im))

theorem fourierRadialSeed_measurable (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Measurable (fourierRadialSeed m ψ) := (fourierRadialSeed_continuous m ψ hψ).measurable

@[simp] theorem fourierRadialSeed_norm (m : ℤ) (ψ : ℝ → ℂ) (z : UpperHalfPlane) :
    ‖fourierRadialSeed m ψ z‖ = ‖ψ z.im‖ := by
  simp only [fourierRadialSeed, norm_mul, AddCircle.fourier_apply, Circle.norm_coe, one_mul]

theorem fourierRadialSeed_periodic (m : ℤ) (ψ : ℝ → ℂ) :
    ∀ k : ℤ, ∀ z : UpperHalfPlane,
      fourierRadialSeed m ψ (translate k z) = fourierRadialSeed m ψ z := by
  intro k z
  have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
    AddCircle.coe_eq_zero_iff.mpr ⟨k, by simp [zsmul_eq_mul]⟩
  rw [translate_eq_vadd, fourierRadialSeed_translate, hk]
  simp

theorem cuspStripSeed_measurable (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Measurable (cuspStripSeed m ψ) :=
  (fourierRadialSeed_measurable m ψ hψ).indicator strip_measurable

theorem cuspStripSeed_support_subset (m : ℤ) (ψ : ℝ → ℂ) :
    Function.support (cuspStripSeed m ψ) ⊆ cuspSupportK ψ := by
  intro z hz
  have hs : z ∈ strip := by
    by_contra hnot
    exact hz (by simp [cuspStripSeed, hnot])
  refine ⟨⟨hs.1, hs.2.le⟩, ?_⟩
  by_contra hnot
  have hzero : ψ z.im = 0 := image_eq_zero_of_notMem_tsupport hnot
  exact hz (by simp [cuspStripSeed, hs, fourierRadialSeed, hzero])

/-- The discontinuous H seed is locally integrable as a measurable
indicator of a continuous function, and its true support is compact. -/
theorem cuspStripSeed_integrable (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Integrable (cuspStripSeed m ψ) (volume : Measure UpperHalfPlane) := by
  have hlocal : LocallyIntegrable (cuspStripSeed m ψ) (volume : Measure UpperHalfPlane) :=
    (fourierRadialSeed_continuous m ψ hψ).locallyIntegrable.indicator strip_measurable
  exact (integrableOn_iff_integrable_of_support_subset
    (cuspStripSeed_support_subset m ψ)).mp
      (hlocal.integrableOn_isCompact (cuspSupportK_isCompact ψ hc hpos))

/-- The periodic cusp seed needs ONLY strip L1; it is not H-L1. -/
theorem fourierRadialSeed_integrableOn_strip (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (fourierRadialSeed m ψ) strip :=
  (integrable_indicator_iff strip_measurable).mp (cuspStripSeed_integrable m ψ hψ hc hpos)

/-- An actual global seed bound derived from the radial compact support. -/
theorem cuspStripSeed_bound (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖cuspStripSeed m ψ z‖ ≤ B := by
  obtain ⟨b, hb⟩ := hc.bddAbove_image hψ.norm.continuousOn
  refine ⟨max b 0, le_max_right b 0, ?_⟩
  intro z
  by_cases hs : z ∈ strip
  · rw [cuspStripSeed, indicator_of_mem hs, fourierRadialSeed_norm]
    by_cases hy : z.im ∈ tsupport ψ
    · exact (hb ⟨z.im, hy, rfl⟩).trans (le_max_left b 0)
    · simpa only [image_eq_zero_of_notMem_tsupport hy, norm_zero] using le_max_right b 0
  · simpa [cuspStripSeed, hs] using le_max_right b 0

private theorem bounded_measurable_compact_seed_memLp_two (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) (hf : Integrable f (volume : Measure UpperHalfPlane))
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖f z‖ ≤ B) :
    MemLp (complexPoincare N f) 2 (carrierPushforward N) := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  obtain ⟨M, _hM, hfinite⟩ := compact_seed_uniform_finite_support N f hK hsupp
  have htrace : ∀ z, ‖complexSeedTrace N f z‖ ≤ (M : ℝ) * B := by
    intro z
    obtain ⟨S, hcard, hzero⟩ := hfinite z
    calc
      _ = ‖∑ q ∈ S, f (effectiveMatrixAction N q z)‖ := congrArg norm (tsum_eq_sum hzero)
      _ ≤ ∑ q ∈ S, ‖f (effectiveMatrixAction N q z)‖ := norm_sum_le _ _
      _ ≤ ∑ _q ∈ S, B := Finset.sum_le_sum (fun q _ => hb _)
      _ = (S.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  apply MemLp.of_bound (complexPoincare_integrable N f hf).aestronglyMeasurable ((M : ℝ) * B)
  apply Filter.Eventually.of_forall
  intro u
  by_cases hu : u ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hu
    rw [complexPoincare_projection]
    exact htrace z
  · have hz : ∀ q : effectiveGamma0 N, quotientSeedTerm N f q u = 0 := by
      intro q
      exact Function.extend_apply' _ _ u hu
    simp only [complexPoincare, hz, tsum_zero, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hB

/-- Compact support makes the actual effective strip-indicator series
summable at EVERY point, licensing the true complex parabolic reindex. -/
private theorem compact_cusp_trace_reindex (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    complexSeedTrace N (cuspStripSeed m ψ) z = parabolicTraceComplex N (fourierRadialSeed m ψ) z := by
  obtain ⟨M, hM, hfinite⟩ := compact_seed_uniform_finite_support N (cuspStripSeed m ψ)
    (cuspSupportK_isCompact ψ hc hpos) (cuspStripSeed_support_subset m ψ)
  obtain ⟨S, _hcard, hzero⟩ := hfinite z
  have hs : Summable (fun e : effectiveGamma0 N => cuspStripSeed m ψ (effectiveMatrixAction N e z)) :=
    summable_of_ne_finset_zero (s := S) hzero
  have hprod := (parabolicEffectiveEquiv N).summable_iff.mpr hs
  have hprod' : Summable (fun p : GammaInfinityCosets N × ℤ =>
      strip.indicator (fourierRadialSeed m ψ)
        (translate p.2 (parabolicRepresentative N p.1 • z))) := by
    apply hprod.congr
    rintro ⟨q, k⟩
    exact congrArg (cuspStripSeed m ψ) (parabolicPair_action N q k z)
  change (∑' e : effectiveGamma0 N, cuspStripSeed m ψ (effectiveMatrixAction N e z)) = _
  calc
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        cuspStripSeed m ψ (effectiveMatrixAction N (parabolicEffectiveEquiv N p) z) :=
      ((parabolicEffectiveEquiv N).tsum_eq _).symm
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        strip.indicator (fourierRadialSeed m ψ)
          (translate p.2 (parabolicRepresentative N p.1 • z)) := by
      apply tsum_congr
      rintro ⟨q, k⟩
      exact congrArg (cuspStripSeed m ψ) (parabolicPair_action N q k z)
    _ = ∑' q : GammaInfinityCosets N, ∑' k : ℤ,
        strip.indicator (fourierRadialSeed m ψ) (translate k (parabolicRepresentative N q • z)) :=
      hprod'.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro q
      exact periodic_strip_indicator_tsum _ (fourierRadialSeed_periodic m ψ) _

/-- The actual parabolic quotient series equals the full effective series
of the COMPACT STRIP INDICATOR seed, with all convergence proved. -/
theorem compactCusp_quotient_eq_full (N : ℕ) [NeZero N] (m : ℤ) (ψ : ℝ → ℂ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    parabolicComplexPoincare N (fourierRadialSeed m ψ) = complexPoincare N (cuspStripSeed m ψ) := by
  funext u
  by_cases hu : u ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hu
    rw [parabolicComplexPoincare_projection, complexPoincare_projection]
    exact (compact_cusp_trace_reindex N m ψ hc hpos z).symm
  · have hleft : parabolicComplexPoincare N (fourierRadialSeed m ψ) u = 0 :=
      Function.extend_apply' _ _ u hu
    have hterms : ∀ q : effectiveGamma0 N, quotientSeedTerm N (cuspStripSeed m ψ) q u = 0 := by
      intro q
      exact Function.extend_apply' _ _ u hu
    rw [hleft]
    simp only [complexPoincare, hterms, tsum_zero]

/-- Actual parabolic cusp Poincare L2, with no hL2 or hAbsSum premise. -/
theorem compactCuspPoincare_memLp_two (N : ℕ) [NeZero N] (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    MemLp (parabolicComplexPoincare N (fourierRadialSeed m ψ)) 2 (carrierPushforward N) := by
  rw [compactCusp_quotient_eq_full N m ψ hc hpos]
  obtain ⟨B, hB, hb⟩ := cuspStripSeed_bound m ψ hψ hc
  exact bounded_measurable_compact_seed_memLp_two N _ (cuspStripSeed_integrable m ψ hψ hc hpos)
    (cuspSupportK_isCompact ψ hc hpos) (cuspStripSeed_support_subset m ψ) B hB hb

private theorem cuspStripSeed_squareMass_eq (m : ℤ) (ψ : ℝ → ℂ) :
    seedSquareMass (cuspStripSeed m ψ) =
      strip.indicator (fun z : UpperHalfPlane => ENNReal.ofReal (‖ψ z.im‖ ^ 2)) := by
  funext z
  by_cases hs : z ∈ strip <;> simp [seedSquareMass, cuspStripSeed, hs, fourierRadialSeed_norm]

/-- The radial strip square mass is finite from the actual compact support
and derived bound, so the quantitative budget has a finite RHS. -/
theorem compactCusp_radial_squareMass_finite (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    (∫⁻ z in strip, ENNReal.ofReal (‖ψ z.im‖ ^ 2)) < ∞ := by
  obtain ⟨B, hB, hb⟩ := cuspStripSeed_bound m ψ hψ hc
  have hK := cuspSupportK_isCompact ψ hc hpos
  have hsquare : seedSquareMass (cuspStripSeed m ψ) =
      (cuspSupportK ψ).indicator (seedSquareMass (cuspStripSeed m ψ)) := by
    funext z
    by_cases hz : z ∈ cuspSupportK ψ
    · simp only [indicator_of_mem hz]
    · have hzero : cuspStripSeed m ψ z = 0 := by
        by_contra hn
        exact hz (cuspStripSeed_support_subset m ψ hn)
      simp only [indicator_of_notMem hz, seedSquareMass, hzero, norm_zero,
        zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
  calc
    _ = ∫⁻ z, seedSquareMass (cuspStripSeed m ψ) z ∂(volume : Measure UpperHalfPlane) := by
      rw [cuspStripSeed_squareMass_eq, lintegral_indicator strip_measurable]
    _ = ∫⁻ z in cuspSupportK ψ, seedSquareMass (cuspStripSeed m ψ) z := by
      rw [hsquare, lintegral_indicator hK.measurableSet]
    _ ≤ ∫⁻ _z in cuspSupportK ψ, ENNReal.ofReal (B ^ 2) := by
      apply lintegral_mono
      intro z
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hb z) 2)
    _ = ENNReal.ofReal (B ^ 2) * (volume : Measure UpperHalfPlane) (cuspSupportK ψ) := by
      simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
/-- The actual sharp finite-overlap squared-norm budget. Its RHS is the
true strip radial mass, with no factor from duplicate scalar matrices. -/
theorem compactCuspPoincare_squareMass_budget (N : ℕ) [NeZero N]
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    (∫⁻ u, ENNReal.ofReal (‖parabolicComplexPoincare N (fourierRadialSeed m ψ) u‖ ^ 2)
        ∂carrierPushforward N) ≤
      ENNReal.ofReal (compactOverlapBound N (cuspSupportK ψ) : ℝ) *
        ∫⁻ z in strip, ENNReal.ofReal (‖ψ z.im‖ ^ 2) := by
  rw [compactCusp_quotient_eq_full N m ψ hc hpos]
  have h := compactSeed_quotient_squareMass_budget N (cuspStripSeed m ψ)
    (cuspStripSeed_measurable m ψ hψ) (cuspSupportK_isCompact ψ hc hpos)
    (cuspStripSeed_support_subset m ψ)
  rw [cuspStripSeed_squareMass_eq, lintegral_indicator strip_measurable] at h
  exact h

def compactCuspPoincareL2 (N : ℕ) [NeZero N] (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Lp ℂ 2 (carrierPushforward N) :=
  (compactCuspPoincare_memLp_two N m ψ hψ hc hpos).toLp
    (parabolicComplexPoincare N (fourierRadialSeed m ψ))

end
end ImbalancedChen.Part3.CompactCuspParabolicL220261025a

