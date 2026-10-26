import ImbalancedChen.Part3Gamma0NonnegativePoincareUnfolding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An actual measurable region in H on which the ACTUAL Gamma orbit map is
injective pushes canonical volume to the restriction of the original
quotient measure to its true 0/1 Poincare image. The original effective
Gamma tiling and reduced-carrier freeness prove multiplicity one; neither
a fundamental-domain nor quotient-density premise is supplied. This is
the measure primitive for genuine normalized high-cusp embeddings.
-/
namespace ImbalancedChen.Part3.GammaInjectiveRegionMeasure20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open Gamma0EffectiveActionKernel20261024z
open Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0NonnegativePoincareUnfolding20261025a
open Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a
open Gamma0QuotientCellPushforward20261025a

/-- The actual reduced carrier is free for effective labels; this is
deduced from the already proved disjoint actual carrier translates. -/
theorem effective_action_at_reduced_injective (N : ℕ) [NeZero N]
    {z : UpperHalfPlane} (hz : z ∈ reducedCarrier N) :
    Function.Injective (fun q : effectiveGamma0 N => effectiveMatrixAction N q z) := by
  intro q r hqr
  by_contra hne
  have hq : effectiveMatrixAction N q z ∈ effectiveCell N q := ⟨z, hz, rfl⟩
  have hr : effectiveMatrixAction N q z ∈ effectiveCell N r := ⟨z, hz, hqr.symm⟩
  exact (Set.disjoint_left.mp (effectiveCell_disjoint N hne)) hq hr

theorem injective_region_trace_zero_or_one (N : ℕ) [NeZero N]
    (A : Set UpperHalfPlane) (hAinj : Set.InjOn (orbitProjection N) A)
    {z : UpperHalfPlane} (hz : z ∈ reducedCarrier N) :
    fullSeedTrace N (A.indicator (fun _ => (1 : ℝ≥0∞))) z = 0 ∨
      fullSeedTrace N (A.indicator (fun _ => (1 : ℝ≥0∞))) z = 1 := by
  classical
  have huniq : ∀ q r : effectiveGamma0 N,
      effectiveMatrixAction N q z ∈ A → effectiveMatrixAction N r z ∈ A → q = r := by
    intro q r hq hr
    apply effective_action_at_reduced_injective N hz
    apply hAinj hq hr
    simp only [effectiveMatrixAction, orbitProjection_smul]
  by_cases hex : ∃ q : effectiveGamma0 N, effectiveMatrixAction N q z ∈ A
  · obtain ⟨q, hq⟩ := hex
    right
    rw [fullSeedTrace, tsum_eq_single q]
    · exact Set.indicator_of_mem hq _
    · intro r hr
      exact Set.indicator_of_notMem (fun hh => hr (huniq r q hh hq)) _
  · left
    apply tsum_eq_zero.mpr
    intro q
    exact Set.indicator_of_notMem (fun hq => hex ⟨q, hq⟩) _

def injectiveRegionIndicator (N : ℕ) [NeZero N] (A : Set UpperHalfPlane) :
    Gamma0OrbitSpace N → ℝ≥0∞ :=
  nonnegativePoincare N (A.indicator (fun _ => 1))

def quotientInjectiveRegion (N : ℕ) [NeZero N] (A : Set UpperHalfPlane) :
    Set (Gamma0OrbitSpace N) := {q | injectiveRegionIndicator N A q = 1}

theorem injectiveRegionIndicator_measurable (N : ℕ) [NeZero N]
    {A : Set UpperHalfPlane} (hA : MeasurableSet A) :
    Measurable (injectiveRegionIndicator N A) :=
  nonnegativePoincare_measurable N _ (measurable_const.indicator hA)

theorem quotientInjectiveRegion_measurable (N : ℕ) [NeZero N]
    {A : Set UpperHalfPlane} (hA : MeasurableSet A) :
    MeasurableSet (quotientInjectiveRegion N A) :=
  (injectiveRegionIndicator_measurable N hA) measurableSet_singleton

theorem injectiveRegionIndicator_zero_or_one (N : ℕ) [NeZero N]
    (A : Set UpperHalfPlane) (hAinj : Set.InjOn (orbitProjection N) A)
    (q : Gamma0OrbitSpace N) :
    injectiveRegionIndicator N A q = 0 ∨ injectiveRegionIndicator N A q = 1 := by
  by_cases hq : q ∈ Set.range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hq
    rw [injectiveRegionIndicator, nonnegativePoincare_projection]
    exact injective_region_trace_zero_or_one N A hAinj z.property
  · left
    exact Function.extend_apply' _ _ q hq

theorem injectiveRegionIndicator_eq_indicator (N : ℕ) [NeZero N]
    (A : Set UpperHalfPlane) (hAinj : Set.InjOn (orbitProjection N) A) :
    injectiveRegionIndicator N A = (quotientInjectiveRegion N A).indicator (fun _ => 1) := by
  funext q
  rcases injectiveRegionIndicator_zero_or_one N A hAinj q with hq | hq
  · simp [quotientInjectiveRegion, hq]
  · simp [quotientInjectiveRegion, hq]

theorem fullSeedTrace_quotient_weight (N : ℕ) (A : Set UpperHalfPlane)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) (z : UpperHalfPlane) :
    fullSeedTrace N (A.indicator (fun w => W (orbitProjection N w))) z =
      fullSeedTrace N (A.indicator (fun _ => 1)) z * W (orbitProjection N z) := by
  have heq : A.indicator (fun w => W (orbitProjection N w)) =
      fun w => A.indicator (fun _ => (1 : ℝ≥0∞)) w * W (orbitProjection N w) := by
    funext w
    by_cases hw : w ∈ A <;> simp [hw]
  rw [heq]
  unfold fullSeedTrace
  simp_rw [effectiveMatrixAction, orbitProjection_smul]
  exact ENNReal.tsum_mul_right

theorem injectiveRegion_quotient_weight_ae (N : ℕ) [NeZero N]
    (A : Set UpperHalfPlane) (W : Gamma0OrbitSpace N → ℝ≥0∞) :
    nonnegativePoincare N (A.indicator (fun w => W (orbitProjection N w))) =ᵐ[
      carrierPushforward N] (fun q => injectiveRegionIndicator N A q * W q) := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  rw [nonnegativePoincare_projection, fullSeedTrace_quotient_weight,
    injectiveRegionIndicator, nonnegativePoincare_projection]
  rfl

/-- Exact weighted geometric transport, with the original effective
center counted once and with no compactness/integrability restriction. -/
theorem quotient_injective_region_lintegral (N : ℕ) [NeZero N]
    {A : Set UpperHalfPlane} (hA : MeasurableSet A)
    (hAinj : Set.InjOn (orbitProjection N) A)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ q in quotientInjectiveRegion N A, W q ∂carrierPushforward N) =
      ∫⁻ z in A, W (orbitProjection N z) := by
  calc
    _ = ∫⁻ q, injectiveRegionIndicator N A q * W q ∂carrierPushforward N := by
      rw [injectiveRegionIndicator_eq_indicator N A hAinj,
        ← lintegral_indicator (quotientInjectiveRegion_measurable N hA)]
      apply lintegral_congr
      intro q
      by_cases hq : q ∈ quotientInjectiveRegion N A <;> simp [hq]
    _ = ∫⁻ q, nonnegativePoincare N (A.indicator (fun z => W (orbitProjection N z))) q
        ∂carrierPushforward N :=
      lintegral_congr_ae (injectiveRegion_quotient_weight_ae N A W).symm
    _ = ∫⁻ z, A.indicator (fun z => W (orbitProjection N z)) z :=
      nonnegative_poincare_unfolding N _
        ((hW.comp (orbitProjection_measurable N)).indicator hA)
    _ = _ := lintegral_indicator hA _

/-- An actual orbit-injective spatial chart has multiplicity exactly
one as a pushforward measure on the genuine quotient. -/
theorem quotient_injective_region_map_measure (N : ℕ) [NeZero N]
    {A : Set UpperHalfPlane} (hA : MeasurableSet A)
    (hAinj : Set.InjOn (orbitProjection N) A) :
    ((volume : Measure UpperHalfPlane).restrict A).map (orbitProjection N) =
      (carrierPushforward N).restrict (quotientInjectiveRegion N A) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (orbitProjection_measurable N) hS]
  have h := quotient_injective_region_lintegral N hA hAinj
    (S.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hS)
  have hi : (fun z : UpperHalfPlane => S.indicator (fun _ => (1 : ℝ≥0∞)) (orbitProjection N z)) =
      (orbitProjection N ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    rfl
  rw [hi, lintegral_indicator hS,
    lintegral_indicator ((orbitProjection_measurable N) hS)] at h
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using h.symm

end
end ImbalancedChen.Part3.GammaInjectiveRegionMeasure20261026b
