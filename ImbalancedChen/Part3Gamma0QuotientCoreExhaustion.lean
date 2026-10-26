import ImbalancedChen.Part3Gamma0CompletedFormFixedCoreRellich
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal actual finite-class quotient cores are monotone and exhaust
the genuine reduced carrier and hence almost every original quotient
point. Restrictions of EVERY actual quotient L2 vector converge strongly
to that vector. The squared truncation error is exactly its integral over
the literal quotient-core complement. No cusp decomposition or uniform
energy-family tail bound is used or inferred from this pointwise result.
-/

namespace ImbalancedChen.Part3.Gamma0QuotientCoreExhaustion20261026b
noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped UpperHalfPlane
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0FiniteChartReconstruction20261026b
open Gamma0QuotientChartReconstruction20261026b
open Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0CompletedFormFixedCoreRellich20261026b

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

theorem core_mono (N : ℕ) [NeZero N] : Monotone (core N) := by
  intro Y Z hYZ z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨i, hi.1, hi.2.trans hYZ⟩

theorem quotientCore_mono (N : ℕ) [NeZero N] : Monotone (quotientCore N) := by
  intro Y Z hYZ q hq
  obtain ⟨z, hz, rfl⟩ := hq
  exact ⟨z, core_mono N hYZ hz, rfl⟩

/-- Each actual finite carrier chart has a finite actual coordinate
height. All finite-class covering data come from the original carrier. -/
theorem eventually_core_of_carrier (N : ℕ) [NeZero N]
    {z : UpperHalfPlane} (hz : z ∈ gamma0Carrier N) :
    ∀ᶠ Y : ℝ in atTop, z ∈ core N Y := by
  obtain ⟨q, hq⟩ := mem_iUnion.mp hz
  rw [mem_smul_set_iff_inv_smul_mem] at hq
  let i : ChartIndex N := Fintype.equivFin (gamma0Classes N) q
  have hi : chartClass N i = q := (Fintype.equivFin (gamma0Classes N)).symm_apply_apply q
  have hfd : chartCoordinate N i z ∈
      ModularFundamentalFiniteMeasure20261024z.modularFD := by
    simpa only [chartCoordinate, chartMatrix, hi] using hq
  filter_upwards [eventually_ge_atTop (chartCoordinate N i z).im] with Y hY
  exact mem_iUnion.mpr ⟨i, hfd, hY⟩

theorem core_iUnion_eq_carrier (N : ℕ) [NeZero N] :
    (⋃ Y : ℝ, core N Y) = gamma0Carrier N := by
  apply Subset.antisymm
  · exact iUnion_subset (fun Y => core_subset_carrier N Y)
  · intro z hz
    obtain ⟨Y, hY⟩ := (eventually_core_of_carrier N hz).exists
    exact mem_iUnion.mpr ⟨Y, hY⟩

theorem quotientCore_iUnion_eq_reduced_range (N : ℕ) [NeZero N] :
    (⋃ Y : ℝ, quotientCore N Y) = range (reducedProjection N) := by
  apply Subset.antisymm
  · rintro q ⟨Y, z, hz, rfl⟩
    exact ⟨z, rfl⟩
  · rintro q ⟨z, rfl⟩
    obtain ⟨Y, hY⟩ := (eventually_core_of_carrier N z.property.1).exists
    exact mem_iUnion.mpr ⟨Y, z, hY, rfl⟩

/-- The exceptional quotient points are exactly handled by the proved
conull reduced-carrier image; no globally chosen orbit height is assumed. -/
theorem quotientCore_eventually_mem_ae (N : ℕ) [NeZero N] :
    ∀ᵐ q ∂carrierPushforward N, ∀ᶠ Y : ℝ in atTop, q ∈ quotientCore N Y := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  exact (eventually_core_of_carrier N z.property.1).mono
    (fun Y hY => ⟨z, hY, rfl⟩)

/-- An exact identity in the original quotient L2 norm and measure. -/
theorem restriction_error_square (N : ℕ) [NeZero N] (Y : ℝ) (u : QuotientL2 N) :
    ‖u-quotientCoreRestriction N Y u‖^2 =
      ∫ q in (quotientCore N Y)ᶜ, ‖u q‖^2 ∂carrierPushforward N := by
  have hsquare : ‖u-quotientCoreRestriction N Y u‖^2 =
      ∫ q, ‖(u-quotientCoreRestriction N Y u) q‖^2 ∂carrierPushforward N := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner (u-quotientCoreRestriction N Y u)
        (u-quotientCoreRestriction N Y u))]
    apply integral_congr_ae
    exact Eventually.of_forall (fun q => by
      simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_re])
  rw [hsquare, ← integral_indicator (quotientCore_measurable N Y).compl]
  apply integral_congr_ae
  filter_upwards [quotientCoreRestriction_coe_ae N Y u,
    Lp.coeFn_sub u (quotientCoreRestriction N Y u)] with q hres hsub
  rw [hsub, hres]
  by_cases hq : q ∈ quotientCore N Y <;> simp [hq]

/-- Literal quotient-complement integrals vanish for each fixed L2
vector. This is NOT uniform tail tightness of an energy-bounded family. -/
theorem quotient_complement_integral_tendsto_zero (N : ℕ) [NeZero N]
    (u : QuotientL2 N) :
    Tendsto (fun Y : ℝ => ∫ q in (quotientCore N Y)ᶜ, ‖u q‖^2
      ∂carrierPushforward N) atTop (𝓝 0) := by
  let b : Gamma0OrbitSpace N → ℝ := fun q => ‖u q‖^2
  let E : ℝ → Gamma0OrbitSpace N → ℝ := fun Y => ((quotientCore N Y)ᶜ).indicator b
  have hb : Integrable b (carrierPushforward N) :=
    (memLp_two_iff_integrable_sq_norm u.memLp.aestronglyMeasurable).mp u.memLp
  have hmeas : ∀ Y : ℝ, AEStronglyMeasurable (E Y) (carrierPushforward N) :=
    fun Y => hb.aestronglyMeasurable.indicator (quotientCore_measurable N Y).compl
  have hbound : ∀ Y : ℝ, ∀ᵐ q ∂carrierPushforward N, ‖E Y q‖ ≤ b q := by
    intro Y
    exact Eventually.of_forall (fun q => by
      by_cases hq : q ∈ quotientCore N Y <;>
        simp [E, b, hq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖u q‖)])
  have hlim : ∀ᵐ q ∂carrierPushforward N,
      Tendsto (fun Y : ℝ => E Y q) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [quotientCore_eventually_mem_ae N] with q hq
    exact tendsto_const_nhds.congr' (hq.mono (fun Y hY => by simp [E, hY]))
  have h := tendsto_integral_filter_of_dominated_convergence b
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hb hlim
  simpa only [E, integral_indicator (quotientCore_measurable N _).compl,
    integral_zero] using h

theorem quotientCoreRestriction_norm_error_tendsto_zero (N : ℕ) [NeZero N]
    (u : QuotientL2 N) :
    Tendsto (fun Y : ℝ => ‖u-quotientCoreRestriction N Y u‖) atTop (𝓝 0) := by
  have hs : Tendsto (fun Y : ℝ => ‖u-quotientCoreRestriction N Y u‖^2) atTop (𝓝 0) := by
    simpa only [restriction_error_square] using quotient_complement_integral_tendsto_zero N u
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

/-- Strong convergence on the original quotient Hilbert space. -/
theorem quotientCoreRestriction_tendsto_identity (N : ℕ) [NeZero N]
    (u : QuotientL2 N) :
    Tendsto (fun Y : ℝ => quotientCoreRestriction N Y u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨Y, hY⟩ := Metric.tendsto_atTop.mp
    (quotientCoreRestriction_norm_error_tendsto_zero N u) ε hε
  refine ⟨Y, fun Z hZ => ?_⟩
  have h := hY Z hZ
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    dist_eq_norm, norm_sub_rev] using h

end
end ImbalancedChen.Part3.Gamma0QuotientCoreExhaustion20261026b
