import ImbalancedChen.Part3ActualModularSmoothCuspCutoff
import ImbalancedChen.Part3Gamma0TotalModularHighCuspTail

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual smooth modular cutoff descends to the original Gamma0 orbit
quotient. Its literal squared error from one is dominated by the genuine
full modular high-cusp indicator on the canonical conull quotient image.
The actual finite-cover measure gives L2 error squared <= index/Y.
No global cutoff, quotient mass, or vanishing-error conclusion is assumed.
This does not place the cutoff in the existing smoothCore or completed
Dirichlet form domain; those require explicit approximation suppliers.
-/

namespace ImbalancedChen.Part3.ActualModularSmoothCutoffL2Tail20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ENNReal
open Gamma0ParabolicCosetRows20261025a Gamma0ParabolicEffectiveDecomposition20261025a
open Gamma0ActualParabolicUnfolding20261025a Gamma0ActualHighCuspTail20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a Gamma0ModularFiniteCoverMeasure20261025a
open ActualParabolicHighSeedLocalFinite20261025a ActualModularSmoothCuspCutoff20261025a

/-- Actual scalar smooth high trace on the full modular quotient. -/
def quotientSmoothHighTrace (Y : ℝ) : Gamma0OrbitSpace 1 → ℝ :=
  Quotient.lift (highTrace 1 Y) (by
    intro z w hzw
    obtain ⟨g, rfl⟩ := (MulAction.orbitRel_apply).mp hzw
    exact highTrace_gamma0_invariant 1 Y g w)

@[simp] theorem quotientSmoothHighTrace_projection (Y : ℝ) (z : UpperHalfPlane) :
    quotientSmoothHighTrace Y (orbitProjection 1 z) = highTrace 1 Y z := rfl

theorem quotientSmoothHighTrace_measurable (Y : ℝ) (hY : 0 < Y) :
    Measurable (quotientSmoothHighTrace Y) :=
  measurable_from_quotient.mpr (highTrace_continuous 1 Y hY).measurable

theorem highTrace_square_le_indicator (N : ℕ) (Y : ℝ) (hY : 1 < Y)
    (z : UpperHalfPlane) :
    ENNReal.ofReal ((highTrace N Y z)^2) ≤ parabolicTraceNN N (highSeed Y) z := by
  by_cases hex : ∃ q : GammaInfinityCosets N,
      highProfile Y (parabolicRepresentative N q • z).im ≠ 0
  · obtain ⟨q, hq⟩ := hex
    have hhigh : Y ≤ (parabolicRepresentative N q • z).im :=
      (highProfile_nonzero_height Y (lt_trans (by norm_num) hY) _ hq).le
    have hn : parabolicTraceNN N (highSeed Y) z = 1 := by
      rw [parabolicTraceNN, tsum_eq_single q]
      · exact Set.indicator_of_mem hhigh _
      · intro r hr
        apply Set.indicator_of_notMem
        intro hh
        exact hr (closed_high_coset_unique N Y hY r q z hh hhigh)
    rw [hn]
    have hb := highTrace_bounds N Y hY.le z
    have hs : (highTrace N Y z)^2 ≤ 1 := by
      nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
    exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)
  · have hz : highTrace N Y z = 0 := by
      apply tsum_eq_zero.mpr
      intro q
      exact not_ne_iff.mp (fun h => hex ⟨q, h⟩)
    rw [hz]
    simp

theorem quotientSmoothHighTrace_square_le_indicator_ae (Y : ℝ) (hY : 1 < Y) :
    ∀ᵐ q ∂carrierPushforward 1,
      ENNReal.ofReal ((quotientSmoothHighTrace Y q)^2) ≤ quotientHighIndicator 1 Y q := by
  filter_upwards [reducedProjection_range_ae 1] with q hq
  obtain ⟨z, rfl⟩ := hq
  change ENNReal.ofReal ((highTrace 1 Y (z : UpperHalfPlane))^2) ≤ _
  rw [quotientHighIndicator, parabolicNonnegativePoincare_projection]
  exact highTrace_square_le_indicator 1 Y hY z

theorem lintegral_quotientSmoothHighTrace_square_le (Y : ℝ) (hY : 1 < Y) :
    (∫⁻ q, ENNReal.ofReal ((quotientSmoothHighTrace Y q)^2) ∂carrierPushforward 1) ≤
      ENNReal.ofReal (1 / Y) := by
  calc
    _ ≤ ∫⁻ q, quotientHighIndicator 1 Y q ∂carrierPushforward 1 :=
      lintegral_mono_ae (quotientSmoothHighTrace_square_le_indicator_ae Y hY)
    _ = ENNReal.ofReal (1 / Y) := by
      rw [quotientHighIndicator_eq_indicator 1 Y hY,
        lintegral_indicator (quotientHighTail_measurable 1 Y)]
      simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
      exact quotientHighTail_volume 1 Y hY

/-- Actual smooth global cutoff on every original Gamma0 quotient. -/
def quotientCutoff (N : ℕ) (Y : ℝ) (q : Gamma0OrbitSpace N) : ℝ :=
  1 - quotientSmoothHighTrace Y (forgetLevel N q)

@[simp] theorem quotientCutoff_projection (N : ℕ) (Y : ℝ) (z : UpperHalfPlane) :
    quotientCutoff N Y (orbitProjection N z) = globalCutoff Y z := rfl

theorem quotientCutoff_measurable (N : ℕ) (Y : ℝ) (hY : 0 < Y) :
    Measurable (quotientCutoff N Y) :=
  measurable_const.sub ((quotientSmoothHighTrace_measurable Y hY).comp
    (forgetLevel_measurable N))

theorem quotientCutoff_bounds (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (q : Gamma0OrbitSpace N) :
    0 ≤ quotientCutoff N Y q ∧ quotientCutoff N Y q ≤ 1 := by
  refine Quotient.inductionOn q (fun z => ?_)
  exact globalCutoff_bounds Y hY z

/-- Genuine squared L2 error of the constructed actual modular cutoff,
with the actual subgroup index, not a supplied tail-bound constant. -/
theorem quotientCutoff_L2_error_le (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    (∫⁻ q, ENNReal.ofReal ((1 - quotientCutoff N Y q)^2) ∂carrierPushforward N) ≤
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ENNReal.ofReal (1 / Y) := by
  let F : Gamma0OrbitSpace 1 → ℝ≥0∞ :=
    fun q => ENNReal.ofReal ((quotientSmoothHighTrace Y q)^2)
  have hF : Measurable F :=
    ((quotientSmoothHighTrace_measurable Y
      (lt_trans (by norm_num) hY)).pow_const 2).ennreal_ofReal
  have herr : (fun q => ENNReal.ofReal ((1 - quotientCutoff N Y q)^2)) =
      F ∘ forgetLevel N := by
    funext q
    congr 1
    dsimp [quotientCutoff, F]
    ring
  rw [herr, ← lintegral_map hF (forgetLevel_measurable N),
    forgetLevel_map_carrier, lintegral_smul_measure]
  exact mul_le_mul_left' (lintegral_quotientSmoothHighTrace_square_le Y hY) _

end
end ImbalancedChen.Part3.ActualModularSmoothCutoffL2Tail20261025a
