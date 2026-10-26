import ImbalancedChen.Part3ActualInfinityHighTailMeasureTransport
import Mathlib.MeasureTheory.Function.L2Space

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The genuine whole HIGH infinity strip receives a contractive complex
linear pullback from the original Gamma quotient Hilbert space. Its
representative is literally f(orbitProjection z), its norm is exactly
the original quotient L2 norm restricted to the actual single-cusp tail,
and physical quotient strong limits transport to high-strip strong limits.
No whole low-height strip or all-cusp assertion is made.
-/
namespace ImbalancedChen.Part3.ActualInfinityHighTailL2Pullback20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualHighCuspTail20261025a
open ActualCuspStripCutoff20261025a
open ActualInfinityHighTailMeasureTransport20261026b

abbrev QuotientL2 (N : ℕ) [NeZero N] := Lp ℂ 2 (carrierPushforward N)
abbrev HighStripL2 (Y : ℝ) :=
  Lp ℂ 2 ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y))

def highStripMeasurePreserving (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y) :
    MeasurePreserving (orbitProjection N)
      ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y))
      ((carrierPushforward N).restrict (quotientHighTail N Y)) :=
  ⟨orbitProjection_measurable N, actual_infinity_high_strip_map_measure N hY⟩

def quotientHighTailRestriction (N : ℕ) [NeZero N] (Y : ℝ) :
    QuotientL2 N →L[ℝ] Lp ℂ 2 ((carrierPushforward N).restrict (quotientHighTail N Y)) :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using
      (Measure.restrict_le_self : (carrierPushforward N).restrict (quotientHighTail N Y) ≤
        carrierPushforward N))

theorem quotientHighTailRestriction_norm_le_one (N : ℕ) [NeZero N] (Y : ℝ) :
    ‖quotientHighTailRestriction N Y‖ ≤ 1 := by
  simpa only [quotientHighTailRestriction, ENNReal.toReal_one, Real.one_rpow] using
    (Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := (2 : ℝ≥0∞))
      (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa only [one_smul] using
        (Measure.restrict_le_self : (carrierPushforward N).restrict (quotientHighTail N Y) ≤
          carrierPushforward N)))

theorem quotientHighTailRestriction_ae (N : ℕ) [NeZero N] (Y : ℝ)
    (f : QuotientL2 N) :
    quotientHighTailRestriction N Y f =ᵐ[
      (carrierPushforward N).restrict (quotientHighTail N Y)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
    (by simpa only [one_smul] using
      (Measure.restrict_le_self : (carrierPushforward N).restrict (quotientHighTail N Y) ≤
        carrierPushforward N)) f

private def highPullbackReal (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y) :
    QuotientL2 N →L[ℝ] HighStripL2 Y :=
  ((Lp.compMeasurePreservingₗᵢ ℂ (orbitProjection N)
      (highStripMeasurePreserving N hY)).toContinuousLinearMap.restrictScalars ℝ).comp
    (quotientHighTailRestriction N Y)

private theorem highPullbackReal_ae (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y)
    (f : QuotientL2 N) :
    highPullbackReal N hY f =ᵐ[
      (volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)]
      fun z => f (orbitProjection N z) := by
  have hc := Lp.coeFn_compMeasurePreserving (quotientHighTailRestriction N Y f)
    (highStripMeasurePreserving N hY)
  have hr := (highStripMeasurePreserving N hY).quasiMeasurePreserving.ae_eq
    (quotientHighTailRestriction_ae N Y f)
  exact hc.trans hr

private theorem highPullbackReal_norm_le (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y)
    (f : QuotientL2 N) : ‖highPullbackReal N hY f‖ ≤ ‖f‖ := by
  change ‖Lp.compMeasurePreservingₗᵢ ℂ (orbitProjection N)
      (highStripMeasurePreserving N hY) (quotientHighTailRestriction N Y f)‖ ≤ ‖f‖
  rw [LinearIsometry.norm_map]
  calc
    _ ≤ ‖quotientHighTailRestriction N Y‖ * ‖f‖ :=
      (quotientHighTailRestriction N Y).le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (quotientHighTailRestriction_norm_le_one N Y) (norm_nonneg f)
    _ = _ := one_mul _

private theorem highPullbackReal_complex_smul (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 1 < Y) (c : ℂ) (f : QuotientL2 N) :
    highPullbackReal N hY (c • f) = c • highPullbackReal N hY f := by
  apply Lp.ext
  have hcf := (actual_infinity_high_strip_quasiMeasurePreserving N hY).ae_eq (Lp.coeFn_smul c f)
  filter_upwards [highPullbackReal_ae N hY (c • f), highPullbackReal_ae N hY f,
    Lp.coeFn_smul c (highPullbackReal N hY f), hcf] with z h1 h2 h3 h4
  rw [h1, h3, h2, h4]

/-- The original spatial quotient normalization supplies a complex-linear
Hilbert contraction onto the literal high infinity strip. -/
def actualHighTailPullback (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y) :
    QuotientL2 N →L[ℂ] HighStripL2 Y :=
  LinearMap.mkContinuous
    { toFun := highPullbackReal N hY
      map_add' := (highPullbackReal N hY).map_add
      map_smul' := highPullbackReal_complex_smul N hY }
    1 (fun f => by simpa only [one_mul] using highPullbackReal_norm_le N hY f)

theorem actualHighTailPullback_ae (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y)
    (f : QuotientL2 N) :
    actualHighTailPullback N hY f =ᵐ[
      (volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)]
      fun z => f (orbitProjection N z) :=
  highPullbackReal_ae N hY f

theorem actualHighTailPullback_norm_le (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y)
    (f : QuotientL2 N) : ‖actualHighTailPullback N hY f‖ ≤ ‖f‖ :=
  highPullbackReal_norm_le N hY f

theorem actualHighTailPullback_opNorm_le_one (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y) :
    ‖actualHighTailPullback N hY‖ ≤ 1 := by
  apply (actualHighTailPullback N hY).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using actualHighTailPullback_norm_le N hY f

/-- Exact norm on the ORIGINAL quotient restricted measure, not merely
an unspecified bound on a representative's chart norm. -/
theorem actualHighTailPullback_norm_eq (N : ℕ) [NeZero N] {Y : ℝ} (hY : 1 < Y)
    (f : QuotientL2 N) :
    ‖actualHighTailPullback N hY f‖ =
      (eLpNorm f 2 ((carrierPushforward N).restrict (quotientHighTail N Y))).toReal := by
  change ‖Lp.compMeasurePreservingₗᵢ ℂ (orbitProjection N)
      (highStripMeasurePreserving N hY) (quotientHighTailRestriction N Y f)‖ = _
  rw [LinearIsometry.norm_map, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_ae (quotientHighTailRestriction_ae N Y f)

theorem actualHighTailPullback_strong_limit {ι : Type*} (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) {l : Filter ι} {u : ι → QuotientL2 N} {f : QuotientL2 N}
    (hu : Filter.Tendsto u l (nhds f)) :
    Filter.Tendsto (fun i => actualHighTailPullback N hY (u i)) l
      (nhds (actualHighTailPullback N hY f)) :=
  ((actualHighTailPullback N hY).continuous.tendsto f).comp hu

end
end ImbalancedChen.Part3.ActualInfinityHighTailL2Pullback20261026b
