import ImbalancedChen.Part3ActualMobiusLocalJacobian
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Native compact scalar Lp transport for the actual Mobius map.  A produced
bound on |cz+d|^4 and the exact Jacobian equality prove domination of the
actual compact-source pushforward by C times target planar volume.
Consequently every raw target Lp representative composes to source Lp.
In particular squared-L2 error contracts up to C.  No composition
continuity, weak chain rule or gradient covariance is a hypothesis.
-/
namespace ImbalancedChen.Part3.ActualMobiusCompactLpTransport20261026b
noncomputable section
open Set MeasureTheory Matrix
open scoped MatrixGroups UpperHalfPlane
open ActualMobiusConformalTwoJet20261025a ActualMobiusLocalJacobian20261026b

def compactCompositionConstant (g : SL(2, ℤ)) (K : Set ℂ) (hK : IsCompact K) : ℝ :=
  Classical.choose (compact_inverseJacobian_bound g hK)

theorem compactCompositionConstant_one_le (g : SL(2, ℤ)) {K : Set ℂ} (hK : IsCompact K) :
    1 ≤ compactCompositionConstant g K hK :=
  (Classical.choose_spec (compact_inverseJacobian_bound g hK)).1

theorem compactCompositionConstant_bounds (g : SL(2, ℤ)) {K : Set ℂ} (hK : IsCompact K)
    {z : ℂ} (hz : z ∈ K) :
    ‖UpperHalfPlane.denom (realMatrix g) z‖^4 ≤ compactCompositionConstant g K hK :=
  (Classical.choose_spec (compact_inverseJacobian_bound g hK)).2 z hz

theorem compact_composition_lintegral_le (g : SL(2, ℤ)) {K : Set ℂ}
    (hK : IsCompact K) (hKp : ∀ z ∈ K, 0 < z.im) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in K, f (actualMobius g z)) ≤
      ENNReal.ofReal (compactCompositionConstant g K hK) * ∫⁻ w in actualMobius g '' K, f w := by
  let C := compactCompositionConstant g K hK
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (compactCompositionConstant_one_le g hK)
  have hpoint (z : ℂ) (hz : z ∈ K) :
      f (actualMobius g z) ≤ ENNReal.ofReal C *
        (ENNReal.ofReal (rawJacobian g z)*f (actualMobius g z)) := by
    have hden : 0 < ‖UpperHalfPlane.denom (realMatrix g) z‖^4 :=
      pow_pos (norm_pos_iff.mpr (denom_ne_zero g ⟨z,hKp z hz⟩)) 4
    have hcoef : 1 ≤ C*rawJacobian g z := by
      rw [rawJacobian,mul_one_div]
      exact (le_div_iff₀ hden).mpr (by simpa only [one_mul] using compactCompositionConstant_bounds g hK hz)
    have hcoefNN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal C*ENNReal.ofReal (rawJacobian g z) := by
      calc
        _ = ENNReal.ofReal (1 : ℝ) := by simp
        _ ≤ ENNReal.ofReal (C*rawJacobian g z) := ENNReal.ofReal_le_ofReal hcoef
        _ = _ := ENNReal.ofReal_mul hC
    simpa only [one_mul,mul_assoc] using mul_le_mul_right' hcoefNN (f (actualMobius g z))
  calc
    _ ≤ ∫⁻ z in K, ENNReal.ofReal C *
        (ENNReal.ofReal (rawJacobian g z)*f (actualMobius g z)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      exact hpoint z hz
    _ = ENNReal.ofReal C * ∫⁻ z in K,
        ENNReal.ofReal (rawJacobian g z)*f (actualMobius g z) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [← actualMobius_lintegral_image g hK.measurableSet hKp]

theorem actualMobius_aemeasurable_compact (g : SL(2, ℤ)) {K : Set ℂ}
    (hK : IsCompact K) (hKp : ∀ z ∈ K, 0 < z.im) :
    AEMeasurable (actualMobius g) ((volume : Measure ℂ).restrict K) := by
  have hc : ContinuousOn (actualMobius g) K := fun z hz =>
    (actualMobius_hasDerivAt g ⟨z,hKp z hz⟩).continuousAt.continuousWithinAt
  exact hc.aemeasurable hK.measurableSet

/-- The bound is a theorem about the actual pushforward measure, not a
transport-map field supplied by a future H1 structure. -/
theorem compact_composition_map_le (g : SL(2, ℤ)) {K : Set ℂ}
    (hK : IsCompact K) (hKp : ∀ z ∈ K, 0 < z.im) :
    (((volume : Measure ℂ).restrict K).map (actualMobius g)) ≤
      ENNReal.ofReal (compactCompositionConstant g K hK) •
        ((volume : Measure ℂ).restrict (actualMobius g '' K)) := by
  apply Measure.le_iff.mpr
  intro A hA
  have hineq := compact_composition_lintegral_le g hK hKp (A.indicator (fun _ => (1 : ℝ≥0∞)))
  have hm := actualMobius_aemeasurable_compact g hK hKp
  have hmap := lintegral_map' (measurable_const.indicator hA).aemeasurable hm
  rw [← hmap] at hineq
  simpa only [lintegral_indicator_one hA,Measure.smul_apply,smul_eq_mul] using hineq

/-- Raw target Lp is sufficient; measurability and finite source norm
are consequences of the genuine geometric measure domination. -/
theorem memLp_comp_actualMobius (g : SL(2, ℤ)) {K : Set ℂ}
    (hK : IsCompact K) (hKp : ∀ z ∈ K, 0 < z.im)
    {p : ℝ≥0∞} {F : ℂ → ℂ}
    (hF : MemLp F p ((volume : Measure ℂ).restrict (actualMobius g '' K))) :
    MemLp (fun z => F (actualMobius g z)) p ((volume : Measure ℂ).restrict K) := by
  have hpush : MemLp F p (((volume : Measure ℂ).restrict K).map (actualMobius g)) :=
    hF.of_measure_le_smul (by simp) (compact_composition_map_le g hK hKp)
  exact hpush.comp_of_map (actualMobius_aemeasurable_compact g hK hKp)

/-- The precise scalar error inequality used in first-jet approximation. -/
theorem compact_composition_L2_error_le (g : SL(2, ℤ)) {K : Set ℂ}
    (hK : IsCompact K) (hKp : ∀ z ∈ K, 0 < z.im) (F G : ℂ → ℂ) :
    (∫⁻ z in K, ENNReal.ofReal (‖F (actualMobius g z)-G (actualMobius g z)‖^2)) ≤
      ENNReal.ofReal (compactCompositionConstant g K hK) *
        ∫⁻ w in actualMobius g '' K, ENNReal.ofReal (‖F w-G w‖^2) :=
  compact_composition_lintegral_le g hK hKp (fun w => ENNReal.ofReal (‖F w-G w‖^2))

end
end ImbalancedChen.Part3.ActualMobiusCompactLpTransport20261026b
