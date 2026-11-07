import ImbalancedChen.Part3CommonHeightSmoothApproximation
import ImbalancedChen.Part3CuspPhysicalHeightExhaustion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Genuine smooth height localization of the physical horizontal weak graph.
The multiplier is C-infinity with compact support inside positive height.
Multiplying a weak pair by the same height cutoff preserves its ordinary
tensor weak equation: test with beta*chi and use the actual AE Lp joins.
The horizontal derivative of chi is literally zero. An explicit sequence
of such smooth multipliers approximates both physical L2 coordinates.
This proves compact-height WEAK graph approximation; it does not claim
that multiplying an arbitrary weak pair smooths its horizontal variable.
-/
namespace ImbalancedChen.Part3.CuspSmoothHeightWeakLocalization20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a CuspPhysicalWeakTailModes20261026b
open CuspPhysicalHeightExhaustion20261026b
open PositiveRectangleSmoothTensorDensity20261025a
attribute [local instance] Measure.Subtype.measureSpace

structure SmoothHeightCutoff where
  function : ℝ → ℝ
  smooth : ContDiff ℝ ∞ function
  compact : HasCompactSupport function
  positive_support : tsupport function ⊆ Ioi (0 : ℝ)
  nonneg : ∀ y, 0 ≤ function y
  le_one : ∀ y, function y ≤ 1

theorem cutoff_norm_le_one (χ : SmoothHeightCutoff) (y : ℝ) :
    ‖(χ.function y : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (χ.nonneg y)]
  exact χ.le_one y

theorem heightCutoff_horizontal_hasDerivAt_zero (χ : SmoothHeightCutoff)
    (y : PositiveHeight) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => (χ.function (y : ℝ) : ℂ)) 0 t :=
  hasDerivAt_const t _

def heightMultiplierFunction (χ : SmoothHeightCutoff) (u : CuspCylinder → ℂ)
    (z : CuspCylinder) : ℂ := (χ.function (z.2 : ℝ) : ℂ) * u z

theorem heightMultiplier_memLp (μ : Measure CuspCylinder) (χ : SmoothHeightCutoff)
    (u : Lp ℂ 2 μ) : MemLp (heightMultiplierFunction χ u) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := (1 : ℝ))
  · exact ((Complex.continuous_ofReal.comp (χ.smooth.continuous.comp
      (continuous_subtype_val.comp continuous_snd))).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable u)
  · exact Eventually.of_forall fun z => by
      change ‖(χ.function (z.2 : ℝ) : ℂ) * u z‖ ≤ 1 * ‖u z‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (cutoff_norm_le_one χ _) (norm_nonneg _)

def heightMultiplier (μ : Measure CuspCylinder) (χ : SmoothHeightCutoff)
    (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (heightMultiplier_memLp μ χ u).toLp (heightMultiplierFunction χ u)

theorem heightMultiplier_ae (μ : Measure CuspCylinder) (χ : SmoothHeightCutoff)
    (u : Lp ℂ 2 μ) :
    (heightMultiplier μ χ u : CuspCylinder → ℂ) =ᵐ[μ] heightMultiplierFunction χ u :=
  (heightMultiplier_memLp μ χ u).coeFn_toLp

def smoothLocalizedPair (a : ℝ) (χ : SmoothHeightCutoff)
    (p : FunctionL2 a × DerivativeL2 a) : FunctionL2 a × DerivativeL2 a :=
  (heightMultiplier (functionMeasure a) χ p.1,
   heightMultiplier (derivativeMeasure a) χ p.2)

/-- Exact tensor weak equation after smooth compact height localization.
Both native coordinates use the same multiplier. The raw derivative AE
join is transported into weighted tests by the actual positive-tail
measure bound, before any representative is rewritten. -/
theorem smoothLocalizedPair_preserves_weak_derivative {w a : ℝ} (ha : 0 < a)
    (χ : SmoothHeightCutoff) {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative w a u d) :
    HasWeakPhysicalTailDerivative w a
      (smoothLocalizedPair a χ (u, d)).1 (smoothLocalizedPair a χ (u, d)).2 := by
  intro φ ψ hφ hψ β hβ hβc hβp
  have htest := hweak φ ψ hφ hψ (fun y => β y * χ.function y)
    (hβ.mul χ.smooth) (hβc.mul_right)
    (tsupport_mul_subset_left.trans hβp)
  have hu := heightMultiplier_ae (functionMeasure a) χ u
  have hd := (Measure.absolutelyContinuous_of_le_smul
    (functionMeasure_le_derivativeMeasure ha)).ae_eq
      (heightMultiplier_ae (derivativeMeasure a) χ d)
  have hleft : (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 *
      ((w : ℂ) * (smoothLocalizedPair a χ (u, d)).2 z) ∂functionMeasure a) =
      ∫ z : CuspCylinder, ((β (z.2 : ℝ) * χ.function (z.2 : ℝ) : ℝ) : ℂ) *
        φ z.1 * ((w : ℂ) * d z) ∂functionMeasure a := by
    apply integral_congr_ae
    filter_upwards [hd] with z hz
    change (β (z.2 : ℝ) : ℂ) * φ z.1 *
      ((w : ℂ) * heightMultiplier (derivativeMeasure a) χ d z) = _
    rw [hz, heightMultiplierFunction]
    push_cast
    ring
  have hright : (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 *
      (smoothLocalizedPair a χ (u, d)).1 z ∂functionMeasure a) =
      ∫ z : CuspCylinder, ((β (z.2 : ℝ) * χ.function (z.2 : ℝ) : ℝ) : ℂ) *
        ψ z.1 * u z ∂functionMeasure a := by
    apply integral_congr_ae
    filter_upwards [hu] with z hz
    change (β (z.2 : ℝ) : ℂ) * ψ z.1 *
      heightMultiplier (functionMeasure a) χ u z = _
    rw [hz, heightMultiplierFunction]
    push_cast
    ring
  rw [hleft, hright]
  exact htest

theorem heightMultiplier_zero_outside (μ : Measure CuspCylinder) (χ : SmoothHeightCutoff)
    (u : Lp ℂ 2 μ) :
    ∀ᵐ z ∂μ, (z.2 : ℝ) ∉ tsupport χ.function → heightMultiplier μ χ u z = 0 := by
  filter_upwards [heightMultiplier_ae μ χ u] with z hz
  intro hs
  rw [hz, heightMultiplierFunction, image_eq_zero_of_notMem_tsupport hs]
  simp

def tailSmoothCutoff (a : ℝ) (ha : 0 < a) (n : ℕ) : SmoothHeightCutoff where
  function := verticalBump a (a + (n : ℝ) + 1) ha (by linarith [Nat.cast_nonneg (R := ℝ) n])
  smooth := (verticalBump _ _ _ _).contDiff
  compact := (verticalBump _ _ _ _).hasCompactSupport
  positive_support := verticalBump_positive_support _ _ _ _
  nonneg := fun _ => (verticalBump _ _ _ _).nonneg
  le_one := fun _ => (verticalBump _ _ _ _).le_one

theorem tailSmoothCutoff_eventually_one {a : ℝ} (ha : 0 < a)
    (y : PositiveHeight) (hy : a ≤ (y : ℝ)) :
    ∀ᶠ n : ℕ in atTop, (tailSmoothCutoff a ha n).function (y : ℝ) = 1 := by
  filter_upwards [eventually_mem_heightBand a y hy] with n hn
  exact verticalBump_eq_one _ _ _ _ hn

private theorem norm_sq_integral {μ : Measure CuspCylinder} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂μ := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  rw [integral_ofReal] at h
  exact Complex.ofReal_injective h

theorem heightMultiplier_error_bound (χ : SmoothHeightCutoff) (u : CuspCylinder → ℂ)
    (z : CuspCylinder) : ‖heightMultiplierFunction χ u z - u z‖ ≤ ‖u z‖ := by
  have he : heightMultiplierFunction χ u z - u z =
      (((χ.function (z.2 : ℝ) - 1 : ℝ) : ℂ)) * u z := by
    simp only [heightMultiplierFunction, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc : |χ.function (z.2 : ℝ) - 1| ≤ 1 := abs_le.mpr
    ⟨by linarith [χ.nonneg (z.2 : ℝ)], by linarith [χ.le_one (z.2 : ℝ)]⟩
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)

/-- Strong native L2 convergence for the actual smooth height sequence.
The squared error is dominated by the input's own integrable square norm. -/
theorem tailSmoothCutoff_tendsto {a : ℝ} (ha : 0 < a) (μ : Measure CuspCylinder)
    (htail : ∀ᵐ z ∂μ, a ≤ (z.2 : ℝ)) (u : Lp ℂ 2 μ) :
    Tendsto (fun n => heightMultiplier μ (tailSmoothCutoff a ha n) u) atTop (𝓝 u) := by
  have hsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n =>
      ‖heightMultiplierFunction (tailSmoothCutoff a ha n) u z - u z‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [htail] with z hz
    apply (tendsto_congr' ((tailSmoothCutoff_eventually_one ha z.2 hz).mono
      fun n hn => by simp [heightMultiplierFunction, hn])).mpr
    exact tendsto_const_nhds
  have hint := tendsto_integral_of_dominated_convergence (fun z => ‖u z‖ ^ 2)
    (fun n => (((heightMultiplier_memLp μ (tailSmoothCutoff a ha n) u).aestronglyMeasurable.sub
      (Lp.aestronglyMeasurable u)).norm.pow_const 2)) hsq
    (fun n => Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (heightMultiplier_error_bound (tailSmoothCutoff a ha n) u z) 2)
    (f := fun _ => (0 : ℝ)) hlim
  have hn : Tendsto (fun n => ‖heightMultiplier μ (tailSmoothCutoff a ha n) u - u‖ ^ 2)
      atTop (𝓝 0) := by
    have he (n : ℕ) : ‖heightMultiplier μ (tailSmoothCutoff a ha n) u - u‖ ^ 2 =
        ∫ z, ‖heightMultiplierFunction (tailSmoothCutoff a ha n) u z - u z‖ ^ 2 ∂μ := by
      rw [norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (heightMultiplier μ (tailSmoothCutoff a ha n) u) u,
        heightMultiplier_ae μ (tailSmoothCutoff a ha n) u] with z hz hc
      simp only [hz, Pi.sub_apply, hc]
    simpa only [he, integral_zero] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- The SAME genuine smooth compact-height cutoffs converge in both
physical graph norms. Every term satisfies the original weak equation. -/
theorem smoothLocalizedPair_tendsto {a : ℝ} (ha : 0 < a)
    (p : FunctionL2 a × DerivativeL2 a) :
    Tendsto (fun n => smoothLocalizedPair a (tailSmoothCutoff a ha n) p) atTop (𝓝 p) := by
  have hf : ∀ᵐ z ∂functionMeasure a, a ≤ (z.2 : ℝ) := by
    filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
    exact hz.2.le
  have hd : ∀ᵐ z ∂derivativeMeasure a, a ≤ (z.2 : ℝ) := by
    filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
    exact hz.2.le
  exact (tailSmoothCutoff_tendsto ha (functionMeasure a) hf p.1).prodMk_nhds
    (tailSmoothCutoff_tendsto ha (derivativeMeasure a) hd p.2)

end
end ImbalancedChen.Part3.CuspSmoothHeightWeakLocalization20261026b
