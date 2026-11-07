import ImbalancedChen.Part3CuspVerticalWeakCutoffProduct

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual compact-height approximation of a physical weak H1 jet.
The value is in Haar x dy/y^2 and both weak derivatives are in Haar x dy.
One C-infinity cutoff is used for all coordinates. Its vertical derivative
includes the proved commutator chi'_R*u, which converges to zero in raw
energy for arbitrary weighted-L2 input. Genuine weak equations and exact
horizontal zero mean are preserved. No weak gradient, form membership,
compact approximation or commutator smallness is an assumed conclusion.
-/
namespace ImbalancedChen.Part3.CuspPhysicalH1HeightExhaustion20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open CuspPhysicalWeakTailModes20261026b CuspSmoothHeightWeakLocalization20261026b
open CuspVerticalHeightCommutator20261026b CuspVerticalWeakCutoffProduct20261026b
attribute [local instance] Measure.Subtype.measureSpace

private theorem norm_sq_integral {μ : Measure CuspCylinder} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂μ := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  rw [integral_ofReal] at h
  exact Complex.ofReal_injective h

/-- Smooth bounded multipliers converge strongly whenever they are
eventually one at almost every point; no representative limit is assumed
for the L2 vector being multiplied. -/
theorem heightMultiplier_sequence_tendsto (μ : Measure CuspCylinder)
    (χ : ℕ → SmoothHeightCutoff)
    (heventual : ∀ᵐ z ∂μ, ∀ᶠ n : ℕ in atTop, (χ n).function (z.2 : ℝ) = 1)
    (u : Lp ℂ 2 μ) : Tendsto (fun n => heightMultiplier μ (χ n) u) atTop (𝓝 u) := by
  have hsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n =>
      ‖heightMultiplierFunction (χ n) u z - u z‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [heventual] with z hz
    apply (tendsto_congr' (hz.mono fun n hn => by simp [heightMultiplierFunction, hn])).mpr
    exact tendsto_const_nhds
  have hi := tendsto_integral_of_dominated_convergence (fun z => ‖u z‖ ^ 2)
    (fun n => ((heightMultiplier_memLp μ (χ n) u).aestronglyMeasurable.sub
      (Lp.aestronglyMeasurable u)).norm.pow_const 2) hsq
    (fun n => Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (heightMultiplier_error_bound (χ n) u z) 2)
    (f := fun _ => (0 : ℝ)) hlim
  have hn : Tendsto (fun n => ‖heightMultiplier μ (χ n) u - u‖ ^ 2) atTop (𝓝 0) := by
    have he (n : ℕ) : ‖heightMultiplier μ (χ n) u - u‖ ^ 2 =
        ∫ z, ‖heightMultiplierFunction (χ n) u z - u z‖ ^ 2 ∂μ := by
      rw [norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (heightMultiplier μ (χ n) u) u,
        heightMultiplier_ae μ (χ n) u] with z hz hc
      simp only [hz, Pi.sub_apply, hc]
    simpa only [he, integral_zero] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

theorem physicalVerticalCutoff_eventually_one {a : ℝ} (ha : 0 < a)
    (μ : Measure CuspCylinder) (htail : ∀ᵐ z ∂μ, a ≤ (z.2 : ℝ)) :
    ∀ᵐ z ∂μ, ∀ᶠ n : ℕ in atTop,
      (physicalVerticalCutoff a (cutoffRadius a n) ha (cutoffRadius_pos ha n)).function
        (z.2 : ℝ) = 1 := by
  filter_upwards [htail] with z hz
  exact (cutoffRadius_eventually_gt a (z.2 : ℝ)).mono fun n hn =>
    verticalHeightCutoff_eq_one ha (cutoffRadius_pos ha n) hz hn.le

theorem physicalVerticalCutoff_multiplier_tendsto {a : ℝ} (ha : 0 < a)
    (μ : Measure CuspCylinder) (htail : ∀ᵐ z ∂μ, a ≤ (z.2 : ℝ)) (u : Lp ℂ 2 μ) :
    Tendsto (fun n => heightMultiplier μ
      (physicalVerticalCutoff a (cutoffRadius a n) ha (cutoffRadius_pos ha n)) u)
        atTop (𝓝 u) :=
  heightMultiplier_sequence_tendsto μ _ (physicalVerticalCutoff_eventually_one ha μ htail) u

theorem verticalLocalizedValue_tendsto {a : ℝ} (ha : 0 < a) (u : FunctionL2 a) :
    Tendsto (fun n => verticalLocalizedValue ha (cutoffRadius_pos ha n) u) atTop (𝓝 u) := by
  apply physicalVerticalCutoff_multiplier_tendsto ha
  filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
  exact hz.2.le

theorem verticalLocalizedDerivative_tendsto {a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) :
    Tendsto (fun n => verticalLocalizedDerivative ha (cutoffRadius_pos ha n) u d) atTop (𝓝 d) := by
  have hd : Tendsto (fun n => heightMultiplier (derivativeMeasure a)
      (physicalVerticalCutoff a (cutoffRadius a n) ha (cutoffRadius_pos ha n)) d) atTop (𝓝 d) := by
    apply physicalVerticalCutoff_multiplier_tendsto ha
    filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
    exact hz.2.le
  simpa only [verticalLocalizedDerivative, add_zero] using hd.add (commutatorVector_tendsto_zero ha u)

theorem verticalLocalized_compact_support {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (u : FunctionL2 a) (d : DerivativeL2 a) :
    (∀ᵐ z ∂functionMeasure a, (z.2 : ℝ) ∉ Icc (a / 2) (2 * R) →
      verticalLocalizedValue ha hR u z = 0) ∧
    (∀ᵐ z ∂derivativeMeasure a, (z.2 : ℝ) ∉ Icc (a / 2) (2 * R) →
      verticalLocalizedDerivative ha hR u d z = 0) := by
  constructor
  · filter_upwards [heightMultiplier_ae (functionMeasure a) (physicalVerticalCutoff a R ha hR) u]
      with z hz
    intro hnot
    have hc : verticalHeightCutoff a R (z.2 : ℝ) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hnot (verticalHeightCutoff_tsupport ha hR h))
    simpa only [verticalLocalizedValue, hz, heightMultiplierFunction, physicalVerticalCutoff,
      hc, Complex.ofReal_zero, zero_mul]
  · filter_upwards [verticalLocalizedDerivative_ae ha hR u d] with z hz
    intro hnot
    have hχ : (z.2 : ℝ) ∉ tsupport (verticalHeightCutoff a R) :=
      fun h => hnot (verticalHeightCutoff_tsupport ha hR h)
    have hc := image_eq_zero_of_notMem_tsupport hχ
    have hdc := deriv_of_notMem_tsupport hχ
    simp [hz, hc, hdc]

theorem verticalLocalizedValue_preserves_mean_zero {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (u : FunctionL2 a)
    (hmean : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, verticalLocalizedValue ha hR u (x, y)
        ∂AddCircle.haarAddCircle) = 0 := by
  apply (ae_restrict_iff' (strictHeightTail_measurable a)).mp
  have hvalue := heightMultiplier_ae (functionMeasure a) (physicalVerticalCutoff a R ha hR) u
  rw [functionMeasure_product] at hvalue
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hvalue
  filter_upwards [ae_ae_of_ae_prod hswap,
    hmean.filter_mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le,
    ae_restrict_mem (strictHeightTail_measurable a)] with y hy hm hytail
  rw [integral_congr_ae hy]
  change (∫ x : UnitAddCircle, (verticalHeightCutoff a R (y : ℝ) : ℂ) * u (x, y)
    ∂AddCircle.haarAddCircle) = 0
  rw [integral_const_mul, hm hytail, mul_zero]

abbrev PhysicalH1Jet (a : ℝ) := FunctionL2 a × (DerivativeL2 a × DerivativeL2 a)

def localizedH1Jet {a : ℝ} (ha : 0 < a) (n : ℕ) (J : PhysicalH1Jet a) : PhysicalH1Jet a :=
  (verticalLocalizedValue ha (cutoffRadius_pos ha n) J.1,
   (heightMultiplier (derivativeMeasure a)
      (physicalVerticalCutoff a (cutoffRadius a n) ha (cutoffRadius_pos ha n)) J.2.1,
    verticalLocalizedDerivative ha (cutoffRadius_pos ha n) J.1 J.2.2))

/-- Both genuine weak derivative equations survive the SAME compact
height localization. Only the vertical coordinate has a commutator. -/
theorem localizedH1Jet_weak {a : ℝ} (ha : 0 < a) (n : ℕ) (J : PhysicalH1Jet a)
    (hx : HasWeakPhysicalTailDerivative 1 a J.1 J.2.1)
    (hy : HasRawWeakPhysicalVerticalDerivative a J.1 J.2.2) :
    HasWeakPhysicalTailDerivative 1 a (localizedH1Jet ha n J).1 (localizedH1Jet ha n J).2.1 ∧
    HasRawWeakPhysicalVerticalDerivative a (localizedH1Jet ha n J).1 (localizedH1Jet ha n J).2.2 := by
  exact ⟨smoothLocalizedPair_preserves_weak_derivative ha
    (physicalVerticalCutoff a (cutoffRadius a n) ha (cutoffRadius_pos ha n)) hx,
    verticalLocalized_preserves_weak_derivative ha (cutoffRadius_pos ha n) hy⟩

/-- Strong approximation in the actual weighted-value/raw-gradient norm,
with no global raw L2 assumption on the value and no omitted commutator. -/
theorem localizedH1Jet_tendsto {a : ℝ} (ha : 0 < a) (J : PhysicalH1Jet a) :
    Tendsto (fun n => localizedH1Jet ha n J) atTop (𝓝 J) := by
  have hx : Tendsto (fun n => heightMultiplier (derivativeMeasure a)
      (physicalVerticalCutoff a (cutoffRadius a n) ha (cutoffRadius_pos ha n)) J.2.1)
        atTop (𝓝 J.2.1) := by
    apply physicalVerticalCutoff_multiplier_tendsto ha
    filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
    exact hz.2.le
  exact (verticalLocalizedValue_tendsto ha J.1).prodMk_nhds
    (hx.prodMk_nhds (verticalLocalizedDerivative_tendsto ha J.1 J.2.2))

end
end ImbalancedChen.Part3.CuspPhysicalH1HeightExhaustion20261026b
