import ImbalancedChen.Part3Gamma0CompletedLocalizedChartGradient
import ImbalancedChen.Part3PositiveRectangleNativeHyperbolicL2

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
Exact ordinary physical derivative-energy transport from canonical
hyperbolic chart energy. Both coordinates and the y^-2 cancellation are
proved explicitly. Derivatives vanish outside the positive rectangle by
their actual support theorem. Native cutoff support also controls genuine
zero germs of both coordinate derivatives, so no boundary term is dropped. -/

namespace ImbalancedChen.Part3.PositiveRectangleNativeDerivativeEnergy20261026b
noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane
open PositiveRectangleAffineNormalization20261026b
open PositiveRectanglePhysicalRellich20261026b
open PositiveRectangleNativeHyperbolicL220261026b
open CompactRectanglePhysicalRellich20261026a
open MaassWeakOperatorCore20261024zz
open MaassWeightedCoordinateL220261024zz
open CanonicalTensorHyperbolicLaplacianForm20261024z
open Gamma0CompactGreenProductL120261025a
open ActualGamma0MaassDescent20261025a
open ActualPoincareGradientEnergyBudget20261025a
open ActualPoincareDirichletTrace20261025a
open ActualModularSmoothCuspCutoff20261025a

theorem physical_partial_zero_nonpositive {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) (j : Fin 2) {p : Plane} (hp : ¬ 0 < p.2) :
    partial s.function j p = 0 := by
  by_contra hn
  have hy := (region_height hδ (partial_support_region s j hn)).1
  exact hp (R.bottom_pos.trans_le hy)

theorem native_slice_partials {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ)
    {p : Plane} (hp : 0 < p.2) :
    sliceDx s.function p = partial s.function 0 p ∧
      sliceDy s.function p = partial s.function 1 p := by
  have hd : DifferentiableOn ℝ s.function positiveChart :=
    (s.smooth.differentiable (by norm_num)).differentiableOn
  constructor
  · simpa only [partial,direction,if_pos rfl] using sliceDx_eq_fderiv _ hd hp
  · simpa only [partial,direction,Fin.one_ne_zero,if_false] using sliceDy_eq_fderiv _ hd hp

/-- Canonical y^-2 volume cancels exactly against the y² in chartEnergy.
The output is the literal sum of ordinary physical partial energies. -/
theorem native_chartEnergy_eq_physicalEnergy {R : Rectangle} {δ : ℝ}
    (hδ : 0 ≤ δ) (s : RectangleSeed R δ) :
    (∫ z : UpperHalfPlane, chartEnergy s.function (z.re,z.im)) = energy s := by
  let G : Plane → ℝ := fun p => p.2^2 *
    (‖partial s.function 0 p‖^2 + ‖partial s.function 1 p‖^2)
  have hn : (∫ z : UpperHalfPlane, chartEnergy s.function (z.re,z.im)) =
      ∫ z : UpperHalfPlane, G (z.re,z.im) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      rw [chartEnergy,(native_slice_partials s z.im_pos).1,
        (native_slice_partials s z.im_pos).2])
  rw [hn,canonical_real_integral_eq_chart G]
  unfold chartMeasure
  rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
  have hc : (∫ p in upperChart, chartWeight p • G p) =
      ∫ p in upperChart, ‖partial s.function 0 p‖^2 + ‖partial s.function 1 p‖^2 := by
    apply setIntegral_congr_fun upperChart_measurable
    intro p hp
    change (p.2⁻¹)^2 * (p.2^2 * _) = _
    have hy : p.2 ≠ 0 := ne_of_gt hp
    field_simp
  rw [hc]
  have he : (∫ p in upperChart, ‖partial s.function 0 p‖^2 + ‖partial s.function 1 p‖^2) =
      ∫ p : Plane, ‖partial s.function 0 p‖^2 + ‖partial s.function 1 p‖^2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      rw [physical_partial_zero_nonpositive hδ s 0 hp,physical_partial_zero_nonpositive hδ s 1 hp]
      simp)
  rw [he]
  have hi (j : Fin 2) : Integrable (fun p : Plane => ‖partial s.function j p‖^2) :=
    ((partial_continuous _ s.smooth j).norm.pow 2).integrable_of_hasCompactSupport
      ((compact_of_support R (partial_support_region s j)).norm.comp_left
        (g := fun t : ℝ => t^2) (by simp))
  rw [integral_add (hi 0) (hi 1)]
  rfl

/-- Explicit physical mass comparison with the exact native L2 norm.
Only the physical rectangle's upper height enters this direction. -/
theorem physical_mass_le_top_square_native {R : Rectangle} {δ : ℝ}
    (hδ : 0 ≤ δ) (s : RectangleSeed R δ) :
    ‖physical s‖^2 ≤ (R.bottom+R.height)^2 * ‖nativeL2 hδ s‖^2 := by
  have h := (weighted_square_bounds hδ s).1
  rw [← nativeL2_norm hδ s] at h
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg (R.bottom+R.height))
  have ht : R.bottom+R.height ≠ 0 := ne_of_gt (R.bottom_pos.add R.height_pos)
  field_simp [ht] at hmul
  nlinarith

theorem physical_h1_le_native_mass_energy {R : Rectangle} {δ : ℝ}
    (hδ : 0 ≤ δ) (s : RectangleSeed R δ) :
    ‖physical s‖^2 + energy s ≤ ((R.bottom+R.height)^2+1) *
      ((∫ z : UpperHalfPlane, ‖nativeFunction s z‖^2) +
        ∫ z : UpperHalfPlane, chartEnergy s.function (z.re,z.im)) := by
  have hm := physical_mass_le_top_square_native hδ s
  rw [nativeL2_square] at hm
  rw [native_chartEnergy_eq_physicalEnergy hδ s]
  have he : 0 ≤ energy s := add_nonneg (directionalEnergy_nonneg s 0) (directionalEnergy_nonneg s 1)
  have hn := integral_nonneg (μ := (volume : Measure UpperHalfPlane))
    (fun z => sq_nonneg ‖nativeFunction s z‖)
  nlinarith [mul_nonneg (sq_nonneg (R.bottom+R.height)) he]

/-- Outside native topological support, the positive coordinate chart
has a true zero germ. Thus BOTH actual coordinate derivatives vanish. -/
theorem native_chartEnergy_zero_outside_tsupport (f : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) (hz : z ∉ tsupport f) :
    chartEnergy (extendUpper f) (z.re,z.im) = 0 := by
  have hf : ∀ᶠ w in 𝓝 z, f w = 0 :=
    (isClosed_tsupport.isOpen_compl.mem_nhds hz).mono
      (fun w hw => image_eq_zero_of_notMem_tsupport hw)
  have hc : Tendsto chartLift (𝓝 (z.re,z.im)) (𝓝 z) := by
    simpa only [chartLift_pair] using chartLift_continuousAt_positive z.im_pos
  have hg : extendUpper f =ᶠ[𝓝 (z.re,z.im)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hc.eventually hf,
      (isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos] with p hp hpos
    rw [extendUpper_chartLift _ p hpos]
    exact hp
  rw [chartEnergy,sliceDx_eq_of_eventuallyEq hg,sliceDy_eq_of_eventuallyEq hg]
  simp [sliceDx,sliceDy]

theorem native_chartEnergy_compact (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f) :
    HasCompactSupport (fun z : UpperHalfPlane => chartEnergy (extendUpper f) (z.re,z.im)) := by
  apply HasCompactSupport.of_support_subset_isCompact hfc
  intro z hz
  by_contra hout
  exact hz (native_chartEnergy_zero_outside_tsupport f z hout)

theorem native_mass_energy_restrict_support (f : UpperHalfPlane → ℂ)
    (K : Set UpperHalfPlane) (hs : tsupport f ⊆ K) :
    (∫ z in K, ‖f z‖^2 + chartEnergy (extendUpper f) (z.re,z.im)) =
      ∫ z : UpperHalfPlane, ‖f z‖^2 + chartEnergy (extendUpper f) (z.re,z.im) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hout : z ∉ tsupport f := fun h => hz (hs h)
  rw [image_eq_zero_of_notMem_tsupport hout,native_chartEnergy_zero_outside_tsupport f z hout]
  simp

end
end ImbalancedChen.Part3.PositiveRectangleNativeDerivativeEnergy20261026b
