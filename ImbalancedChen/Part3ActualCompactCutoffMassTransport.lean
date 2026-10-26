import ImbalancedChen.Part3GenuineWeakCutoffIMS
import ImbalancedChen.Part3ActualPullbackLocalH1Transfer

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The mass in ordinary-coordinate weak IMS is EXACTLY canonical hyperbolic
mass of the original Gamma orbit pullback. The genuine bounded potential
localization equals y^-2 times the localized input on the cutoff support;
both ordinary and canonical mass integrands are independently L1.
-/
namespace ImbalancedChen.Part3.ActualCompactCutoffMassTransport20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a
open GenuineWeakCutoffIMS20261026b
open ActualPullbackLocalH1Transfer20261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CompactDefectMollifier20261026a Gamma0SmoothedPotentialL2Budget20261026a
open Gamma0CompactQuotientLocalLp20261025a
open CanonicalPlanarL2UnitarySourceOnly UpperHalfPlaneHyperbolicMeasure20261024z
open CanonicalTensorHyperbolicLaplacianForm20261024z

def heightPotential (p : Plane) : ℝ := (p.2⁻¹)^2

theorem actual_localized_mass_coefficient (N : ℕ) [NeZero N]
    (K : Set UpperHalfPlane) (B a : ℝ) (f : QuotientL2 N) (p : Plane)
    (hp : a ≤ p.2) :
    localizedPotential N K B a f p =
      (heightPotential p : ℂ) * localizedPlane N K B f p := by
  simp only [localizedPotential,cappedPotential,heightPotential,max_eq_right hp,Complex.real_smul]

/-- Canonical y^-2 density transport, retaining the RAW orbit pullback.
No quotient-form gradient or global ordinary-L2 claim is used. -/
theorem raw_cutoff_mass_transport (N : ℕ) (f : QuotientL2 N) (χ : Plane → ℝ) :
    (∫ p : Plane, (χ p)^2 * heightPotential p * ‖actualPlanePullback N f p‖^2) =
      ∫ z : UpperHalfPlane, (χ (chartMap z))^2 * ‖f (orbitProjection N z)‖^2 := by
  symm
  have hvol : (volume : Measure UpperHalfPlane) =
      coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞)) :=
    UpperHalfPlane.volume_def
  calc
    _ = ∫ z : UpperHalfPlane,
        (z.im⁻¹)^2 * ((χ (chartMap z))^2 * ‖f (orbitProjection N z)‖^2) ∂coordinateMeasure := by
      rw [hvol,integral_withDensity_eq_integral_smul upperDensityNN_measurable]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        rw [upperDensityNN_eq_chartWeight]
        rfl
    _ = ∫ p in upperChart, (χ p)^2 * heightPotential p * ‖actualPlanePullback N f p‖^2 := by
      symm
      rw [← map_coordinateMeasure,chartMap_measurableEmbedding.integral_map]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        rw [actualPlanePullback_at_upper]
        dsimp [heightPotential,chartMap]
        ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : actualPlanePullback N f p = 0 := by
        simp only [actualPlanePullback,dif_neg hp]
      rw [hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero]

/-- Compact-cutoff mass on the original Gamma pullback has genuine L1
meaning on BOTH sides of the density transport identity. The support
preimage in K is a geometric input, not a spectral or energy estimate. -/
theorem actual_compact_cutoff_mass_integrable (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (f : QuotientL2 N)
    {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχK : ∀ p ∈ tsupport χ, ∃ z ∈ K, chartMap z = p) :
    Integrable (fun p : Plane => (χ p)^2 * heightPotential p * ‖actualPlanePullback N f p‖^2) volume ∧
    Integrable (fun z : UpperHalfPlane => (χ (chartMap z))^2 * ‖f (orbitProjection N z)‖^2) volume := by
  have hF := localizedPlane_memLp N hK hB f
  have hm := localizedPotential_memLp N hK hB ha f
  have hcoeff : ∀ p ∈ tsupport χ, localizedPotential N K B a f p =
      (heightPotential p : ℂ) * localizedPlane N K B f p := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := hχK p hp
    exact actual_localized_mass_coefficient N K B a f _ (hlower z hz)
  have hordinary := (weak_IMS_energy_integrable (localizedPlane N K B f)
    (localizedPotential N K B a f) heightPotential χ hF hm 0 0 hχ hχc hcoeff).2.1
  have heq (p : Plane) (hp : p ∈ tsupport χ) :
      localizedPlane N K B f p = actualPlanePullback N f p := by
    obtain ⟨z,hz,rfl⟩ := hχK p hp
    rw [localizedPlane_at_upper N hbound f z,actualPlanePullback_at_upper]
    simp only [compactPullback,indicator_of_mem hz]
  have hraw : Integrable (fun p : Plane => (χ p)^2 * heightPotential p * ‖actualPlanePullback N f p‖^2) volume :=
    hordinary.congr (Eventually.of_forall fun p => by
      by_cases hp : p ∈ tsupport χ
      · rw [heq p hp]
      · have hz := image_eq_zero_of_notMem_tsupport hp
        simp only [hz,zero_pow (by norm_num : 2 ≠ 0),zero_mul])
  let A : UpperHalfPlane → ℂ := fun z => (χ (chartMap z) : ℂ)
  have hA : Continuous A := Complex.continuous_ofReal.comp
    (hχ.continuous.comp (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im))
  have hAs : Function.support A ⊆ K := by
    intro z hz
    have hp : chartMap z ∈ tsupport χ := subset_closure (by
      intro hzero
      exact hz (by simp only [A,hzero,Complex.ofReal_zero]))
    obtain ⟨w,hw,hwp⟩ := hχK _ hp
    have hwz : w = z := chartMap_measurableEmbedding.injective hwp
    simpa only [hwz] using hw
  have hAc : HasCompactSupport A := HasCompactSupport.of_support_subset_isCompact hK hAs
  obtain ⟨C,hC⟩ := hAc.exists_bound_of_continuous hA
  have hq := quotientLp_pullback_memLp N hK f
  have hproduct : MemLp (fun z : UpperHalfPlane => A z * f (orbitProjection N z)) 2
      ((volume : Measure UpperHalfPlane).restrict K) := by
    apply hq.of_le_mul (hA.aestronglyMeasurable.restrict.mul hq.aestronglyMeasurable)
    exact Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)
  have hglobal := (memLp_indicator_iff_restrict hK.measurableSet).2 hproduct
  have hind : K.indicator (fun z : UpperHalfPlane => A z * f (orbitProjection N z)) =
      (fun z : UpperHalfPlane => A z * f (orbitProjection N z)) := by
    funext z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      have hzero : A z = 0 := notMem_support.mp (fun h => hz (hAs h))
      simp only [hzero,zero_mul]
  rw [hind] at hglobal
  have hcanonical := (memLp_two_iff_integrable_sq_norm hglobal.aestronglyMeasurable).mp hglobal
  refine ⟨hraw,hcanonical.congr (Eventually.of_forall fun z => ?_)⟩
  simp only [A,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]

end
end ImbalancedChen.Part3.ActualCompactCutoffMassTransport20261026b
