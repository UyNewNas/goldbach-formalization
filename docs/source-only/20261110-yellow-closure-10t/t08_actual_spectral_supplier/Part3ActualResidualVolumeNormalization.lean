import ImbalancedChen.Part3ActualCuspResidualMultiplicity
import ImbalancedChen.Part3ActualHighStripCircleMeasure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! Exact calibration of the common residue to the reciprocal physical
quotient mass. The modular cell is measured in the same pushforward
of dx dy/y² used by the actual Poincaré and Hilbert-space pairings. -/
namespace ImbalancedChen.Part3.ActualResidualVolumeNormalization20261110

noncomputable section
open Set Filter Topology MeasureTheory Real UpperHalfPlane Complex
open scoped MatrixGroups UpperHalfPlane ENNReal
open ActualHighStripCircleMeasure20261026b CanonicalPlanarL2UnitarySourceOnly
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeightedCoordinateL220261024zz
open ModularFundamentalFiniteMeasure20261024z Gamma0ActualConstantMode20261025a
open Gamma0QuotientCellPushforward20261025a ActualCharacterCuspExpansion20261110
open ActualNativeResidualChannel20261110 ActualCuspResidualMultiplicity20261110
open ActualCriticalScatteringEntry20261110 ActualYoungCriticalCusps20261110

private def cut (x : ℝ) := Real.sqrt (1-x^2)
private def base := Icc (-(1/2 : ℝ)) (1/2)
private def region : Set (ℝ × ℝ) := {p | p.1 ∈ base ∧ cut p.1 ≤ p.2}

private theorem cut_cont : Continuous cut := Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
private theorem cut_pos {x : ℝ} (hx : x ∈ base) : 0 < cut x := by
  apply Real.sqrt_pos.mpr
  have h := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
  nlinarith

private theorem region_meas : MeasurableSet region :=
  (measurableSet_Icc.preimage measurable_fst).inter ((isClosed_le (cut_cont.comp continuous_fst) continuous_snd).measurableSet)

private theorem original_region : chartMap ⁻¹' region = modularFD := by
  ext z
  change (z.re ∈ base ∧ cut z.re ≤ z.im) ↔ (1 ≤ Complex.normSq (z : ℂ) ∧ |z.re| ≤ 1/2)
  rw [Complex.normSq_apply,abs_le,cut,Real.sqrt_le_iff]
  change ((-(1/2 : ℝ) ≤ z.re ∧ z.re ≤ 1/2) ∧ 0 ≤ z.im ∧ 1-z.re^2 ≤ z.im^2) ↔ _
  constructor
  · rintro ⟨hx,_,hy⟩
    exact ⟨by nlinarith,hx⟩
  · rintro ⟨hy,hx⟩
    exact ⟨hx,z.im_pos.le,by nlinarith⟩

private theorem vertical_mass {a : ℝ} (ha : 0 < a) :
    verticalWeightedMeasure (Ici a) = ENNReal.ofReal a⁻¹ := by
  have hfun {y : ℝ} (hy : 0 < y) : y^(-2 : ℝ) = (y⁻¹)^2 := by
    calc
      _ = (y^(2 : ℝ))⁻¹ := Real.rpow_neg hy.le 2
      _ = (y^2)⁻¹ := by norm_cast
      _ = _ := (inv_pow y 2).symm
  have hi : IntegrableOn (fun y : ℝ => (y⁻¹)^2) (Ioi a) := by
    apply (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha).congr_fun _ measurableSet_Ioi
    exact fun y hy => hfun (ha.trans hy)
  have hval : (∫ y in Ioi a, (y⁻¹)^2) = a⁻¹ := by
    calc
      _ = ∫ y in Ioi a, y^(-2 : ℝ) := setIntegral_congr_fun measurableSet_Ioi
        (fun y hy => (hfun (ha.trans hy)).symm)
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
        norm_num [Real.rpow_neg_one]
  have hs : Ici a ∩ Ioi (0 : ℝ) = Ici a := inter_eq_left.mpr (fun y hy => ha.trans_le hy)
  rw [verticalWeightedMeasure,Measure.withDensity_apply _ measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,
    hs,← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := a) (μ := (volume : Measure ℝ)))]
  have hW : (fun y : ℝ => (verticalWeight y : ℝ≥0∞)) = fun y => ENNReal.ofReal ((y⁻¹)^2) :=
    funext (fun y => by simpa only [verticalWeight] using (ENNReal.ofReal_coe_nnreal (p := verticalWeight y)).symm)
  rw [hW,← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun y => sq_nonneg _)),hval]

private theorem horizontal_integral : (∫ x in base,(cut x)⁻¹) = Real.pi/3 := by
  have hle : -(1/2 : ℝ) ≤ 1/2 := by norm_num
  have H : ContinuousOn (fun x : ℝ => (cut x)⁻¹) base := cut_cont.continuousOn.inv₀ (fun _ hx => (cut_pos hx).ne')
  have hA : Real.arcsin (1/2) = Real.pi/6 := by
    rw [← Real.sin_pi_div_six,Real.arcsin_sin] <;> linarith [Real.pi_pos]
  rw [base,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hle]
  have J : (∫ x in (-(1/2 : ℝ))..(1/2), (cut x)⁻¹) =
      Real.arcsin (1/2)-Real.arcsin (-(1/2)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle Real.continuous_arcsin.continuousOn
    · intro x hx
      simpa only [cut,one_div] using Real.hasDerivAt_arcsin (x := x) (by linarith [hx.1]) (by linarith [hx.2])
    · exact H.intervalIntegrable_of_Icc hle
  rw [J,Real.arcsin_neg,hA]
  ring

/-- Actual area of Mathlib's closed modular cell under the native upper
half-plane volume, with the geometric boundary included. -/
theorem modular_cell_volume : (volume : Measure ℍ) modularFD = ENNReal.ofReal (Real.pi/3) := by
  classical
  letI : SigmaFinite verticalWeightedMeasure := by unfold verticalWeightedMeasure; infer_instance
  have hs (x : ℝ) : Prod.mk x ⁻¹' region = if x ∈ base then Ici (cut x) else ∅ := by
    classical
    by_cases h : x ∈ base <;> ext y <;> simp [region,h]
  have hfun : (fun x : ℝ => verticalWeightedMeasure (Prod.mk x ⁻¹' region)) =
      base.indicator (fun x : ℝ => ENNReal.ofReal (cut x)⁻¹) := by
    classical
    funext x
    rw [hs]
    by_cases h : x ∈ base <;> simp [h,vertical_mass,cut_pos]
  have hi : IntegrableOn (fun x : ℝ => (cut x)⁻¹) base := ContinuousOn.integrableOn_compact isCompact_Icc
    (cut_cont.continuousOn.inv₀ (fun _ hx => (cut_pos hx).ne'))
  have hpos : 0 ≤ᵐ[(volume : Measure ℝ).restrict base] (fun x : ℝ => (cut x)⁻¹) :=
    Eventually.of_forall (fun x => inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [← original_region,← Measure.map_apply chartMap_measurableEmbedding.measurable region_meas,
    canonical_chart_map_measure,chartMeasure_eq_product,Measure.prod_apply region_meas,hfun,
    lintegral_indicator (show MeasurableSet base from measurableSet_Icc),
    ← ofReal_integral_eq_lintegral_ofReal hi hpos,horizontal_integral]

theorem quotient_volume (N : ℕ) [NeZero N] :
    actualVolume N = ((CongruenceSubgroup.Gamma0 N).index : ℝ)*(Real.pi/3) := by
  rw [actualVolume,Measure.real,quotient_mass_exact,modular_cell_volume,ENNReal.toReal_mul,
    ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity)]

/-- The actual ordinary Eisenstein and every scattering entry have
residue 1/vol of this exact quotient under its original spatial measure. -/
theorem native_residue_inverse_volume (N : ℕ) [NeZero N] (a : NativeCusps N) :
    nativeResidue N a = ((actualVolume N : ℝ) : ℂ)⁻¹ := by
  rw [native_residue_index,quotient_volume]
  push_cast
  have hi : ((CongruenceSubgroup.Gamma0 N).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (CongruenceSubgroup.Gamma0 N).index_ne_zero_of_finite
  field_simp [hi,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

theorem native_pole (N : ℕ) [NeZero N] (a : NativeCusps N) (z : ℍ) :
    Tendsto (fun s : ℂ => (s-1)*cuspFamily N a s z) (𝓝[≠] 1) (𝓝 (((actualVolume N : ℝ) : ℂ)⁻¹)) := by
  rw [← native_residue_inverse_volume N a]
  exact native_point_residue N a z

theorem entry_pole (N : ℕ) [NeZero N] (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Tendsto (fun s : ℂ => (s-1)*continuedEntry N (NeZero.pos N) g h s)
      (𝓝[≠] 1) (𝓝 (((actualVolume N : ℝ) : ℂ)⁻¹)) := by
  rw [← native_residue_inverse_volume N (nativeFrameOrbit N g)]
  exact scattering_entry_residue N g h

end
end ImbalancedChen.Part3.ActualResidualVolumeNormalization20261110
