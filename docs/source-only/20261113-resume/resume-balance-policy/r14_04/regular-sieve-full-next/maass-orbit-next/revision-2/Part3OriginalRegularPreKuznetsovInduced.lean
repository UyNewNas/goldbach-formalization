import ImbalancedChen.Part3OriginalRegularPreKuznetsovOrbitL1
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Batteries.Tactic.OpenPrivate

/-! The integrated same-observation Bruhat transform of the exponential
seed. Polar and logarithmic changes are made on the absolute mass first. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovInduced20261113
open Set Filter MeasureTheory Complex
open scoped ENNReal Topology
open OriginalPositiveScalarGeometry20261112 (plane induced)
open OriginalRegularPreKuznetsovPolar20261113 (physical polar_density)
open OriginalRegularPreKuznetsovOrbitL120261113 (angleMeasure polarWave polar_integrable)
open OriginalRegularPreKuznetsovFourier20261113 (character)
open OriginalRegularPreKuznetsovAngle20261113 (angularWave angular)
open OriginalAbelOrbit (heights)
open OriginalAbelGaussian (dilation)
open private height_integral height_range dilation_deriv dilation_inj from ImbalancedChen.Part3OriginalAbelOrbit

private abbrev half : Set (ℝ×ℝ) := {z | 0<z.2}
private def raw (δ p r : ℝ) (z : ℝ×ℝ) :=
  half.indicator (fun w => plane (fun a b => physical δ r a*star (physical δ r b)) (p^2) w.1 w.2) z

private def mapped (δ p r : ℝ) (z : ℝ×ℝ) := z.1 • raw δ p r (polarCoord.symm z)

private def coeff (δ p : ℝ) := Real.pi^2*p^2*((2*Real.pi)^2*p^2)^δ

private def angularSlot (δ p r : ℝ) (ξ : ℝ) (θ : ℝ) : ℂ :=
  (coeff δ p:ℂ)*(Ioo (0:ℝ) Real.pi).indicator (polarWave δ (4*Real.pi*p) r ξ) θ

private abbrev angleFull : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)

private theorem upper_meas : MeasurableSet half := measurable_snd measurableSet_Ioi

private theorem raw_meas (δ p r : ℝ) : Measurable (raw δ p r) := by
  apply Measurable.indicator _ upper_meas
  unfold plane physical ActualUnitBandHeightSeeds20261112.modulation P3Period64NativeReconstructionSourceOnly.e
  fun_prop

private theorem mapped_meas (δ p r : ℝ) : Measurable (mapped δ p r) := by
  dsimp only [mapped]
  apply measurable_fst.smul
  refine (raw_meas δ p r).comp ?_
  simp only [polarCoord_symm_apply]; fun_prop

private theorem upper_chart {p : ℝ} (hp : 0<p) (δ r ξ : ℝ) {θ : ℝ}
    (hθ : θ∈Ioo (-Real.pi) Real.pi) :
    dilation (p^2) ξ • mapped δ p r (dilation (p^2) ξ, θ)=angularSlot δ p r ξ θ := by
  let R := p*Real.exp ξ
  have R0 : 0<R := mul_pos hp (Real.exp_pos _)
  have dR : dilation (p^2) ξ=R := by rw [dilation,Real.sqrt_sq hp.le]
  rw [dR,mapped,smul_smul]
  by_cases s : 0<θ
  · have ht : θ∈Ioo 0 Real.pi := ⟨s,hθ.2⟩
    have sin0 := Real.sin_pos_of_mem_Ioo ht
    have A : polarCoord.symm (R,θ)∈half := by
      change 0<(polarCoord.symm (R,θ)).2
      rw [polarCoord_symm_apply]; exact mul_pos R0 sin0
    rw [raw,indicator_of_mem A,polarCoord_symm_apply,←sq,angularSlot,indicator_of_mem ht]
    have E := polar_density hp ht δ r ξ
    change (R^2:ℝ) • plane _ _ (R*Real.cos θ) (R*Real.sin θ)=_ at E
    rw [E,coeff,polarWave]
    have powers : ((2*Real.pi)^2*(p^2*Real.sin θ^2))^δ=
        ((2*Real.pi)^2*p^2)^δ*Real.sin θ^(2*δ) := by
      rw [Real.rpow_mul sin0.le,Real.rpow_two,←Real.mul_rpow (by positivity) (sq_nonneg _)]
      congr 1;ring
    rw [powers];push_cast;ring
  · have ns : Real.sin θ≤0 := by
      have h := Real.sin_nonneg_of_mem_Icc (x:=-θ) ⟨neg_nonneg.mpr (le_of_not_gt s),by linarith [hθ.1]⟩
      rwa [Real.sin_neg,neg_nonneg] at h
    have A : polarCoord.symm (R,θ)∉half := by
      change ¬0<(polarCoord.symm (R,θ)).2
      rw [polarCoord_symm_apply]; exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos R0.le ns)
    simp [raw,A,angularSlot,indicator_of_notMem (show θ∉Ioo 0 Real.pi from fun h => s h.1)]

private theorem slot_int {p δ : ℝ} (hp : 0<p) (hδ : 0≤δ) (r : ℝ) :
    Integrable (Function.uncurry (angularSlot δ p r)) (volume.prod angleFull) := by
  let A := Ioo (0:ℝ) Real.pi
  let B := Ioo (-Real.pi) Real.pi
  let h := polar_integrable hδ (show 0<4*Real.pi*p by positivity) r
  let f := Function.uncurry (polarWave δ (4*Real.pi*p) r)
  have sub : A⊆B := fun _ ht => ⟨(neg_lt_zero.mpr Real.pi_pos).trans ht.1,ht.2⟩
  have E : ∀ z : ℝ×ℝ, Function.uncurry (angularSlot δ p r) z=
      ((univ: Set ℝ) ×ˢ A).indicator (fun p' => (coeff δ p:ℂ)*f p') z := by
    intro z
    by_cases hz : z.2∈A
    · simp [Function.uncurry,angularSlot,hz,A,f]
    · simp [Function.uncurry,angularSlot,hz,A,f]
  rw [funext E,integrable_indicator_iff (MeasurableSet.univ.prod measurableSet_Ioo)]
  change Integrable _ (((volume : Measure ℝ).prod (volume.restrict B)).restrict (univ ×ˢ A))
  rw [←Measure.prod_restrict,Measure.restrict_univ,Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr sub]
  exact h.const_mul (coeff δ p:ℂ)

private theorem chart_mass {p δ : ℝ} (hp : 0<p) (r : ℝ) :
    (∫⁻ z : ℝ×ℝ,‖raw δ p r z‖ₑ)=∫⁻ z : ℝ×ℝ,‖angularSlot δ p r z.1 z.2‖ₑ ∂volume.prod angleFull := by
  let F := mapped δ p r
  let G := angularSlot δ p r
  have coeffR (R : ℝ) (hr : 0<R) (θ : ℝ) :
      ENNReal.ofReal R*‖raw δ p r (polarCoord.symm (R,θ))‖ₑ=‖F (R,θ)‖ₑ := by
    simp only [F,mapped,enorm_smul,Real.enorm_eq_ofReal hr.le]
  have inv := lintegral_comp_polarCoord_symm (fun z => ‖raw δ p r z‖ₑ)
  have Fm := (mapped_meas δ p r).enorm
  have Gm : Measurable (fun z : ℝ×ℝ => ‖G z.1 z.2‖ₑ) := by
    have g : Measurable (fun z : ℝ×ℝ => G z.1 z.2) := by
      dsimp only [G,angularSlot]
      change Measurable (fun z : ℝ×ℝ => _*(if z.2∈Ioo 0 Real.pi then _ else _))
      unfold polarWave angularWave OriginalRegularPreKuznetsovAngle20261113.ray character
      fun_prop
    exact g.enorm
  rw [←inv]
  calc
    _ = ∫⁻ z in polarCoord.target,‖F z‖ₑ := by
      apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
      intro z hz; exact coeffR z.1 hz.1 z.2
    _ = ∫⁻ R ∈ Ioi (0:ℝ),∫⁻ θ,‖F (R,θ)‖ₑ ∂angleFull := by
      change (∫⁻ z in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,‖F z‖ₑ)=_
      rw [Measure.volume_eq_prod,←Measure.prod_restrict,lintegral_prod _ Fm.aemeasurable]
    _ = _ := by
      have J := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_univ
        (fun ξ _ => (dilation_deriv (p^2) ξ).hasDerivWithinAt) (dilation_inj (sq_pos_of_pos hp))
        (fun R => ∫⁻ θ,‖F (R,θ)‖ₑ ∂angleFull)
      rw [height_range (sq_pos_of_pos hp),setLIntegral_univ] at J
      rw [J,lintegral_prod _ Gm.aemeasurable]
      apply lintegral_congr; intro ξ
      have d := show 0<dilation (p^2) ξ by dsimp only [dilation]; positivity
      rw [abs_of_pos d,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo : MeasurableSet (Ioo (-Real.pi) Real.pi))] with θ ht
      rw [←upper_chart hp δ r ξ ht,enorm_smul,Real.enorm_eq_ofReal d.le]

private theorem slots_integral (δ p r ξ : ℝ) :
    (∫ θ,angularSlot δ p r ξ θ ∂angleFull)=(coeff δ p:ℂ)*∫ θ,polarWave δ (4*Real.pi*p) r ξ θ ∂angleMeasure := by
  simp only [angularSlot,integral_const_mul]
  congr 1
  change (∫ θ in Ioo (-Real.pi) Real.pi,(Ioo 0 Real.pi).indicator _ θ)=_
  rw [setIntegral_indicator measurableSet_Ioo]
  have s : Ioo (0:ℝ) Real.pi⊆Ioo (-Real.pi) Real.pi := fun _ h => ⟨(neg_lt_zero.mpr Real.pi_pos).trans h.1,h.2⟩
  simp only [angleMeasure,inter_eq_right.mpr s,inter_eq_left.mpr s]

/-- The original induced coefficient is the full-line Fourier transform
of the upper angular integral. The prefactor contains the entire q
normalization even when a positive δ regularization is retained. -/
theorem induced_exponential {p δ : ℝ} (hp : 0<p) (hδ : 0≤δ) (r : ℝ) :
    induced (fun a b => physical δ r a*star (physical δ r b)) (4*Real.pi*p)=
      ((Real.pi^2*p*((2*Real.pi)^2*p^2)^δ:ℝ):ℂ)*
        ∫ ξ : ℝ,∫ θ,polarWave δ (4*Real.pi*p) r ξ θ ∂angleMeasure := by
  let F := raw δ p r
  let P := mapped δ p r
  have sinteg := slot_int hp hδ r
  have fin : Integrable F := by
    refine ⟨(raw_meas δ p r).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_enorm,chart_mass hp r]
    exact sinteg.lintegral_lt_top
  have pinteg : IntegrableOn P polarCoord.target := by
    refine ⟨(mapped_meas δ p r).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have absfin := fin.lintegral_lt_top
    rw [←lintegral_comp_polarCoord_symm (fun z => ‖F z‖ₑ)] at absfin
    apply lt_of_eq_of_lt _ absfin
    apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
    intro z hz
    simp only [P,F,mapped,enorm_smul,Real.enorm_eq_ofReal hz.1.le]
  have calc1 : (∫ z : ℝ×ℝ,F z)=∫ R in Ioi (0:ℝ),∫ θ,P (R,θ) ∂angleFull := by
    rw [←integral_comp_polarCoord_symm F]
    change (∫ z in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,P z)=_
    exact setIntegral_prod P pinteg
  have rawVertical (x : ℝ) : (∫ y : ℝ,F (x,y))=
      ∫ y,plane (fun a b => physical δ r a*star (physical δ r b)) (p^2) x y ∂heights := by
    change (∫ y,(Ioi 0).indicator (plane _ (p^2) x) y)=_
    exact integral_indicator measurableSet_Ioi _
  have finprod : Integrable F ((volume:Measure ℝ).prod volume) := by rwa [←Measure.volume_eq_prod]
  have k : (4*Real.pi*p/(4*Real.pi))^2=p^2 := by field_simp [Real.pi_ne_zero]
  rw [induced,k]
  simp_rw [←rawVertical]
  rw [←integral_prod F finprod,←Measure.volume_eq_prod,calc1,
    height_integral (sq_pos_of_pos hp) (fun R => ∫ θ,P (R,θ) ∂angleFull)]
  have row (ξ : ℝ) : dilation (p^2) ξ • (∫ θ,P (dilation (p^2) ξ,θ) ∂angleFull)=
      (coeff δ p:ℂ)*∫ θ,polarWave δ (4*Real.pi*p) r ξ θ ∂angleMeasure := by
    rw [←integral_smul,←slots_integral]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo : MeasurableSet (Ioo (-Real.pi) Real.pi))] with θ ht
    exact upper_chart hp δ r ξ ht
  simp_rw [row,integral_const_mul]
  simp only [coeff,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat]
  field_simp [Complex.ofReal_ne_zero.mpr hp.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

theorem induced_boundary {u : ℝ} (hu : 0<u) (r : ℝ) :
    induced (fun a b => physical 0 r a*star (physical 0 r b)) u=
      ((Real.pi*u/4:ℝ):ℂ)*(∫ ξ : ℝ,character ξ r*angular (u*Real.cosh ξ)) := by
  let p := u/(4*Real.pi)
  have hp : 0<p := div_pos hu (mul_pos (by norm_num) Real.pi_pos)
  have scale : 4*Real.pi*p=u := by dsimp only [p];field_simp [Real.pi_ne_zero]
  have E := induced_exponential hp (show 0≤(0:ℝ) by norm_num) r
  rw [scale,Real.rpow_zero,mul_one] at E
  rw [E]
  have coef : Real.pi^2*p=Real.pi*u/4 := by dsimp only [p];field_simp [Real.pi_ne_zero] <;> ring
  rw [coef]
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [polarWave,mul_zero,Real.rpow_zero,Complex.ofReal_one,one_mul,integral_const_mul]
  rw [angular,intervalIntegral.integral_of_le Real.pi_pos.le,integral_Ioc_eq_integral_Ioo] <;> rfl

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovInduced20261113
end
