import ImbalancedChen.Part3ActualOppositeBruhatCoordinates
import ImbalancedChen.Part3ActualCompactBruhatKernel

/-! Absolute three-variable integrability of the original opposite-sign
test and of its two-probe hyperbolic coordinates. -/
namespace ImbalancedChen.Part3.ActualOppositeBruhatMass20261112

noncomputable section
open Set Filter MeasureTheory Complex
open ActualOppositeBruhatCoordinates20261112 ActualOppositeKProduct20261112
open ActualMarkedBruhatTest20261112 ActualCompactBruhatKernel20261025a
open ComplexOrderKBridgeSourceOnly ComplexOrderKPositiveLaplace20261025a
open CompactCuspGeometricFubini20261025a P3Period64NativeReconstructionSourceOnly (e)

abbrev grid : Measure (ℝ × ℝ × ℝ) := posMeasure.prod ((volume : Measure ℝ).prod posMeasure)

private theorem k_decay (ν : ℂ) {δ : ℝ} (hδ : 0<δ) :
    ∃ M : ℝ, 0≤M ∧ ∀ c : ℝ,δ≤c → ∀ v : ℝ,
      ‖complexOrderK ν (c*Real.cosh v)‖ ≤ M*Real.exp (-(δ/2)*Real.cosh v) := by
  let D := RealOrderKPositiveLaplace.tiltedCoshDensity ν.re (δ/2)
  have hD : Integrable D := RealOrderKPositiveLaplace.tiltedCoshDensity_integrable _ (half_pos hδ)
  have mD : 0≤∫ r,D r := integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨(∫ r,D r)/2,by positivity,?_⟩
  intro c hc v
  have hq := mul_pos (hδ.trans_le hc) (Real.cosh_pos v)
  let f := tiltedDensity ν (c*Real.cosh v)
  have hb (r : ℝ) : ‖f r‖ ≤ Real.exp (-(δ/2)*Real.cosh v)*D r := by
    simp only [f,D,tiltedDensity,Complex.norm_exp,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero,RealOrderKPositiveLaplace.tiltedCoshDensity,
      ← Real.exp_add,Real.exp_le_exp]
    have V := Real.one_le_cosh v
    have R := Real.one_le_cosh r
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (mul_nonneg (Real.cosh_pos v).le (Real.cosh_pos r).le),
      mul_nonneg hδ.le (mul_nonneg (sub_nonneg.mpr V) (Real.cosh_pos r).le),
      mul_nonneg hδ.le (mul_nonneg (sub_nonneg.mpr R) (Real.cosh_pos v).le)]
  have h := (norm_integral_le_integral_norm f).trans (integral_mono
    (tiltedDensity_integrable ν hq).norm (hD.const_mul _) hb)
  rw [show (∫ r,f r)=_ from tiltedDensity_integral ν hq,norm_mul,integral_const_mul] at h
  norm_num only [Complex.norm_ofNat] at h
  linarith

private theorem amp_bound {l a : ℝ} (hl : 0<l) (h : l≤a) :
    0≤amp a ∧ amp a≤(l*Real.sqrt l)⁻¹ := by
  have ha := hl.trans_le h
  have hs := Real.sqrt_pos.mpr ha
  have asq := Real.sq_sqrt ha.le
  have eqn : amp a=(a*Real.sqrt a)⁻¹ := by
    unfold amp
    field_simp [ha.ne',hs.ne'] <;> nlinarith
  rw [eqn]
  exact ⟨by positivity,inv_anti₀ (mul_pos hl (Real.sqrt_pos.mpr hl))
    (mul_le_mul h (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _) ha.le)⟩

theorem raw_measurable (ν : ℂ) (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hφ : Continuous φ) :
    Measurable (fun p : ℝ × ℝ × ℝ => raw ν ψ φ p.1 p.2.1 p.2.2) := by
  have hk := k_measurable (2*ν)
  unfold raw orbitTestKernel radialWeight e
  fun_prop

theorem trans_measurable (ν : ℂ) (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hφ : Continuous φ) :
    Measurable (fun p : ℝ × ℝ × ℝ => transformed ν ψ φ p.1 p.2.1 p.2.2) := by
  have hk := k_measurable (2*ν)
  unfold transformed amp oscillation
  fun_prop

theorem trans_integrable (ν : ℂ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun p : ℝ × ℝ × ℝ => transformed ν ψ φ p.1 p.2.1 p.2.2) grid := by
  obtain ⟨l,hl,L⟩ := radial_support_positive_floor ψ hcψ hpψ
  obtain ⟨m,hm,M⟩ := radial_support_positive_floor φ hcφ hpφ
  let δ := 4*Real.pi*Real.sqrt (l*m)
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,KC⟩ := k_decay (2*ν) hδ
  let A := (l*Real.sqrt l)⁻¹
  let B := (m*Real.sqrt m)⁻¹
  let g := fun v => Real.exp (-(δ/2)*Real.cosh v)
  have hg : Integrable g := by
    simpa only [g,RealOrderKPositiveLaplace.tiltedCoshDensity,zero_mul,add_zero] using
      RealOrderKPositiveLaplace.tiltedCoshDensity_integrable 0 (half_pos hδ)
  have U : Integrable (fun a => ‖ψ a‖) posMeasure := (hψ.norm.integrable_of_hasCompactSupport hcψ.norm).integrableOn
  have V : Integrable (fun b => ‖φ b‖) posMeasure := (hφ.norm.integrable_of_hasCompactSupport hcφ.norm).integrableOn
  apply ((U.mul_prod (hg.mul_prod V)).const_mul ((A*B/2)*C)).mono'
    (trans_measurable ν ψ φ hψ hφ).aestronglyMeasurable
  apply ae_of_all
  rintro ⟨a,v,b⟩
  change ‖transformed ν ψ φ a v b‖≤(A*B/2*C)*(‖ψ a‖*(g v*‖φ b‖))
  by_cases za : ψ a=0
  · simp [transformed,za]
  by_cases zb : φ b=0
  · simp [transformed,zb]
  have hA := amp_bound hl (L a za)
  have hB := amp_bound hm (M b zb)
  have sc : δ≤4*Real.pi*Real.sqrt (a*b) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul (L a za) (M b zb) hm.le (hl.trans_le (L a za)).le))
      (by positivity)
  have bound := KC _ sc v
  simp only [transformed,norm_mul,Complex.norm_real,Real.norm_of_nonneg (div_nonneg (mul_nonneg hA.1 hB.1) (by norm_num)),
    norm_oscillation,one_mul,norm_star]
  calc
    _ ≤ (A*B/2)*(‖ψ a‖*‖φ b‖)*(C*g v) := by gcongr <;> first | exact hA.2 | exact hB.2 | exact bound
    _ = _ := by ring

private theorem nested_mass (F : ℝ × ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p,F p ∂grid) = ∫⁻ a,∫⁻ x : ℝ,∫⁻ q,F (a,x,q) ∂posMeasure ∂volume ∂posMeasure := by
  rw [lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro a
  exact lintegral_prod _ (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable

theorem raw_integrable (ν : ℂ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun p : ℝ × ℝ × ℝ => raw ν ψ φ p.1 p.2.1 p.2.2) grid := by
  have mr := raw_measurable ν ψ φ hψ hφ
  have mt := trans_measurable ν ψ φ hψ hφ
  have H := (trans_integrable ν ψ φ hψ hcψ hpψ hφ hcφ hpφ).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm,nested_mass _ mt.enorm] at H
  refine ⟨mr.aestronglyMeasurable,hasFiniteIntegral_iff_enorm.mpr ?_⟩
  rw [nested_mass _ mr.enorm]
  refine lt_of_eq_of_lt (lintegral_congr_ae ?_) H
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact change_mass ν ψ φ ha

def reversal : (ℝ × ℝ × ℝ) ≃ᵐ (ℝ × ℝ × ℝ) :=
  MeasurableEquiv.prodAssoc.symm |>.trans MeasurableEquiv.prodComm |>.trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm)

theorem reversal_preserves : MeasurePreserving reversal grid grid := by
  have E := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc posMeasure volume posMeasure)
  exact ((MeasurePreserving.id posMeasure).prod (Measure.measurePreserving_swap (μ := posMeasure) (ν := volume))).comp
    ((Measure.measurePreserving_swap (μ := posMeasure.prod volume) (ν := posMeasure)).comp E)

theorem nested (F : ℝ × ℝ × ℝ → ℂ) (hF : Integrable F grid) :
    (∫ p,F p ∂grid) = ∫ a,∫ x : ℝ,∫ q,F (a,x,q) ∂posMeasure ∂volume ∂posMeasure := by
  rw [integral_prod _ hF]
  apply integral_congr_ae
  filter_upwards [hF.prod_right_ae] with a ha
  exact integral_prod _ ha

end
end ImbalancedChen.Part3.ActualOppositeBruhatMass20261112
