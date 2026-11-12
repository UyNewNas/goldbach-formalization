import ImbalancedChen.Part3OriginalPositiveLowCosine
import ImbalancedChen.Part3OriginalPositiveStripDiagonal

/-! Pointwise projection of the actual compact test after subtraction of every
even holomorphic weight. Both changes in the cosine inversion are ordinary integrals. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStrip20261112
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveHolomorphicWeights20261112 (intJ moment)
open OriginalPositiveJacobiAnger20261112 (oddOrder)
open OriginalPositiveStripMoments20261112 (m sign coeff)
open OriginalPositiveStripDensity20261112 (tail tail_pos_bound tail_deriv h_formula h_even)
open OriginalPositiveCosineInversion20261112 (C cosine_inversion)
open OriginalPositiveLowCosine20261112 (weight weight_sum low_integral)
open OriginalPositiveQuarterContour20261112 (low high quarter)
open KCosineInversionSourceOnly (integral_even_eq_two_Ioi)
open private tendsto_cosh_atTop from ImbalancedChen.Part3ImaginaryKContourRectangle

def residual (ell : D4→ℤ) (Y q : ℝ) := spectralTest ell Y q-
  ∑' j : ℕ,2*(oddOrder j:ℂ)*moment (oddOrder j) (spectralTest ell Y)*intJ (oddOrder j) q

private def kcos (q w : ℝ) : ℂ := Real.cos (q*Real.cosh w)
private def spec (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (q s : ℝ) : ℂ :=
  (Real.cos (q*s):ℂ)*C ell hY s

private theorem kbound (q w : ℝ) : ‖kcos q w‖≤1 := by
  simpa [kcos,Real.norm_eq_abs] using Real.abs_cos_le_one (q*Real.cosh w)

private theorem hcint (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (q : ℝ) :
    Integrable (fun w : ℝ => h ell Y w*kcos q w) := by
  have hh : Integrable (h ell Y) := by
    simpa [OriginalPositiveStripContour20261112.wave] using hhat_L1 ell hY (ξ:=0) (by norm_num)
  exact hh.mul_bdd (by unfold kcos; fun_prop) (ae_of_all _ (kbound q))

private theorem scint (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (q : ℝ) :
    Integrable (spec ell hY q) :=
  (C ell hY).integrable.bdd_mul (by fun_prop) (ae_of_all _ fun s => by
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (q*s))

private theorem spec_cont (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (q : ℝ) : Continuous (spec ell hY q) :=
  (by fun_prop : Continuous (fun s : ℝ => (Real.cos (q*s):ℂ))).mul (C ell hY).continuous

private theorem coeff_exp (ell : D4→ℤ) (Y : ℝ) (j : ℕ) (w : ℝ) :
    weight ell Y j*sign j*(Real.exp (-(oddOrder j:ℝ)*w):ℂ)=
      -2*(coeff ell Y j*(-(oddOrder j:ℂ))^1*Complex.exp (-(oddOrder j:ℂ)*w)) := by
  rw [Complex.ofReal_exp]; dsimp only [coeff,weight]; push_cast; ring

private theorem upper_sum (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (q : ℝ) :
    HasSum (fun j => weight ell Y j*sign j*(high j q:ℂ))
      ((Real.pi:ℂ)*(∫ w in Ioi (0:ℝ),h ell Y w*kcos q w)-
        ∫ s in Ioi (1:ℝ),spec ell hY q s) := by
  let V := spec ell hY q
  let U := fun j (w : ℝ) => weight ell Y j*sign j*
    ((Real.exp (-(oddOrder j:ℝ)*w)*Real.cos (q*Real.cosh w):ℝ):ℂ)
  let Z := fun w : ℝ => -2*tail ell Y 1 w*kcos q w
  let W := fun w : ℝ => Real.sinh w • V (Real.cosh w)
  have ZW (w : ℝ) : Z w=(Real.pi:ℂ)*(h ell Y w*kcos q w)-W w := by
    dsimp only [Z,W,V,spec,kcos]
    rw [h_formula ell hY,Complex.real_smul]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
  have ie : IntegrableOn (fun w : ℝ => Real.exp (-w)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0
  have hb (j : ℕ) (w : ℝ) (hw : 0<w) : ‖U j w‖≤‖weight ell Y j‖*Real.exp (-w) := by
    have ho : 1≤(oddOrder j:ℝ) := by exact_mod_cast (show 1≤oddOrder j by dsimp [oddOrder]; omega)
    have e : Real.exp (-(oddOrder j:ℝ)*w)≤Real.exp (-w) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right ho hw.le])
    simp only [U,sign,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (by simpa using
      mul_le_mul e (Real.abs_cos_le_one (q*Real.cosh w)) (abs_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
  have su (w : ℝ) (hw : 0<w) : Summable (U · w) := Summable.of_norm_bounded
    ((weight_sum ell hY).mul_right (Real.exp (-w))) (fun j => hb j w hw)
  have us (w : ℝ) (hw : 0<w) : HasSum (U · w) (Z w) := by
    apply (su w hw).hasSum_iff.mpr
    dsimp only [Z,tail,U]
    rw [←tsum_mul_left,←tsum_mul_right]
    apply tsum_congr
    intro j
    push_cast
    rw [←coeff_exp]; dsimp only [kcos]; ring
  have me (j : ℕ) : Continuous (U j) := by dsimp only [U]; fun_prop
  have H := hasSum_integral_of_dominated_convergence (μ:=volume.restrict (Ioi (0:ℝ)))
    (F:=U) (f:=Z) (fun j w => ‖weight ell Y j‖*Real.exp (-w))
    (fun j => (me j).aestronglyMeasurable)
    (fun j => by filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw; exact hb j w hw)
    (ae_of_all _ fun _ => (weight_sum ell hY).mul_right _)
    (by simpa only [tsum_mul_right] using ie.const_mul (∑' j,‖weight ell Y j‖))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw; exact us w hw)
  have zi : IntegrableOn Z (Ioi 0) := by
    obtain ⟨K,hK,b⟩ := tail_pos_bound ell hY 1
    have tc : Continuous (fun w : ℝ => tail ell Y 1 w) :=
      continuous_iff_continuousAt.mpr fun w => (tail_deriv ell hY 1 (w:ℂ)).comp_ofReal.continuousAt
    apply (ie.const_mul (2*K)).mono' (by dsimp only [Z,kcos]; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    dsimp only [Z]; rw [norm_mul,norm_mul,norm_neg,Complex.norm_ofNat]
    calc
      _ ≤ (2*(K*Real.exp (-w)))*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (b w hw.le) (by norm_num)) (kbound q w)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hi := (hcint ell hY q).integrableOn (s:=Ioi (0:ℝ))
  have wi : IntegrableOn W (Ioi 0) := by
    apply ((hi.const_mul (Real.pi:ℂ)).sub zi).congr_fun _ measurableSet_Ioi
    intro w _; rw [ZW]; ring
  have sub := integral_deriv_smul_comp_Ioi (f:=Real.cosh) (f':=Real.sinh) (g:=V) (a:=(0:ℝ))
    Real.continuous_cosh.continuousOn tendsto_cosh_atTop (fun w _ => (Real.hasDerivAt_cosh w).hasDerivWithinAt)
    (spec_cont ell hY q).continuousOn (scint ell hY q).integrableOn
    (integrableOn_Ici_iff_integrableOn_Ioi.mpr wi)
  change (∫ w in Ioi (0:ℝ),W w)=_ at sub
  rw [Real.cosh_zero] at sub
  rw [←sub,←integral_const_mul,←integral_sub (hi.const_mul (Real.pi:ℂ)) wi,←funext ZW]
  apply H.congr_fun
  intro j
  rw [high,←integral_ofReal,←integral_const_mul]
  rfl

theorem original_projection (ell : D4→ℤ) {Y q : ℝ} (hY : 0<Y) (hq : 0≤q) :
    residual ell Y q=∫ w : ℝ,h ell Y w*(Real.cos (q*Real.cosh w):ℂ) := by
  let V := spec ell hY q
  let A := ∫ w in Ioi (0:ℝ),h ell Y w*kcos q w
  have split := intervalIntegral.integral_interval_add_Ioi
    ((scint ell hY q).integrableOn (s:=Ioi 0)) ((scint ell hY q).integrableOn (s:=Ioi 1))
  have inv := cosine_inversion ell hY hq
  change (∫ x in (0:ℝ)..1,V x)+(∫ x in Ioi (1:ℝ),V x)=∫ x in Ioi (0:ℝ),V x at split
  change (∫ x in Ioi (0:ℝ),V x)=(Real.pi/2:ℝ)*spectralTest ell Y q at inv
  have H := ((low_integral ell hY q).sub (upper_sum ell hY q)).div_const ((Real.pi/2:ℝ):ℂ)
  have sum : HasSum (fun j => 2*(oddOrder j:ℂ)*moment (oddOrder j) (spectralTest ell Y)*intJ (oddOrder j) q)
      (((∫ x in (0:ℝ)..1,V x)-((Real.pi:ℂ)*A-∫ x in Ioi (1:ℝ),V x))/((Real.pi/2:ℝ):ℂ)) := by
    apply H.congr_fun
    intro j
    rw [show weight ell Y j*(low j q:ℂ)-weight ell Y j*sign j*(high j q:ℂ)=
      weight ell Y j*((low j q:ℂ)-sign j*(high j q:ℂ)) by ring,←quarter j hq]
    dsimp only [weight,m]
    push_cast; field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
  have ev := integral_even_eq_two_Ioi (fun w : ℝ => h ell Y w*kcos q w) (hcint ell hY q)
    (fun w => by rw [h_even ell hY]; simp only [kcos,Real.cosh_neg])
  change residual ell Y q=∫ w : ℝ,h ell Y w*kcos q w
  rw [ev,residual,sum.tsum_eq]
  change _=2*A
  have e := split.trans inv
  have collected :
      ((∫ x in (0:ℝ)..1,V x)-((Real.pi:ℂ)*A-∫ x in Ioi (1:ℝ),V x))=
      ((Real.pi/2:ℝ):ℂ)*(spectralTest ell Y q-2*A) := by
    push_cast at e ⊢
    linear_combination e
  rw [collected,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (by positivity : Real.pi/2≠0))]
  ring

end ImbalancedChen.Part3.OriginalPositiveStrip20261112
end
