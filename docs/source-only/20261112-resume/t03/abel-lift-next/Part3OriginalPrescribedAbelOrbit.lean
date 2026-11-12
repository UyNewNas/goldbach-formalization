import ImbalancedChen.Part3OriginalAbelOrbit

/-! Abel inversion at each positive manuscript argument, before any
summation over marks, moduli or spectral parameters. -/
namespace ImbalancedChen.Part3.OriginalPrescribedAbelOrbit20261112
noncomputable section
open Set MeasureTheory Complex
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalAbelKernel OriginalAbelGaussian OriginalPrescribedAbelProfile OriginalAbelOrbit
open OriginalPrescribedAbelLift20261112

private def slopeOf (k p : ℝ) := Real.sqrt ((k-p)/p)
private def jac (k p : ℝ) := k/(2*p*Real.sqrt p*Real.sqrt (k-p))

private lemma square_slope {k p : ℝ} (hp : p∈Ioo 0 k) : slopeOf k p^2=(k-p)/p :=
  Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hp.2.le) hp.1.le)

private lemma slope_root {k p : ℝ} (hp : p∈Ioo 0 k) :
    slopeOf k p=Real.sqrt (k-p)/Real.sqrt p :=
  Real.sqrt_div (sub_nonneg.mpr hp.2.le) p

private lemma p_slope {k p : ℝ} (hp : p∈Ioo 0 k) : productAt k (slopeOf k p)=p := by
  rw [productAt,square_slope hp]; field_simp [hp.1.ne', (hp.1.trans hp.2).ne']; ring

private lemma slope_range {k : ℝ} (hk : 0<k) :
    slopeOf k '' Ioo 0 k=Ioi 0 := by
  ext s
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact Real.sqrt_pos.mpr (div_pos (sub_pos.mpr hp.2) hp.1)
  · intro hs
    let d := 1+s^2
    have hd : 1<d := by dsimp [d]; nlinarith [sq_pos_of_pos hs]
    have hd0 := zero_lt_one.trans hd
    have hp : k/d∈Ioo 0 k := ⟨div_pos hk hd0,(div_lt_self hk hd)⟩
    refine ⟨k/d,hp,?_⟩
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hs.le).mp
    rw [square_slope hp]; dsimp [d] at *
    field_simp [hk.ne',hd0.ne']; ring

private lemma slope_deriv {k p : ℝ} (hp : p∈Ioo 0 k) :
    HasDerivAt (slopeOf k) (-(jac k p)) p := by
  have he := (sub_pos.mpr hp.2)
  have hh : 0<(k-p)/p := div_pos he hp.1
  have d := (Real.hasDerivAt_sqrt hh.ne').comp p
    (((hasDerivAt_id p).const_sub k).div (hasDerivAt_id p) hp.1.ne')
  convert d using 1
  dsimp [jac]
  rw [Real.sqrt_div he.le]
  field_simp [hp.1.ne',(Real.sqrt_pos.mpr hp.1).ne',(Real.sqrt_pos.mpr he).ne']
  nlinarith [Real.sq_sqrt hp.1.le]

private lemma jac_value (ell : D4→ℤ) (Y : ℝ) {k p : ℝ} (hp : p∈Ioo 0 k) :
    (jac k p) • (h ell Y p * (Real.exp (-p*slopeOf k p^2):ℝ)) =
      (k/2:ℝ) • (K (k-p) • f ell Y p) := by
  have r := Real.sqrt_pos.mpr hp.1
  have t := Real.sqrt_pos.mpr (sub_pos.mpr hp.2)
  rw [square_slope hp,show -p*((k-p)/p)= -(k-p) by field_simp [hp.1.ne']]
  simp only [h,jac,K,if_pos (sub_pos.mpr hp.2),Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_div,Complex.ofReal_ofNat]
  field_simp [Complex.ofReal_ne_zero.mpr hp.1.ne',Complex.ofReal_ne_zero.mpr r.ne',
    Complex.ofReal_ne_zero.mpr t.ne']; ring

private theorem signed_slopes (ell : D4→ℤ) {Y k : ℝ} (hY : 0<Y) (hk : 0<k) :
    (∫s:ℝ,h ell Y (productAt k s)*(Real.exp (-(productAt k s)*s^2):ℝ))=
      k • A (f ell Y) k := by
  let J := fun s:ℝ => h ell Y (productAt k s)*(Real.exp (-(productAt k s)*s^2):ℝ)
  have negJ (s : ℝ) : J (-s)=J s := by simp [J,productAt]
  have Jc : Continuous J := by
    have fc := (f_smooth ell hY).continuous
    dsimp [J,productAt,h]; fun_prop
  have Js : HasCompactSupport J := (amp_compact ell hY hk).mul_right
  have Ji : Integrable J := Jc.integrable_of_hasCompactSupport Js
  have half := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun p hp => (slope_deriv hp).hasDerivWithinAt)
    (fun a ha b hb he => (p_slope ha).symm.trans ((congrArg (productAt k) he).trans (p_slope hb))) J
  rw [slope_range hk] at half
  have cut : (∫p:ℝ,K (k-p) • f ell Y p)=∫p in Ioo (0:ℝ) k,K (k-p) • f ell Y p := by
    rw [←integral_indicator measurableSet_Ioo]
    apply integral_congr_ae; filter_upwards with p
    by_cases hp : p∈Ioo 0 k
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp]
      rcases not_and_or.mp hp with h0|h1
      · have z := f_jet_below ell hY 0 ((le_of_not_gt h0).trans (lo_pos hY).le)
        simp only [iteratedDeriv_zero] at z; rw [z,smul_zero]
      · have h : ¬0<k-p := not_lt.mpr (sub_nonpos.mpr (le_of_not_gt h1))
        simp [K,h]
  have pos : (∫s in Ioi (0:ℝ),J s)=(k/2:ℝ) • A (f ell Y) k := by
    rw [half,A,convolution_lsmul_swap,cut,←integral_smul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro p hp
    have hp0 : 0<p := hp.1
    have hkp := sub_pos.mpr hp.2
    dsimp [J]; rw [p_slope hp,abs_neg,abs_of_pos (by dsimp [jac]; positivity : 0<jac k p)]
    exact jac_value ell Y hp
  change (∫s:ℝ,J s)=_
  calc
    _ = (∫s in Iic (0:ℝ),J s) + (∫s in Ioi (0:ℝ),J s) :=
      (intervalIntegral.integral_Iic_add_Ioi Ji.integrableOn Ji.integrableOn).symm
    _ = (2:ℝ) • (∫s in Ioi (0:ℝ),J s) := by
      have n := integral_comp_neg_Ioi (0:ℝ) J
      simp_rw [negJ,neg_zero] at n
      rw [←n,Complex.real_smul]; push_cast; ring
    _ = _ := by rw [pos,smul_smul,show (2:ℝ)*(k/2)=k by ring]

/-- Every original positive argument, including both support endpoints. -/
theorem prescribed (ell : D4→ℤ) {Y q : ℝ} (hY : 0<Y) (hq : 0<q) :
    induced (H_ab ell Y) q=spectralTest ell Y q := by
  let k := (q/(4*Real.pi))^2
  have t : 0<q/(4*Real.pi) := by positivity
  have hk : 0<k := sq_pos_of_pos t
  have sq : Real.sqrt k=q/(4*Real.pi) := Real.sqrt_sq t.le
  have Q : 4*Real.pi*Real.sqrt k=q := by rw [sq]; field_simp [Real.pi_ne_zero]
  rw [induced,orbit_to_slope ell hY hk,signed_slopes ell hY hk,inverse_exact ell hY k,F,Q]
  change _ • (k • (spectralTest ell Y q/(Real.sqrt k:ℂ)))=_
  rw [smul_smul,sq]; dsimp [k]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hq.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]; ring

end
end ImbalancedChen.Part3.OriginalPrescribedAbelOrbit20261112
