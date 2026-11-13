import ImbalancedChen.Part3OriginalPositiveScalarGeometry
import ImbalancedChen.Part3OriginalPositiveOrbitResponse

/-! The sign changes only the phase in the two positive-height Jacobians.
The scale and logarithmic substitutions are those already supplied for the
original orbit. Finite absolute mass here is proved at each actual packet. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
open Set Filter MeasureTheory Complex
open scoped Topology BigOperators
open P3Period64NativeReconstructionSourceOnly (e norm_e)
open RadialSchrodingerL2Form20261025a (RadialTest)
open OriginalPositiveHeightTest20261112 (height height_pos)
open ActualPositiveScalarPacket20261112 (test_radius)
open OriginalAbelGaussian (productAt dilation coordinate_identity)
open OriginalAbelOrbit (heights)
open private height_integral height_range dilation_deriv dilation_inj linear_integral x_range
  from ImbalancedChen.Part3OriginalAbelOrbit

private def cyl (H : ℝ→ℝ→ℂ) (k s a : ℝ) : ℂ :=
  a⁻¹ • (H a (productAt k s/a)*e ((a+productAt k s/a)*s))

def amp (η : RadialTest) (R k s : ℝ) := (Real.sqrt (productAt k s):ℂ)*η.function (Real.log (productAt k s)+R)

private def expr (H : RadialTest) (k s w : ℝ) :=
  H.function w*e (2*(Real.sqrt (productAt k s)*s)*Real.cosh w)

private theorem slope_change (H : ℝ→ℝ→ℂ) (k s : ℝ) {a : ℝ} (ha : 0<a) :
    a • plane H k (a*s) a=cyl H k s a := by
  have dn : (a*s)^2+a^2=a^2*(1+s^2) := by ring
  have sq : 1+s^2≠0 := by positivity
  have b : k*a/((a*s)^2+a^2)=productAt k s/a := by
    rw [dn]; dsimp [productAt]; field_simp [ha.ne',sq]; ring
  have ph : a*s+k*(a*s)/((a*s)^2+a^2)=(a+productAt k s/a)*s := by
    rw [dn]; dsimp [productAt]; field_simp [ha.ne',sq]; ring
  simp only [plane,cyl,b,ph,smul_smul]; congr 1; field_simp [ha.ne']

private theorem chart_value (η H : RadialTest) (R : ℝ) {k : ℝ} (hk : 0<k) (s w : ℝ) :
    let p := productAt k s
    let a := dilation p w
    a • cyl (height η H R) k s a=amp η R k s*expr H k s w := by
  let p := productAt k s
  have hp : 0<p := by dsimp [p,productAt]; positivity
  obtain ⟨ha,hb,hab,hw,_⟩ := coordinate_identity hp w
  have ratio : (Real.log (dilation p w)-Real.log (p/dilation p w))/2=w := by
    simpa only [Real.log_div ha.ne' hb.ne'] using hw
  have sum : dilation p w+p/dilation p w=2*Real.sqrt p*Real.cosh w := by
    have inv : p/dilation p w=Real.sqrt p*Real.exp (-w) := by
      unfold dilation; rw [Real.exp_neg]
      field_simp [(Real.sqrt_pos.mpr hp).ne',(Real.exp_pos w).ne']; nlinarith [Real.sq_sqrt hp.le]
    rw [inv,dilation,Real.cosh_eq]; ring
  dsimp only
  rw [cyl,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,height_pos η H R ha hb,hab,ratio,sum]
  dsimp only [amp,expr,p]
  rw [show 2*Real.sqrt (productAt k s)*Real.cosh w*s=2*(Real.sqrt (productAt k s)*s)*Real.cosh w by ring]
  ring

private theorem amp_compact (η : RadialTest) (R : ℝ) {k : ℝ} (hk : 0<k) :
    HasCompactSupport (amp η R k) := by
  obtain ⟨S,s0,sup⟩ := test_radius η
  let lo := Real.exp (-S-R)
  have pos : 0<lo := Real.exp_pos _
  let A := 1+k/lo
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-A) A))
  intro s nz
  have hp : 0<productAt k s := by dsimp [productAt]; positivity
  have L := (abs_le.mp (sup _ (right_ne_zero_of_mul nz))).1
  have l : lo≤productAt k s := by rw [←Real.exp_log hp]; apply Real.exp_le_exp.mpr; linarith
  have sq := (le_div_iff₀ (show 0<1+s^2 by positivity)).mp l
  have S2 : s^2≤k/lo := (le_div_iff₀ pos).mpr (by nlinarith)
  apply abs_le.mp
  dsimp only [A]
  nlinarith [sq_abs s,sq_nonneg (|s|-1/2),div_nonneg hk.le pos.le]

private theorem amp_cont (η : RadialTest) (R : ℝ) {k : ℝ} (hk : 0<k) :
    Continuous (amp η R k) := by
  have C : Continuous (productAt k) := by dsimp [productAt]; fun_prop (disch := positivity)
  have L := C.log (fun s => by dsimp [productAt]; positivity)
  exact (Complex.continuous_ofReal.comp C.sqrt).mul (η.smooth.continuous.comp (L.add_const R))

private theorem val_integrable (H : RadialTest) (k s : ℝ) : Integrable (expr H k s) := by
  apply (H.smooth.continuous.integrable_of_hasCompactSupport H.compact).norm.mono'
    ((H.smooth.continuous.mul (by unfold e; fun_prop)).aestronglyMeasurable)
  exact ae_of_all _ fun w => by simp [expr,norm_mul,norm_e]

private theorem cylinder_integrable (η H : RadialTest) (R : ℝ) {k : ℝ} (hk : 0<k) :
    Integrable (Function.uncurry (cyl (height η H R) k)) (volume.prod heights) := by
  have M : Measurable (Function.uncurry (cyl (height η H R) k)) := by
    unfold cyl height OriginalPositiveHeightTest20261112.logHeight Function.uncurry productAt e
    fun_prop (disch := first | exact η.smooth.continuous.measurable | exact H.smooth.continuous.measurable)
  apply (integrable_prod_iff M.aestronglyMeasurable).mpr
  have hp (s : ℝ) : 0<productAt k s := by dsimp [productAt]; positivity
  constructor
  · exact ae_of_all _ fun s => by
      have J := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_univ
        (fun w _ => (dilation_deriv (productAt k s) w).hasDerivWithinAt)
        (dilation_inj (hp s)) (cyl (height η H R) k s)
      rw [height_range (hp s),integrableOn_univ] at J
      apply J.mpr
      apply ((val_integrable H k s).const_mul (amp η R k s)).congr
      exact ae_of_all _ fun w => by
        rw [abs_of_pos (show 0<dilation (productAt k s) w by dsimp [dilation]; positivity),chart_value η H R hk]
  · have A := (amp_cont η R hk).norm.integrable_of_hasCompactSupport (amp_compact η R hk).norm
    apply (A.mul_const (∫w : ℝ,‖H.function w‖)).congr
    exact ae_of_all _ fun s => by
      rw [height_integral (hp s),←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun w => by
        have pos : 0<dilation (productAt k s) w := by dsimp [dilation]; positivity
        simpa only [norm_smul,Real.norm_of_nonneg pos.le,norm_mul,expr,norm_e,mul_one,smul_eq_mul]
          using (congrArg norm (chart_value η H R hk s w)).symm

theorem plane_integrable (η H : RadialTest) (R : ℝ) {k : ℝ} (hk : 0<k) :
    Integrable (Function.uncurry (plane (height η H R) k)) (volume.prod heights) := by
  let F := height η H R
  let P := plane F k
  let C := cyl F k
  have CI := cylinder_integrable η H R hk
  have PM : Measurable (Function.uncurry P) := by
    dsimp [P,F,plane,height,OriginalPositiveHeightTest20261112.logHeight,Function.uncurry,e]
    fun_prop (disch := first | exact η.smooth.continuous.measurable | exact H.smooth.continuous.measurable)
  apply (integrable_prod_iff' PM.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [CI.prod_left_ae,ae_restrict_mem measurableSet_Ioi] with a ac ha
    have J := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_univ
      (fun s _ => ((hasDerivAt_id s).const_mul a).hasDerivWithinAt)
      (fun _ _ _ _ h => mul_left_cancel₀ ha.ne' h) (fun x => P x a)
    rw [x_range ha,integrableOn_univ,integrableOn_univ] at J
    apply J.mpr
    simpa only [abs_of_pos ha,Function.id_def,P,slope_change F _ _ ha] using ac
  · apply CI.swap.integral_norm_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [linear_integral (fun x => ‖P x a‖) ha]
    apply integral_congr_ae; exact ae_of_all _ fun s => by
      simpa only [C,P,norm_smul,Real.norm_of_nonneg ha.le,smul_eq_mul]
        using (congrArg norm (slope_change F k s ha)).symm

private def slopeRow (η H : RadialTest) (R k s : ℝ) := amp η R k s*∫ w : ℝ,expr H k s w

private theorem slope_integrals (η H : RadialTest) (R : ℝ) {k : ℝ} (hk : 0<k) :
    Integrable (slopeRow η H R k) ∧
    (∫ x : ℝ,∫ a,plane (height η H R) k x a ∂heights)=∫ s : ℝ,slopeRow η H R k s := by
  let F := height η H R
  let P := plane F k
  let C := cyl F k
  have CI := cylinder_integrable η H R hk
  have PI := plane_integrable η H R hk
  have row (s : ℝ) : (∫a,C s a ∂heights)=slopeRow η H R k s := by
    have hp : 0<productAt k s := by dsimp [productAt]; positivity
    rw [height_integral hp,slopeRow,←integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (chart_value η H R hk s))
  refine ⟨CI.integral_prod_left.congr (ae_of_all _ row),?_⟩
  rw [show (∫x:ℝ,∫a,plane _ k x a ∂heights)=∫a,∫x:ℝ,P x a ∂volume ∂heights from integral_integral_swap PI]
  calc
    _ = ∫a,∫s:ℝ,C s a ∂volume ∂heights := by
      apply integral_congr_ae; filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      rw [linear_integral _ ha]
      exact integral_congr_ae (ae_of_all _ fun s => slope_change F k s ha)
    _ = ∫s:ℝ,∫a,C s a ∂heights := (integral_integral_swap CI).symm
    _ = _ := integral_congr_ae (ae_of_all _ row)

private theorem phases (v : ℝ) :
    e v+e (-v)=2*(Real.cos (2*Real.pi*v):ℂ) := by
  rw [Complex.ofReal_cos,Complex.cos]
  simp only [e,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_neg]
  rw [show 2*(Real.pi:ℂ)*I*v=(2*Real.pi*(v:ℂ))*I by ring,
    show 2*(Real.pi:ℂ)*I*(-(v:ℂ))=-(2*Real.pi*(v:ℂ))*I by ring]
  ring

theorem positive_slopes (η H : RadialTest) (R : ℝ) {k : ℝ} (hk : 0<k) :
    (∫ x : ℝ,∫ a,plane (height η H R) k x a ∂heights)=
      2*∫ s in Ioi (0:ℝ),amp η R k s*response H (4*Real.pi*Real.sqrt (productAt k s)*s) := by
  obtain ⟨rowI,hplane⟩ := slope_integrals η H R hk
  let V := slopeRow η H R k
  have evenSum (s : ℝ) : V s+V (-s)=2*(amp η R k s*response H (4*Real.pi*Real.sqrt (productAt k s)*s)) := by
    have p : productAt k (-s)=productAt k s := by simp [productAt]
    have a : amp η R k (-s)=amp η R k s := by simp [amp,p]
    dsimp only [V,slopeRow]
    rw [a,←mul_add,←integral_add (val_integrable H k s) (val_integrable H k (-s)),response,
      mul_left_comm (2:ℂ) (amp η R k s),←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun w => by
      dsimp only [expr]; rw [p,←mul_add,show 2*(Real.sqrt (productAt k s)*(-s))*Real.cosh w=
        -(2*(Real.sqrt (productAt k s)*s)*Real.cosh w) by ring,phases]
      rw [show 2*Real.pi*(2*(Real.sqrt (productAt k s)*s)*Real.cosh w)=
        4*Real.pi*Real.sqrt (productAt k s)*s*Real.cosh w by ring]; ring
  have half := integral_comp_neg_Ioi (0:ℝ) V
  have all := intervalIntegral.integral_Iic_add_Ioi (b:=(0:ℝ)) rowI.integrableOn rowI.integrableOn
  rw [hplane,←all,←show (∫ s in Ioi (0:ℝ),V (-s))=∫ s in Iic 0,V s by simpa using half,
    add_comm,←integral_add rowI.integrableOn rowI.comp_neg.integrableOn,←integral_const_mul]
  exact integral_congr_ae (ae_of_all _ evenSum)
end ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
end
