import ImbalancedChen.Part3PrescribedLogTensorExpansion
import ImbalancedChen.Part3OriginalPrescribedAbelOrbit
import ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov

/-! Fubini on the actual (x,a) plane, at one positive physical
argument. Its absolute majorant is uniform over the active tiles. -/
namespace ImbalancedChen.Part3.PrescribedTensorOrbitExchange20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112
open PrescribedLogTensorExpansion20261112 OriginalPrescribedAbelLift20261112
open OriginalPrescribedAbelOrbit20261112 ActualMarkedBruhatTest20261112
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e norm_e)

abbrev planeMeasure := (volume : Measure ℝ).prod OriginalAbelOrbit.heights
def orbit (q : Modes) := orbitTest (-1) (pattern q.1.1 q.2.1) (rightPattern q.1.2 q.2.2)
def weightedPlane (ell : D4 → ℤ) (Y k : ℝ) (q : Modes) (p : ℝ × ℝ) : ℂ :=
  c ell Y q*OriginalAbelOrbit.plane (productAt q) k p.1 p.2
def qFloor (Y : ℝ) := 4*Real.pi*Real.sqrt (floor Y)
theorem qFloor_pos {Y : ℝ} (hY : 0<Y) : 0<qFloor Y :=
  mul_pos (by positivity) (Real.sqrt_pos.mpr (floor_pos hY))

private theorem active_xy (ell : D4 → ℤ) {Y k : ℝ} (hY : 0<Y) (hk : 0≤k)
    (q : Modes) (p : ℝ × ℝ) (hp : weightedPlane ell Y k q p≠0) :
    let a := p.2
    let L := Real.exp ((q.1.1:ℝ)-2)
    let U := Real.exp ((q.1.1:ℝ)+2)
    a∈Icc L U ∧ floor Y≤k ∧ |p.1|≤U*Real.sqrt (k/floor Y) := by
  let a := p.2
  let x := p.1
  let b := k*a/(x^2+a^2)
  have hc : c ell Y q≠0 := fun z => hp (by simp [weightedPlane,z])
  have ht : productAt q a b≠0 := by
    intro z; apply hp
    change _ * (((a⁻¹)^2:ℝ) • (productAt q a b*_))=0
    simp only [z,zero_mul,smul_zero,mul_zero]
  have ha := pattern_support _ _ (subset_tsupport _ (mul_ne_zero_iff.mp ht).1)
  have hapos : 0<a := (Real.exp_pos _).trans_le ha.1
  have hd : 0<x^2+a^2 := by positivity
  have hb := active_product ell hY q hc ht
  have he : floor Y*(x^2+a^2)≤k*a^2 := by
    have hb' : floor Y ≤ (k*a^2)/(x^2+a^2) := by convert hb using 1 <;> dsimp [b] <;> ring
    exact (le_div_iff₀ hd).mp hb'
  have hf := floor_pos hY
  have hcut : floor Y≤k := by
    by_contra! h
    nlinarith only [he,mul_nonneg hf.le (sq_nonneg x),mul_pos (sub_pos.mpr h) (sq_pos_of_pos hapos)]
  have hs : x^2≤a^2*(k/floor Y) := by
    rw [← mul_div_assoc,le_div_iff₀ hf]
    nlinarith only [he,mul_nonneg hf.le (sq_nonneg a)]
  have hh : |x|≤a*Real.sqrt (k/floor Y) := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hapos.le (Real.sqrt_nonneg _))).mp
    simpa only [sq_abs,mul_pow,Real.sq_sqrt (div_nonneg hk hf.le)] using hs
  exact ⟨ha,hcut,hh.trans (mul_le_mul_of_nonneg_right ha.2 (Real.sqrt_nonneg _))⟩

private theorem plane_meas (ell : D4 → ℤ) (Y k : ℝ) (q : Modes) :
    Measurable (weightedPlane ell Y k q) := by
  have h := (pattern_test q.1.1 q.2.1).1.measurable
  have l := (right_test q.1.2 q.2.2).1.measurable
  dsimp [weightedPlane,OriginalAbelOrbit.plane,productAt,e]
  fun_prop

theorem plane_price (ell : D4 → ℤ) {Y k : ℝ} (hY : 0<Y) (hk : 0≤k) (q : Modes) :
    Integrable (weightedPlane ell Y k q) planeMeasure ∧
    (∫ p,‖weightedPlane ell Y k q p‖ ∂planeMeasure) ≤
      ‖c ell Y q‖*(2*Real.exp 8*Real.sqrt (k/floor Y)) := by
  let L := Real.exp ((q.1.1:ℝ)-2)
  let U := Real.exp ((q.1.1:ℝ)+2)
  let T := Real.sqrt (k/floor Y)
  let X := U*T
  let K := (Icc (-X) X) ×ˢ (Icc L U)
  let W := ‖c ell Y q‖*(L⁻¹)^2
  have hL : 0<L := Real.exp_pos _
  have hU : 0<U := Real.exp_pos _
  have hT : 0≤T := Real.sqrt_nonneg _
  have hX : 0≤X := mul_nonneg hU.le hT
  have hLU : L≤U := Real.exp_le_exp.mpr (by linarith)
  have hK : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hr : Icc L U ∩ Ioi (0:ℝ)=Icc L U := inter_eq_left.mpr (fun y hy => hL.trans_le hy.1)
  have hm : planeMeasure K = ENNReal.ofReal (X-(-X))*ENNReal.ofReal (U-L) := by
    simp only [K,planeMeasure,Measure.prod_prod,OriginalAbelOrbit.heights,
      Measure.restrict_apply measurableSet_Icc,hr,Real.volume_Icc]
  have hw : 0≤W := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hI : Integrable (K.indicator (fun _ : ℝ×ℝ => W)) planeMeasure :=
    (integrable_indicator_iff hK).mpr (integrableOn_const (by rw [hm]; exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne))
  have dom (p : ℝ×ℝ) : ‖weightedPlane ell Y k q p‖ ≤ K.indicator (fun _ => W) p := by
    by_cases z : weightedPlane ell Y k q p=0
    · rw [z,norm_zero]; exact indicator_nonneg (fun _ _ => hw) _
    obtain ⟨ha,_,hx⟩ := active_xy ell hY hk q p z
    have inK : p∈K := ⟨abs_le.mp hx,ha⟩
    rw [indicator_of_mem inK,weightedPlane,norm_mul,OriginalAbelOrbit.plane,norm_smul,
      Real.norm_of_nonneg (sq_nonneg _),norm_mul,norm_e,mul_one]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (mul_le_of_le_one_right (sq_nonneg _) (product_bound _ _ _)).trans
      ((sq_le_sq₀ (inv_nonneg.mpr (hL.trans_le ha.1).le) (inv_nonneg.mpr hL.le)).mpr (inv_anti₀ hL ha.1))
  have hi := hI.mono' (plane_meas ell Y k q).aestronglyMeasurable (ae_of_all _ dom)
  refine ⟨hi,(integral_mono hi.norm hI dom).trans ?_⟩
  rw [integral_indicator hK,setIntegral_const,smul_eq_mul,measureReal_def,hm,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith),ENNReal.toReal_ofReal (sub_nonneg.mpr hLU)]
  have rat : U^2*(L⁻¹)^2=Real.exp 8 := by
    dsimp [L,U]; rw [← Real.exp_neg]; simp only [sq,← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (2*X)*U*W := by
      rw [show X-(-X)=2*X by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_self _ hL.le) (by positivity)) hw
    _ = _ := by dsimp [X,W,T]; linear_combination 2*‖c ell Y q‖*Real.sqrt (k/floor Y)*rat

private theorem plane_pointwise (ell : D4 → ℤ) {Y k : ℝ} (hY : 0<Y) (hk : 0<k)
    (x a : ℝ) (ha : 0<a) : HasSum (fun q : Modes => weightedPlane ell Y k q (x,a))
      (OriginalAbelOrbit.plane (H_ab ell Y) k x a) := by
  let b := k*a/(x^2+a^2)
  have hb : 0<b := by dsimp [b]; positivity
  have hs := pointwise ell hY (Real.log a) (Real.log b)
  simp only [logLift,Real.exp_log ha,Real.exp_log hb] at hs
  have h := (hs.mul_right (e (x-k*x/(x^2+a^2)))).mul_left ((((a⁻¹)^2:ℝ):ℂ))
  convert h using 1
  · funext q; dsimp [weightedPlane,OriginalAbelOrbit.plane,b]; rw [Complex.real_smul]; ring
  · rfl

private theorem plane_orbit (ell : D4 → ℤ) {Y t : ℝ} (hY : 0<Y) (ht : 0<t) (q : Modes) :
    let k := (t/(4*Real.pi))^2
    c ell Y q*orbit q t = ((4*Real.pi/t:ℝ):ℂ)*∫ p,weightedPlane ell Y k q p ∂planeMeasure := by
  let k := (t/(4*Real.pi))^2
  have F := (plane_price ell hY (sq_nonneg (t/(4*Real.pi))) q).1
  have r := OriginalAbelOrbit.rank_one (pattern q.1.1 q.2.1) (rightPattern q.1.2 q.2.2)
    (pattern_test _ _).2.2 t
  rw [orbit,←r,OriginalAbelOrbit.induced,Complex.real_smul,integral_prod _ F]
  simp only [weightedPlane,integral_const_mul,productAt]; ring

theorem orbit_zero (ell : D4 → ℤ) {Y t : ℝ} (hY : 0<Y) (ht : 0<t) (hz : t<qFloor Y) (q : Modes) :
    c ell Y q*orbit q t=0 := by
  have hk : (t/(4*Real.pi))^2 < floor Y := by
    have d : t/(4*Real.pi)<Real.sqrt (floor Y) := (div_lt_iff₀ (by positivity)).mpr (by
      simpa only [qFloor,mul_comm] using hz)
    simpa only [Real.sq_sqrt (floor_pos hY).le] using
      (sq_lt_sq₀ (by positivity : 0≤ t/(4*Real.pi)) (Real.sqrt_nonneg _)).mpr d
  have z (p : ℝ×ℝ) : weightedPlane ell Y ((t/(4*Real.pi))^2) q p=0 := by
    by_contra h
    exact (not_le.mpr hk) (active_xy ell hY (sq_nonneg _) q p h).2.1
  rw [plane_orbit ell hY ht]; simp only [z,integral_zero,mul_zero]

def orbitBound (Y : ℝ) := 2*Real.exp 8/Real.sqrt (floor Y)
theorem orbit_price (ell : D4 → ℤ) {Y t : ℝ} (hY : 0<Y) (ht : 0<t) (q : Modes) :
    ‖c ell Y q*orbit q t‖ ≤ ‖c ell Y q‖*orbitBound Y := by
  let k := (t/(4*Real.pi))^2
  have H := (norm_integral_le_integral_norm (weightedPlane ell Y k q)).trans
    (plane_price ell hY (sq_nonneg _) q).2
  rw [plane_orbit ell hY ht,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left H (by positivity : 0≤4*Real.pi/t)).trans_eq
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (by positivity : 0≤t/(4*Real.pi))]
  dsimp [orbitBound]; field_simp [Real.pi_ne_zero,ht.ne',(Real.sqrt_pos.mpr (floor_pos hY)).ne']; ring

theorem orbit_reconstruction (ell : D4 → ℤ) {Y t : ℝ} (hY : 0<Y) (ht : 0<t) :
    HasSum (fun q : Modes => c ell Y q*orbit q t)
      (P3Period64NativeReconstructionSourceOnly.spectralTest ell Y t) := by
  let k := (t/(4*Real.pi))^2
  have hk : 0<k := sq_pos_of_pos (by positivity)
  let F := weightedPlane ell Y k
  have I (q) := (plane_price ell hY hk.le q).1
  have A : Summable (fun q : Modes => ∫ p,‖F q p‖ ∂planeMeasure) :=
    ((absolute_coefficients ell hY).mul_right _).of_nonneg_of_le
      (fun q => integral_nonneg (fun _ => norm_nonneg _)) (fun q => (plane_price ell hY hk.le q).2)
  have hs : Summable (fun q : Modes => c ell Y q*orbit q t) :=
    ((absolute_coefficients ell hY).mul_right _).of_norm_bounded (orbit_price ell hY ht)
  apply hs.hasSum_iff.mpr
  simp_rw [plane_orbit ell hY ht]
  rw [tsum_mul_left,integral_tsum_of_summable_integral_norm I A,← prescribed ell hY ht,
    OriginalAbelOrbit.induced,Complex.real_smul,← integral_prod _ (OriginalAbelOrbit.plane_integrable ell hY hk)]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  rintro ⟨x,a⟩
  by_cases ha : 0<a
  · exact (plane_pointwise ell hY hk x a ha).tsum_eq
  · simp [F,weightedPlane,OriginalAbelOrbit.plane,productAt,pattern,ha,H_ab,OriginalAbelGaussian.height]

end
end ImbalancedChen.Part3.PrescribedTensorOrbitExchange20261112
