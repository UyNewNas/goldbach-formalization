import ImbalancedChen.Part3OriginalExceptionalProbeFloor
import ImbalancedChen.Part3ActualContinuousPoincarePairing
import ImbalancedChen.Part3ImaginaryOrderKZeroOrderPositivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Batteries.Tactic.OpenPrivate

/-! The initial cumulative height interval in the manuscript's regular
large sieve.  The existing physical packet is used at H=1.  On its support
2πy exceeds 4, so the actual imaginary-order Macdonald probe cannot cancel
for |t|≤2. The proof uses integration by parts on a finite interval; no
unproved lower bound for Bessel functions is required. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularBaseProbe20261113
open Set Filter MeasureTheory Complex
open scoped Topology
open ImaginaryOrderKBesselSourceOnly ComplexOrderKBridgeSourceOnly
open OriginalExceptionalHeightWindow20261112 OriginalExceptionalProbeFloor20261113
open OriginalContinuousPoincarePackets20261110 ActualContinuousPoincarePairing20261110
open ActualCriticalCuspEvaluation20261110
open private density_nonneg from ImbalancedChen.Part3OriginalExceptionalProbeFloor

private def W (q x : ℝ) : ℝ := Real.exp (-q*Real.cosh x)
private def flux (q x : ℝ) : ℝ := x*W q x
private def fluxDeriv (q x : ℝ) : ℝ := W q x-q*x*Real.sinh x*W q x

private theorem flux_deriv (q x : ℝ) : HasDerivAt (flux q) (fluxDeriv q x) x := by
  have d := (hasDerivAt_id x).mul (((Real.hasDerivAt_cosh x).const_mul (-q)).exp)
  convert d using 1 <;> simp [flux,fluxDeriv,W] <;> ring

private theorem finite_order_comparison {q : ℝ} (hq : 0<q) (t : ℝ) {A : ℝ} (hA : 0≤A) :
    (2*q-t^2)*(∫ x in (0:ℝ)..A, W q x) ≤
      2*q*(∫ x in (0:ℝ)..A, kIntegrand (t/2) q x) := by
  let c := t^2
  have iw : IntervalIntegrable (W q) volume 0 A := (by unfold W; fun_prop : Continuous (W q)).intervalIntegrable 0 A
  have ik : IntervalIntegrable (kIntegrand (t/2) q) volume 0 A :=
    (by unfold kIntegrand; fun_prop : Continuous (kIntegrand (t/2) q)).intervalIntegrable 0 A
  have idv : IntervalIntegrable (fluxDeriv q) volume 0 A :=
    (by unfold fluxDeriv W; fun_prop : Continuous (fluxDeriv q)).intervalIntegrable 0 A
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x (_ : x∈uIcc 0 A) => flux_deriv q x) idv
  have po (x : ℝ) (hx : x∈Icc 0 A) :
      (2*q-c)*W q x + c*fluxDeriv q x ≤ 2*q*kIntegrand (t/2) q x := by
    have w0 : 0≤W q x := (Real.exp_pos _).le
    have a := Real.one_sub_sq_div_two_le_cos (x:=t*x)
    have b := Real.self_le_sinh_iff.mpr hx.1
    have d := mul_le_mul_of_nonneg_left a
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hq.le) w0)
    have e := mul_le_mul_of_nonneg_left b
      (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg t) hq.le) hx.1) w0)
    rw [kIntegrand,show 2*(t/2)*x=t*x by ring]
    change _ ≤ 2*q*(W q x*Real.cos (t*x))
    dsimp only [fluxDeriv,c]
    nlinarith only [d,e]
  have ineq := intervalIntegral.integral_mono_on hA
    ((iw.const_mul (2*q-c)).add (idv.const_mul c)) (ik.const_mul (2*q)) po
  rw [intervalIntegral.integral_add (iw.const_mul _) (idv.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,ftc] at ineq
  have f0 : flux q 0=0 := by simp [flux]
  have fA : 0≤flux q A := mul_nonneg hA (Real.exp_pos _).le
  dsimp only [c] at ineq
  rw [f0,sub_zero] at ineq
  linarith only [ineq,mul_nonneg (sq_nonneg t) fA]

/-- K_it(q) is at least half of K_0(q) on the packet's entire
nonzero support for the base interval, including t=0 and both signs. -/
theorem kernel_base_floor {q t : ℝ} (hq : 4≤q) (ht : |t|≤2) :
    imaginaryOrderK 0 q/2 ≤ imaginaryOrderK (t/2) q := by
  have qp : 0<q := by linarith
  have i0 : IntegrableOn (W q) (Ioi (0:ℝ)) := by simpa [W,kIntegrand] using kIntegrand_integrable 0 qp
  have h0 := (intervalIntegral_tendsto_integral_Ioi 0 i0 tendsto_id).const_mul (2*q-t^2)
  have h1 := (intervalIntegral_tendsto_integral_Ioi 0 (kIntegrand_integrable (t/2) qp) tendsto_id).const_mul (2*q)
  have lim := le_of_tendsto_of_tendsto h0 h1
    ((eventually_ge_atTop (0:ℝ)).mono (fun _ hu => finite_order_comparison qp t hu))
  have e : (∫ x in Ioi (0:ℝ),W q x) = imaginaryOrderK 0 q := by simp [W,imaginaryOrderK,kIntegrand]
  rw [e] at lim
  change (2*q-t^2)*imaginaryOrderK 0 q ≤ 2*q*imaginaryOrderK (t/2) q at lim
  have tsq : t^2≤4 := by
    have b := pow_le_pow_left₀ (abs_nonneg t) ht 2
    norm_num [sq_abs] at b
    exact b
  have kn : 0≤imaginaryOrderK 0 q := (ImaginaryOrderKZeroOrderPositivitySourceOnly.imaginaryOrderK_zero_pos qp).le
  have scale : q*imaginaryOrderK 0 q ≤ (2*q-t^2)*imaginaryOrderK 0 q :=
    mul_le_mul_of_nonneg_right (by linarith) kn
  apply (mul_le_mul_iff_right₀ (show 0<2*q by positivity)).mp
  calc
    _ = q*imaginaryOrderK 0 q := by ring
    _ ≤ _ := scale.trans lim

private def integrand (t y : ℝ) : ℂ :=
  ((y⁻¹)^2 : ℝ) • (star ((seed 1).toFun y)*orderRadial 1 ((t:ℂ)*I) y)

private theorem integrand_re (t : ℝ) {y : ℝ} (hy : 0<y) :
    (integrand t y).re = (2*bump y/y)*imaginaryOrderK (t/2) (2*Real.pi*y) := by
  have ko : complexOrderK ((t:ℂ)*I) (2*Real.pi*y) =
      (imaginaryOrderK (t/2) (2*Real.pi*y):ℂ) := by
    simpa only [show 2*(t/2)=t by ring] using complexOrderK_imaginary (t/2) (2*Real.pi*y)
  let b := bump y
  let k := imaginaryOrderK (t/2) (2*Real.pi*y)
  have alg : (y⁻¹)^2*((Real.sqrt y*b)*(2*Real.sqrt y*k))=(2*b/y)*k := by
    calc
      _ = (2*b*k)*(Real.sqrt y)^2/y^2 := by field_simp [hy.ne'] <;> ring
      _ = _ := by rw [Real.sq_sqrt hy.le]; field_simp [hy.ne'] <;> ring
  have e : integrand t y = (((y⁻¹)^2*((Real.sqrt y*b)*(2*Real.sqrt y*k)) : ℝ):ℂ) := by
    simp only [integrand,seed_pos_height 1 hy,one_mul,orderRadial,Int.cast_one,abs_one,mul_one,
      ko,Complex.star_def,Complex.conj_ofReal,Complex.real_smul,b,k]
    push_cast
    ring
  rw [e,Complex.ofReal_re,alg]

private theorem integrand_integrable (t : ℝ) : IntegrableOn (integrand t) (Ioi (0:ℝ)) := by
  have h := radialProbe_integrable 1 (by decide) (seed 1).toFun (seed 1).continuous
    (seed 1).compact (seed 1).positive t
  have order : criticalPoint t-1/2=(t:ℂ)*I := by unfold criticalPoint; ring
  simpa only [integrand,orderRadial,ActualOrdinaryContinuousModes20261110.radial,order] using h

def baseFloor : ℝ := probeConstant/2
theorem baseFloor_pos : 0<baseFloor := half_pos probeConstant_pos

theorem regular_base_probe {t : ℝ} (ht : |t|≤2) :
    baseFloor ≤ ‖orderProbe 1 (seed 1).toFun ((t:ℂ)*I)‖ := by
  have cmp (y : ℝ) (hy : 0<y) : (1/2:ℝ)*(integrand 0 y).re ≤ (integrand t y).re := by
    rw [integrand_re 0 hy,integrand_re t hy,zero_div]
    by_cases h : bump y=0
    · simp [h]
    · have by1 := (bump_inside h).1
      have q : 4≤2*Real.pi*y := by
        nlinarith only [Real.pi_gt_three,mul_le_mul_of_nonneg_left by1.le Real.pi_pos.le]
      have floor := mul_le_mul_of_nonneg_left (kernel_base_floor q ht)
        (div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (bump_bounds y).1) hy.le)
      linarith only [floor]
  have raw := integral_mono_ae ((integrand_integrable 0).re.const_mul (1/2:ℝ)) (integrand_integrable t).re
    ((ae_restrict_mem (μ:=volume) measurableSet_Ioi).mono (fun y hy => cmp y hy))
  rw [integral_const_mul,integral_re (integrand_integrable 0),integral_re (integrand_integrable t)] at raw
  change (1/2:ℝ)*(orderProbe 1 (seed 1).toFun ((0:ℂ)*I)).re ≤
    (orderProbe 1 (seed 1).toFun ((t:ℂ)*I)).re at raw
  rw [zero_mul] at raw
  have f := original_probe_floor (H:=1) (α:=0) (by norm_num) (by norm_num)
  have id := original_probe_integral (H:=1) (by norm_num) 0
  have nn : 0≤∫ u in Ioi (0:ℝ),density 1 0 u :=
    integral_nonneg_of_ae ((ae_restrict_mem (μ:=volume) measurableSet_Ioi).mono
      (fun u hu => density_nonneg hu 1 0))
  simp only [Complex.ofReal_zero,Real.rpow_zero,mul_one] at id f
  rw [id,Complex.norm_real,Real.norm_of_nonneg nn] at f
  rw [id,Complex.ofReal_re] at raw
  exact (show baseFloor≤(orderProbe 1 (seed 1).toFun ((t:ℂ)*I)).re by
    unfold baseFloor; linarith only [raw,f]).trans (Complex.re_le_norm _)

end ImbalancedChen.Part3.OriginalRegularBaseProbe20261113
end
