import ImbalancedChen.Part3OriginalRegularPreKuznetsovAngle
import ImbalancedChen.Part3OriginalRegularPreKuznetsovSeed
import ImbalancedChen.Part3OriginalPositiveScalarGeometry
import Batteries.Tactic.OpenPrivate

/-! The exponential seed on the published positive-sign Bruhat plane.
The q^δ regularization has no dependence on the logarithm of the polar
radius after the two height powers have been multiplied. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovPolar20261113
open Set Filter MeasureTheory Complex
open scoped Topology
open OriginalPositiveScalarGeometry20261112 (plane)
open OriginalRegularPreKuznetsovAngle20261113 (angularWave ray ray_components)
open OriginalRegularPreKuznetsovFourier20261113 (character)
open OriginalRegularPreKuznetsovSeed20261113 (seed logSeed halfCarrier)
open ActualUnitBandHeightSeeds20261112 (modulation window)
open private exp_half from ImbalancedChen.Part3ActualUnitBandHeightSeeds
open ActualLogHorocycleAdjoint20261112 (fromLog fromLog_exp)
open ComplexOrderKBridgeSourceOnly (complexOrderK complexOrderK_real)
open ActualHalfOrderKWronskianSourceOnly (realOrderK_half_eq_gaussian_closedForm)
open P3Period64NativeReconstructionSourceOnly (e)

def physical (δ r a : ℝ) : ℂ :=
  ((Real.pi*a*Real.exp (-(2*Real.pi)*a)*(2*Real.pi*a)^δ:ℝ):ℂ)*
    modulation r (Real.log (2*Real.pi*a))

private theorem sqrt_factor {y : ℝ} (hy : 0<y) :
    Real.sqrt y*(2*Real.pi*y)*Real.sqrt (Real.pi/(2*(2*Real.pi*y)))=Real.pi*y := by
  let q := 2*Real.pi*y
  have hq : 0<q := by dsimp only [q]; positivity
  let b := Real.pi/(2*q)
  have hb : 0<b := div_pos Real.pi_pos (by positivity)
  change Real.sqrt y*q*Real.sqrt b=Real.pi*y
  apply (sq_eq_sq₀ (by positivity) (mul_pos Real.pi_pos hy).le).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt hy.le,Real.sq_sqrt hb.le]
  dsimp only [b,q]
  field_simp [hy.ne',Real.pi_ne_zero] <;> ring

/-- On the positive chart this is the actual frequency-one compact
height seed. The sign of the modulation is fixed by the native probe. -/
theorem compact_profile (r : ℝ) (j : ℕ) {y : ℝ} (hy : 0<y) :
    (seed (2*Real.pi) r j).toFun y=
      (window j (Real.log (2*Real.pi*y)):ℂ)*physical 0 r y := by
  let C := 2*Real.pi
  have hC : 0<C := by dsimp only [C]; positivity
  have qpos := mul_pos hC hy
  have h := fromLog_exp (logSeed C r j) (Real.log y)
  rw [Real.exp_log hy,exp_half y hy] at h
  have lj : Real.log y+Real.log C=Real.log (C*y) := by rw [Real.log_mul hC.ne' hy.ne',add_comm]
  have flip : complexOrderK (1/2:ℂ) (C*y)=
      (Real.sqrt (Real.pi/(2*(C*y)))*Real.exp (-(C*y)):ℝ) := by
    rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,complexOrderK_real,realOrderK_half_eq_gaussian_closedForm qpos]
  simp only [logSeed,lj,halfCarrier,Real.exp_log qpos,flip] at h
  change (fromLog (logSeed C r j)).toFun y=_ at h
  change (fromLog (logSeed C r j)).toFun y=_
  rw [h]
  have sq := congrArg (fun x : ℝ => (x:ℂ)) (sqrt_factor hy)
  dsimp only [physical,C] at *
  have en : -(2*Real.pi)*y= -(2*Real.pi*y) := by ring
  simp only [Real.rpow_zero,mul_one,Complex.ofReal_mul,en] at sq ⊢
  linear_combination (norm := ring)
    (window j (Real.log (2*Real.pi*y)):ℂ)*(Real.exp (-(2*Real.pi*y)):ℂ)*
      modulation r (Real.log (2*Real.pi*y))*sq

private theorem modulation_pair {a b : ℝ} (a0 : 0<a) (b0 : 0<b) (r : ℝ) :
    modulation r (Real.log (2*Real.pi*a))*star (modulation r (Real.log (2*Real.pi*b)))=
      Complex.exp ((r:ℂ)*I*(Real.log (a/b):ℂ)) := by
  have cp : (2*Real.pi)≠0 := (mul_pos (by norm_num) Real.pi_pos).ne'
  simp only [modulation,Complex.star_def,←Complex.exp_conj,map_mul,Complex.conj_I,Complex.conj_ofReal,
    ←Complex.exp_add,Real.log_mul cp a0.ne',Real.log_mul cp b0.ne',Real.log_div a0.ne' b0.ne',
    Complex.ofReal_add,Complex.ofReal_sub]
  congr 1
  ring

private theorem rank_pair {a b : ℝ} (a0 : 0<a) (b0 : 0<b) (δ r : ℝ) :
    physical δ r a*star (physical δ r b)=
      ((Real.pi^2*(a*b)*((2*Real.pi)^2*(a*b))^δ:ℝ):ℂ)*
      Complex.exp ((-(2*Real.pi)*(a+b):ℝ):ℂ)*Complex.exp ((r:ℂ)*I*(Real.log (a/b):ℂ)) := by
  have power : (2*Real.pi*a)^δ*(2*Real.pi*b)^δ=((2*Real.pi)^2*(a*b))^δ := by
    rw [←Real.mul_rpow (by positivity : 0≤2*Real.pi*a) (by positivity : 0≤2*Real.pi*b)]; congr 1;ring
  have decay : Real.exp (-(2*Real.pi)*a)*Real.exp (-(2*Real.pi)*b)=Real.exp (-(2*Real.pi)*(a+b)) := by
    rw [←Real.exp_add]; congr 1;ring
  calc
    _ = ((Real.pi^2*(a*b)*((2*Real.pi*a)^δ*(2*Real.pi*b)^δ)*
        (Real.exp (-(2*Real.pi)*a)*Real.exp (-(2*Real.pi)*b)):ℝ):ℂ)*
        (modulation r (Real.log (2*Real.pi*a))*star (modulation r (Real.log (2*Real.pi*b)))) := by
      simp only [physical,star_mul',Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_pow]
      ring
    _ = _ := by rw [power,decay,modulation_pair a0 b0]; push_cast; ring

/-- Both Jacobians, the real Bruhat oscillation, the regularizing height
powers and the Fourier character in r appear in this pointwise identity. -/
theorem polar_density {p : ℝ} (hp : 0<p) {θ : ℝ} (hθ : θ∈Ioo 0 Real.pi)
    (δ r ξ : ℝ) :
    let R := p*Real.exp ξ
    (R^2:ℝ) • plane (fun a b => physical δ r a*star (physical δ r b)) (p^2)
      (R*Real.cos θ) (R*Real.sin θ)=
        ((Real.pi^2*p^2*((2*Real.pi)^2*(p^2*Real.sin θ^2))^δ:ℝ):ℂ)*
        character ξ r*angularWave (4*Real.pi*p*Real.cosh ξ) θ := by
  let R := p*Real.exp ξ
  let s := Real.sin θ
  let c := Real.cos θ
  let a := R*s
  let b := p*Real.exp (-ξ)*s
  have ss := Real.sin_pos_of_mem_Ioo hθ
  have rr : 0<R := mul_pos hp (Real.exp_pos _)
  have aa : 0<a := mul_pos rr ss
  have bb : 0<b := mul_pos (mul_pos hp (Real.exp_pos _)) ss
  have den : (R*c)^2+(R*s)^2=R^2 := by
    dsimp only [c,s]; linear_combination (norm := ring) R^2*(Real.sin_sq_add_cos_sq θ)
  have sec : p^2*a/R^2=b := by
    dsimp only [a,b,R]; rw [Real.exp_neg]; field_simp [hp.ne',(Real.exp_pos ξ).ne'] <;> ring
  have prod : a*b=p^2*s^2 := by
    dsimp only [a,b,R]; rw [Real.exp_neg]; field_simp [(Real.exp_pos ξ).ne'] <;> ring
  have phase : R*c+p^2*(R*c)/R^2=2*p*Real.cosh ξ*c := by
    dsimp only [R]; rw [Real.cosh_eq,Real.exp_neg]; field_simp [hp.ne',(Real.exp_pos ξ).ne'] <;>ring
  have add : a+b=2*p*Real.cosh ξ*s := by dsimp only [a,b,R]; rw [Real.cosh_eq];ring
  have ratio : a/b=Real.exp (2*ξ) := by
    dsimp only [a,b,R]; rw [Real.exp_neg,show 2*ξ=ξ+ξ by ring,Real.exp_add]
    field_simp [hp.ne',ss.ne',(Real.exp_pos ξ).ne'] <;> ring
  have amp : R^2*(a⁻¹)^2*(Real.pi^2*(a*b))=Real.pi^2*p^2 := by
    rw [prod]; dsimp only [a]; field_simp [rr.ne',ss.ne'] <;>ring
  have osc : Complex.exp ((-(2*Real.pi)*(a+b):ℝ):ℂ)*e (R*c+p^2*(R*c)/R^2)=
      angularWave (4*Real.pi*p*Real.cosh ξ) θ := by
    rw [add,phase,e,←Complex.exp_add,angularWave,ray_components]
    congr 1
    dsimp only [c,s]
    push_cast
    linear_combination (norm := ring) (-4*(Real.pi:ℂ)*(p:ℂ)*(Real.cosh ξ:ℂ)*(Real.sin θ:ℂ))*I_sq
  dsimp only
  change (R^2:ℝ) • plane _ (p^2) (R*c) a=_
  rw [plane,show (R*c)^2+a^2=R^2 from den,sec,rank_pair aa bb,ratio,Real.log_exp]
  let V := (((2*Real.pi)^2*(a*b))^δ:ℝ)
  have ac := congrArg (fun x : ℝ => (x:ℂ)) amp
  calc
    _ = ((R^2*(a⁻¹)^2*(Real.pi^2*(a*b)):ℝ):ℂ)*(V:ℂ)*
        Complex.exp ((r:ℂ)*I*((2*ξ:ℝ):ℂ))*
        (Complex.exp ((-(2*Real.pi)*(a+b):ℝ):ℂ)*e (R*c+p^2*(R*c)/R^2)) := by
      simp only [Complex.real_smul,Complex.ofReal_mul,V];ring
    _ = _ := by
      have ch : Complex.exp ((r:ℂ)*I*((2*ξ:ℝ):ℂ))=character ξ r := by
        unfold character; congr 1; push_cast; ring
      rw [ac,osc,ch]
      dsimp only [V]
      rw [prod]
      simp only [Complex.ofReal_mul,Complex.ofReal_pow]

/-- Fixed-frequency identity-cell height integral at δ=0. -/
theorem diagonal (r : ℝ) :
    (∫ a in Ioi (0:ℝ),((a⁻¹)^2:ℝ) • (physical 0 r a*star (physical 0 r a)))=(Real.pi/4:ℝ) := by
  have E {a : ℝ} (ha : 0<a) : ((a⁻¹)^2:ℝ) • (physical 0 r a*star (physical 0 r a))=
      ((Real.pi^2*Real.exp ((-(4*Real.pi))*a):ℝ):ℂ) := by
    rw [rank_pair ha ha,div_self ha.ne',Real.log_one]
    simp only [Real.rpow_zero,mul_one,Complex.ofReal_zero,mul_zero,Complex.exp_zero,
      Complex.real_smul,←Complex.ofReal_exp,←Complex.ofReal_mul]
    congr 1
    rw [show -(2*Real.pi)*(a+a)= -(4*Real.pi)*a by ring]
    field_simp [ha.ne'] <;> ring
  calc
    _ = ∫ a in Ioi (0:ℝ),((Real.pi^2*Real.exp ((-(4*Real.pi))*a):ℝ):ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi (fun _ h => E h)
    _ = _ := by
      rw [integral_complex_ofReal,integral_const_mul,integral_exp_mul_Ioi (by linarith [Real.pi_pos] : -(4*Real.pi)<0) 0]
      push_cast
      simp only [mul_zero,Real.exp_zero]
      field_simp [Real.pi_ne_zero,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovPolar20261113
end
