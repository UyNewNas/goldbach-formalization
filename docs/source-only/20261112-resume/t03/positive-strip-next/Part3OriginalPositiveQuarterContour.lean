import ImbalancedChen.Part3OriginalPositiveStripMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! For each of the *original* odd integer J's we identify the low-frequency
cosine projection and the decaying cosh tail by an ordinary Cauchy rectangle. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveQuarterContour20261112

open Set Filter MeasureTheory Complex
open scoped Topology BigOperators
open ActualPositiveHolomorphicWeights20261112 (intJ intJ_bound expMass)
open OriginalPositiveJacobiAnger20261112 (oddOrder sin_sin)
open OriginalPositiveStripMoments20261112 (odd_injective sign)

def low (j : ℕ) (q : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..Real.pi/2,Real.cos (q*Real.sin t)*Real.cos ((oddOrder j:ℝ)*t)

def high (j : ℕ) (q : ℝ) : ℝ :=
  ∫ w in Ioi (0:ℝ),Real.exp (-(oddOrder j:ℝ)*w)*Real.cos (q*Real.cosh w)

private theorem cos_even_frequency (k : ℤ) :
    (∫ t in (0:ℝ)..Real.pi/2,Real.cos (2*(k:ℝ)*t))=if k=0 then Real.pi/2 else 0 := by
  split_ifs with hk
  · subst k; simp
  have kn : 2*(k:ℝ)≠0 := mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hk)
  have D := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=Real.pi/2)
    (f:=fun t : ℝ => Real.sin (2*(k:ℝ)*t)/(2*(k:ℝ)))
    (f':=fun t => Real.cos (2*(k:ℝ)*t))
    (fun t _ => by convert (((hasDerivAt_id t).const_mul (2*(k:ℝ))).sin.div_const (2*(k:ℝ))) using 1
                   field_simp [kn] <;> ring) (by exact (by fun_prop : Continuous _).intervalIntegrable ..)
  simpa only [show 2*(k:ℝ)*(Real.pi/2)=(k:ℝ)*Real.pi by ring,Real.sin_int_mul_pi,
    mul_zero,Real.sin_zero,zero_div,sub_zero] using D

private theorem orthogonal (j l : ℕ) :
    (∫ t in (0:ℝ)..Real.pi/2,Real.sin ((oddOrder j:ℝ)*t)*Real.sin ((oddOrder l:ℝ)*t))=
      if j=l then Real.pi/4 else 0 := by
  have E (t : ℝ) : 2*(Real.sin ((oddOrder j:ℝ)*t)*Real.sin ((oddOrder l:ℝ)*t))=
      Real.cos (2*((j:ℤ)-l:ℤ)*t)-Real.cos (2*((j:ℤ)+l+1:ℤ)*t) := by
    rw [←mul_assoc,Real.two_mul_sin_mul_sin]
    congr 1 <;> congr 1 <;> simp [oddOrder] <;> push_cast <;> ring
  have e := congrArg (fun f : ℝ→ℝ => ∫ t in (0:ℝ)..Real.pi/2,f t) (funext E)
  simp only [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
    (by exact (by fun_prop : Continuous _).intervalIntegrable ..)
    (by exact (by fun_prop : Continuous _).intervalIntegrable ..),cos_even_frequency] at e
  by_cases h : j=l
  · subst l; simp [show (j:ℤ)+j+1≠0 by omega] at e; rw [if_pos rfl]; linarith
  · simp [show (j:ℤ)-l≠0 by omega,show (j:ℤ)+l+1≠0 by omega] at e; rw [if_neg h]; linarith

private theorem sine_quarter (j : ℕ) {q : ℝ} (hq : 0≤q) :
    ((∫ t in (0:ℝ)..Real.pi/2,Real.sin (q*Real.sin t)*Real.sin ((oddOrder j:ℝ)*t)):ℂ)=
      (Real.pi/2:ℝ)*intJ (oddOrder j) q := by
  let J := fun l => intJ (oddOrder l) q
  have sj : Summable (fun l => ‖J l‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => intJ_bound _ hq le_rfl)
      (((Real.summable_pow_div_factorial (q/2)).comp_injective odd_injective).mul_right (expMass q))
  let S := fun l (t : ℝ) => (Real.sin ((oddOrder l:ℝ)*t):ℂ)
  have sb (l : ℕ) (t : ℝ) : ‖S l t‖≤1 := by
    simpa [S,Real.norm_eq_abs] using Real.abs_sin_le_one ((oddOrder l:ℝ)*t)
  have H := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ:=volume) (a:=(0:ℝ)) (b:=Real.pi/2) (F:=fun l t => 2*J l*S l t*S j t)
    (f:=fun t => (Real.sin (q*Real.sin t):ℂ)*S j t)
    (fun l _ => 2*‖J l‖) (fun l => (by dsimp [S]; fun_prop : Continuous _).aestronglyMeasurable)
    (fun l => ae_of_all _ fun t _ => by
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_ofNat]
      simpa only [mul_one] using mul_le_mul
        (mul_le_mul_of_nonneg_left (sb l t) (by positivity : 0≤2*‖J l‖)) (sb j t)
        (norm_nonneg _) (by positivity))
    (ae_of_all _ fun _ _ => sj.mul_left 2) intervalIntegrable_const
    (ae_of_all _ fun t _ => (sin_sin q t).mul_right (S j t))
  have value (l : ℕ) : (∫ t in (0:ℝ)..Real.pi/2,2*J l*S l t*S j t)=
      if l=j then (Real.pi/2:ℝ)*J j else 0 := by
    simp_rw [mul_assoc (2*J l),S,←Complex.ofReal_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal,orthogonal]
    split_ifs with h <;> simp_all <;> push_cast <;> ring
  simp_rw [value] at H
  rw [←intervalIntegral.integral_ofReal]
  simpa only [S,Complex.ofReal_mul,J,tsum_ite_eq',tsum_ite_eq] using H.tsum_eq.symm

private def G (q : ℝ) (n : ℕ) (z : ℂ) := Complex.exp (((q:ℂ)*Complex.sin z+n*z)*I)

private theorem global (q : ℝ) (n : ℕ) : Differentiable ℂ (G q n) := by unfold G; fun_prop

private theorem norm_top {q R x : ℝ} (hq : 0≤q) (hR : 0≤R)
    (hx : x∈Icc 0 (Real.pi/2)) (n : ℕ) :
    ‖G q n ((x:ℂ)+R*I)‖≤Real.exp (-(n:ℝ)*R) := by
  rw [G,Complex.norm_exp,Complex.sin_add_mul_I]
  apply Real.exp_le_exp.mpr
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
  simp [←Complex.ofReal_cos,←Complex.ofReal_sin,←Complex.ofReal_cosh,←Complex.ofReal_sinh,
    Complex.mul_re,Complex.mul_im]
  nlinarith [mul_nonneg (mul_nonneg hq hc) (Real.sinh_nonneg_iff.mpr hR)]

private theorem sides (q w : ℝ) (j : ℕ) :
    (I*G q (oddOrder j) (w*I)).re=0 ∧
    (I*G q (oddOrder j) (((Real.pi/2:ℝ):ℂ)+w*I)).re=
      -(-1:ℝ)^j*(Real.exp (-(oddOrder j:ℝ)*w)*Real.cos (q*Real.cosh w)) := by
  let n := oddOrder j
  have left : G q n (w*I)=((Real.exp (-(q*Real.sinh w+n*w)):ℝ):ℂ) := by
    rw [G,Complex.sin_mul_I,←Complex.ofReal_sinh,Complex.ofReal_exp]
    congr 1; push_cast; ring_nf; simp [I_sq]; ring
  have phase : Complex.exp ((n:ℂ)*((Real.pi:ℂ)/2*I))=(-1:ℂ)^j*I := by
    rw [Complex.exp_nat_mul,Complex.exp_pi_div_two_mul_I]
    simp [n,oddOrder,pow_succ,pow_mul,I_sq]
  have right : G q n (((Real.pi/2:ℝ):ℂ)+w*I)=
      ((-1:ℂ)^j*I)*(Real.exp (-(n:ℝ)*w):ℂ)*Complex.exp ((q*Real.cosh w:ℝ)*I) := by
    rw [G,Complex.sin_add_mul_I,←Complex.ofReal_sin,←Complex.ofReal_cos,Real.sin_pi_div_two,
      Real.cos_pi_div_two,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,zero_mul,add_zero,one_mul,
      ←Complex.ofReal_cosh,←phase,Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add]
    congr 1; push_cast; ring_nf; simp [I_sq]; ring
  change (I*G q n _).re=0 ∧ (I*G q n _).re=_
  rw [left,right,Complex.exp_mul_I,←Complex.ofReal_sin,←Complex.ofReal_cos]
  constructor
  · simp [Complex.mul_re]
  · rw [show (-1:ℂ)^j=(((-1:ℝ)^j:ℝ):ℂ) by push_cast; rfl]
    simp [Complex.mul_re,Complex.mul_im]; ring

private theorem real_balance (j : ℕ) (q R : ℝ) :
    (∫ x in (0:ℝ)..Real.pi/2,Real.cos (q*Real.sin x+(oddOrder j:ℝ)*x))+
      -(-1:ℝ)^j*(∫ w in (0:ℝ)..R,Real.exp (-(oddOrder j:ℝ)*w)*Real.cos (q*Real.cosh w))=
      (∫ x in (0:ℝ)..Real.pi/2,G q (oddOrder j) ((x:ℂ)+R*I)).re := by
  let n := oddOrder j
  have Z := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (G q n) (⟨0,0⟩:ℂ)
    (⟨Real.pi/2,R⟩:ℂ) (global q n).differentiableOn
  have rb (x : ℝ) : (G q n x).re=Real.cos (q*Real.sin x+(n:ℝ)*x) := by
    rw [G,←Complex.ofReal_sin,←Complex.ofReal_mul,←Complex.ofReal_natCast,←Complex.ofReal_mul,
      ←Complex.ofReal_add,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
    simp
  simp only [Complex.mk_re,Complex.mk_im,Complex.ofReal_zero,zero_mul,add_zero,zero_add,smul_eq_mul] at Z
  simp_rw [←intervalIntegral.integral_const_mul] at Z
  have h := congrArg Complex.re Z
  simp only [Complex.sub_re,Complex.add_re,Complex.zero_re] at h
  have reint {f : ℝ→ℂ} {a b : ℝ} (hf : Continuous f) :
      (∫ u in a..b,f u).re=∫ u in a..b,(f u).re :=
    (intervalIntegral.intervalIntegral_re (hf.intervalIntegrable ..)).symm
  rw [reint ((global q n).continuous.comp Complex.continuous_ofReal),
    reint (f:=fun w : ℝ => I*G q n (((Real.pi/2:ℝ):ℂ)+w*I))
      (by fun_prop (disch := exact (global q n).continuous)),
    reint (f:=fun w : ℝ => I*G q n (w*I))
      (by fun_prop (disch := exact (global q n).continuous))] at h
  simp_rw [rb,(sides q _ j).1,(sides q _ j).2] at h
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_zero,sub_zero] at h
  linarith

theorem quarter (j : ℕ) {q : ℝ} (hq : 0≤q) :
    (Real.pi/2:ℝ)*intJ (oddOrder j) q=(low j q:ℂ)-sign j*(high j q:ℂ) := by
  let n := oddOrder j
  have hn : 0<(n:ℝ) := by exact_mod_cast (show 0<n by dsimp [n,oddOrder]; omega)
  have it : IntegrableOn (fun w : ℝ => Real.exp (-(n:ℝ)*w)*Real.cos (q*Real.cosh w)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hn) 0).mono' (by fun_prop)
    exact ae_of_all _ fun w => by simpa [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (q*Real.cosh w)) (Real.exp_pos _).le
  have T := intervalIntegral_tendsto_integral_Ioi 0 it (tendsto_id (x:=(atTop:Filter ℝ)))
  have top : Tendsto (fun R : ℝ => ∫ x in (0:ℝ)..Real.pi/2,G q n ((x:ℂ)+R*I)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hn))).mul_const (Real.pi/2))
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    simpa only [sub_zero,abs_of_nonneg (by positivity : 0≤Real.pi/2)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => norm_top hq hR (by
        rw [uIoc_of_le (by positivity : 0≤Real.pi/2)] at hx; exact ⟨hx.1.le,hx.2⟩) n))
  have lr := tendsto_nhds_unique
    (tendsto_const_nhds.add (T.const_mul (-(-1:ℝ)^j)))
    (((Complex.continuous_re.tendsto _).comp top).congr (fun R => (real_balance j q R).symm))
  change (∫ x in (0:ℝ)..Real.pi/2,Real.cos (q*Real.sin x+(n:ℝ)*x))+
    -(-1:ℝ)^j*high j q=0 at lr
  simp_rw [Real.cos_add] at lr
  rw [intervalIntegral.integral_sub (by exact (by fun_prop : Continuous _).intervalIntegrable ..)
    (by exact (by fun_prop : Continuous _).intervalIntegrable ..)] at lr
  rw [←sine_quarter j hq,show sign j=(((-1:ℝ)^j:ℝ):ℂ) by simp [sign]]
  norm_cast
  change _=low j q-(-1:ℝ)^j*high j q
  dsimp [low] at *
  linarith

end ImbalancedChen.Part3.OriginalPositiveQuarterContour20261112
end
