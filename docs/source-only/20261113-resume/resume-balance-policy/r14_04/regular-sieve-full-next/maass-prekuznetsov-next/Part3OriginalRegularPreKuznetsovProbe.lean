import ImbalancedChen.Part3ActualUnitBandMellinProbe
import ImbalancedChen.Part3ActualHalfOrderKWronskian

/-! The exponential Poincaré seed in Drappeau (4.27). The half-order
Macdonald factor produces the product of the two shifted coshes. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovProbe20261113
open Set Complex MeasureTheory
open ComplexOrderKBridgeSourceOnly (complexOrderK complexOrderK_real)
open ActualComplexTwoKMellin20261025a
  (actualTwoKMellinDensity actualTwoKMellinDensity_integrable actual_complex_twoK_mellin)
open ImaginaryOrderKFirstMoment20261025a (norm_gamma_half_add_mul_I_sq)
open ImaginaryGammaNormalization20261025a (norm_gamma_one_add_mul_I_sq)
open ActualHalfOrderKWronskianSourceOnly (realOrderK_half_eq_rpow halfKNormalization)

def density (r : ℝ) (ν : ℂ) (q : ℝ) : ℂ :=
  (q:ℂ)^(-((r:ℂ)*I))*complexOrderK (1/2:ℂ) q*complexOrderK ν q

def probe (r : ℝ) (ν : ℂ) := ∫ q in Ioi (0:ℝ),density r ν q

theorem exponential_carrier {q : ℝ} (hq : 0<q) :
    complexOrderK (1/2:ℂ) q=(halfKNormalization*q^(-1/2:ℝ)*Real.exp (-q):ℝ) := by
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,complexOrderK_real,realOrderK_half_eq_rpow hq]

theorem integrable_density (r : ℝ) {ν : ℂ} (hν : |ν.re|<1/2) :
    IntegrableOn (density r ν) (Ioi (0:ℝ)) := by
  let s := 1-(r:ℂ)*I
  have hs : |(1/2:ℂ).re|+|ν.re|<s.re := by
    dsimp only [s]
    norm_num [Complex.sub_re,Complex.mul_re] <;> linarith
  simpa only [actualTwoKMellinDensity,density,show s-1= -((r:ℂ)*I) by dsimp only [s]; ring] using
    (actualTwoKMellinDensity_integrable (nu:=1/2) (mu:=ν) hs)

private def Z (u : ℝ) : ℂ := (1/2:ℂ)+(u:ℂ)*I

private theorem gamma_value (r t : ℝ) :
    probe r ((t:ℂ)*I) =
      (Real.pi:ℂ)*(2:ℂ)^(-1+(r:ℂ)*I)/Gamma (1-(r:ℂ)*I)*
        Gamma (Z (t-r))*Gamma (Z (-(t+r))) := by
  let s := 1-(r:ℂ)*I
  let ν := (t:ℂ)*I
  let a := Z (t-r)
  let b := Z (-(t+r))
  have p1 : (s+(1/2:ℂ)+ν)/2=a/2+1/2 := by dsimp only [s,ν,a,Z]; push_cast; ring
  have p2 : (s+(1/2:ℂ)-ν)/2=b/2+1/2 := by dsimp only [s,ν,b,Z]; push_cast; ring
  have p3 : (s-(1/2:ℂ)+ν)/2=a/2 := by dsimp only [s,ν,a,Z]; push_cast; ring
  have p4 : (s-(1/2:ℂ)-ν)/2=b/2 := by dsimp only [s,ν,b,Z]; push_cast; ring
  have E := actual_complex_twoK_mellin (nu:=(1/2:ℂ)) (mu:=ν) (s:=s)
    (by dsimp [s,ν]; norm_num [Complex.sub_re,Complex.mul_re])
  change probe r ν=_ 
  rw [show probe r ν=∫ q in Ioi (0:ℝ),(q:ℂ)^(s-1)*complexOrderK (1/2:ℂ) q*complexOrderK ν q
    from by simp only [probe,density,show s-1= -((r:ℂ)*I) by dsimp only [s]; ring],E,p1,p2,p3,p4]
  have dup (w : ℂ) : Gamma (w/2)*Gamma (w/2+1/2)=Gamma w*(2:ℂ)^(1-w)*(Real.sqrt Real.pi:ℂ) := by
    simpa only [show 2*(w/2)=w by ring] using Gamma_mul_Gamma_add_half (w/2)
  have two : (2:ℂ)^(s-3)*((2:ℂ)^(1-a)*(2:ℂ)^(1-b))=(2:ℂ)^(-1+(r:ℂ)*I) := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    dsimp only [s,a,b,Z]
    push_cast <;> ring
  have sq : (Real.sqrt Real.pi:ℂ)^2=(Real.pi:ℂ) := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  calc
    _ = ((2:ℂ)^(s-3)/Gamma s)*(Gamma (a/2)*Gamma (a/2+1/2))*(Gamma (b/2)*Gamma (b/2+1/2)) := by ring
    _ = (((2:ℂ)^(s-3)*((2:ℂ)^(1-a)*(2:ℂ)^(1-b)))*(Real.sqrt Real.pi:ℂ)^2/Gamma s)*
        Gamma a*Gamma b := by rw [dup,dup]; ring
    _ = _ := by rw [two,sq]; dsimp only [s,a,b]; ring

def H (t r : ℝ) : ℝ := Real.cosh (Real.pi*t)*Real.cosh (Real.pi*r)/
  (Real.cosh (Real.pi*(t-r))*Real.cosh (Real.pi*(t+r)))

/-- The exact raw-spectral kernel at every real pair, including r=0
and both signs of the observed parameter. No division by sinh at zero. -/
theorem preKuznetsov_multiplier (r t : ℝ) :
    (4/Real.pi^4)*‖Gamma (1-(r:ℂ)*I)‖^2*Real.cosh (Real.pi*r)*‖probe r ((t:ℂ)*I)‖^2 =
      H t r/Real.cosh (Real.pi*t) := by
  have gp : Gamma (1-(r:ℂ)*I)≠0 := Complex.Gamma_ne_zero_of_re_pos
    (by simp [Complex.sub_re,Complex.mul_re])
  have pow : ‖(2:ℂ)^(-1+(r:ℂ)*I)‖=1/2 := by
    rw [show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    norm_num [Complex.add_re,Complex.mul_re]
  have a := norm_gamma_half_add_mul_I_sq (t-r)
  have b := norm_gamma_half_add_mul_I_sq (-(t+r))
  rw [mul_neg,Real.cosh_neg] at b
  rw [gamma_value,norm_mul,norm_mul,norm_div,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le,pow]
  change _=H t r/Real.cosh (Real.pi*t)
  simp only [mul_pow,div_pow,Z,a,b,H]
  field_simp [Real.pi_ne_zero,(norm_ne_zero_iff.mpr gp), (Real.cosh_pos (Real.pi*t)).ne',
    (Real.cosh_pos (Real.pi*(t-r))).ne',(Real.cosh_pos (Real.pi*(t+r))).ne'] <;> ring

theorem positive_half_gamma_norm {r : ℝ} (hr : 0<r) (t : ℝ) :
    ‖probe r ((t:ℂ)*I)‖^2 =
      (Real.pi^3/4)*Real.sinh (Real.pi*r)/
        (r*(Real.cosh (Real.pi*(t-r))*Real.cosh (Real.pi*(t+r)))) := by
  have G := norm_gamma_one_add_mul_I_sq (-r) (neg_ne_zero.mpr hr.ne')
  simp only [Complex.ofReal_neg,neg_mul,←sub_eq_add_neg,mul_neg,Real.sinh_neg,neg_div_neg_eq] at G
  have P := preKuznetsov_multiplier r t
  rw [G,H] at P
  have sh : 0<Real.sinh (Real.pi*r) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hr)
  let A := (4/Real.pi^4)*(Real.pi*r/Real.sinh (Real.pi*r))*Real.cosh (Real.pi*r)
  have a0 : A≠0 := by
    dsimp only [A]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero (by norm_num) (pow_ne_zero _ Real.pi_ne_zero))
      (div_ne_zero (mul_ne_zero Real.pi_ne_zero hr.ne') sh.ne'))
      (Real.cosh_pos _).ne'
  apply mul_left_cancel₀ a0
  calc
    A*‖probe r ((t:ℂ)*I)‖^2 = _ := P
    _ = _ := by
      dsimp only [A]
      field_simp [hr.ne',Real.pi_ne_zero,sh.ne',(Real.cosh_pos (Real.pi*t)).ne',
        (Real.cosh_pos (Real.pi*(t-r))).ne',(Real.cosh_pos (Real.pi*(t+r))).ne'] <;> ring

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovProbe20261113
end
