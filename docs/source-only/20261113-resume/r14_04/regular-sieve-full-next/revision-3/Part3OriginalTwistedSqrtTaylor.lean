import ImbalancedChen.Part3OriginalTwistedSqrtAnalysis

/-! Exact separated exponential series for the physical twist
exp(-lam sqrt(mn)) e(2θ sqrt(mn)/c). The n coordinate is independent of
the m block. Its common normalization allows the Gram estimate on every
Taylor term. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalTwistedSqrtTaylor20261113
open Complex Set
open OAI.Problem337.ExponentialSum (phase phase_norm)
open OriginalTwistedSqrtGram20261113 (anchor)
open OriginalTwistedSqrtAnalysis20261113 (mode primaryAngle)

def coord (x w : ℝ) := (w-x)/x
def complexSlope (lam θ c x y v : ℝ) : ℂ :=
  (-(lam*x*(y-x)):ℝ)+(4*Real.pi*θ/c*x*(y-v):ℝ)*I
def leftWeight (lam θ c x y v : ℝ) (j : ℕ) : ℂ :=
  (Real.exp (-lam*y*x):ℂ)*phase (2*θ/c*(y-v)*x)*
    (complexSlope lam θ c x y v)^j/(j.factorial:ℂ)
def rightWeight (lam x w : ℝ) (j : ℕ) : ℂ :=
  (Real.exp (-lam*x*(w-x)):ℂ)*(coord x w:ℂ)^j
def fullFactor (lam θ c y w : ℝ) : ℂ :=
  (Real.exp (-lam*y*w):ℂ)*phase (2*θ/c*y*w)
def weightBill (M : ℕ) (lam : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-lam*M)*((lam*M+4*Real.pi)^j/j.factorial)

theorem weightBill_sum (M : ℕ) (lam : ℝ) :
    HasSum (weightBill M lam) (Real.exp (4*Real.pi)) := by
  have H : HasSum (fun j : ℕ => (lam*(M:ℝ)+4*Real.pi)^j/j.factorial)
      (Real.exp (lam*M+4*Real.pi)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (lam*M+4*Real.pi)
  have E : Real.exp (-lam*M)*Real.exp (lam*M+4*Real.pi)=Real.exp (4*Real.pi) := by
    rw [←Real.exp_add];congr 1;ring
  rw [←E]
  exact H.mul_left (Real.exp (-lam*M))

theorem weightBill_nonneg (M : ℕ) {lam : ℝ} (hlam : 0≤lam) (j : ℕ) : 0≤weightBill M lam j := by
  dsimp [weightBill]; positivity

theorem factor_hasSum (lam θ c x y v w : ℝ) (hx : 0<x) :
    HasSum (fun j : ℕ => leftWeight lam θ c x y v j*rightWeight lam x w j*
        phase (2*θ/c*v*w)) (fullFactor lam θ c y w) := by
  let p := (Real.exp (-lam*y*x):ℂ)*phase (2*θ/c*(y-v)*x)
  let q := (Real.exp (-lam*x*(w-x)):ℂ)*phase (2*θ/c*v*w)
  let z := complexSlope lam θ c x y v
  let t : ℂ := (coord x w : ℝ)
  have H : HasSum (fun j : ℕ => (z*t)^j/j.factorial) (exp (z*t)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z*t)
  have E : p*q*exp (z*t)=fullFactor lam θ c y w := by
    unfold fullFactor
    dsimp only [p,q,z,t,phase,complexSlope,coord]
    simp only [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    have hxc : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
    field_simp [hxc] <;> ring
  rw [←E]
  refine ((H.mul_left (p*q)).congr_fun ?_)
  intro j
  simp only [p,q,z,t,leftWeight,rightWeight,mul_pow]
  ring

private theorem root_step_bound {M A m c θ : ℝ} (hM : 0<M) (hA : M≤A) (hm : A≤m)
    (hstep : m-A≤c) (hc : 0<c) (hθ : θ∈Icc 0 2) :
    |4*Real.pi*θ/c*Real.sqrt M*(Real.sqrt m-Real.sqrt A)|≤4*Real.pi := by
  have x := Real.sqrt_pos.mpr hM
  have v := Real.sqrt_le_sqrt hA
  have y := Real.sqrt_le_sqrt hm
  have hv := hM.trans_le hA
  have hy := hv.trans_le hm
  have den : 2*Real.sqrt M≤Real.sqrt m+Real.sqrt A := by linarith only [v,y]
  have diff := sub_nonneg.mpr y
  have cut := mul_le_mul_of_nonneg_left den diff
  have sqM := Real.sq_sqrt hy.le
  have sqA := Real.sq_sqrt hv.le
  have d : 2*(Real.sqrt M*(Real.sqrt m-Real.sqrt A))≤c := by
    nlinarith only [cut,sqM,sqA,hstep]
  have z : θ*(Real.sqrt M*(Real.sqrt m-Real.sqrt A))≤c :=
    (mul_le_mul_of_nonneg_right hθ.2 (mul_nonneg x.le diff)).trans d
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by positivity) hθ.1) hc.le) x.le) diff)]
  have h := mul_le_mul_of_nonneg_left z (show 0≤4*Real.pi by positivity)
  apply (mul_le_mul_iff_left₀ hc).mp
  have E : 4*Real.pi*θ/c*Real.sqrt M*(Real.sqrt m-Real.sqrt A)*c=
      4*Real.pi*(θ*(Real.sqrt M*(Real.sqrt m-Real.sqrt A))) := by field_simp [hc.ne'] <;>ring
  rw [E]
  exact h

theorem leftWeight_norm {M : ℕ} (hM : 0<M) {lam θ c A m : ℝ} (hlam : 0≤lam)
    (hc : 0<c) (hθ : θ∈Icc 0 2) (hA : (M:ℝ)≤A) (hm : A≤m) (h2 : m≤2*M)
    (hstep : m-A≤c) (j : ℕ) :
    ‖leftWeight lam θ c (Real.sqrt M) (Real.sqrt m) (Real.sqrt A) j‖≤weightBill M lam j := by
  let x := Real.sqrt (M:ℝ)
  let y := Real.sqrt m
  let v := Real.sqrt A
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have xp : 0<x := Real.sqrt_pos.mpr mp
  have xp2 : x^2=M := Real.sq_sqrt mp.le
  have xy : x≤y := Real.sqrt_le_sqrt (hA.trans hm)
  have y2 : y≤2*x := by
    apply Real.sqrt_le_iff.mpr ⟨mul_nonneg (by norm_num) xp.le,?_⟩
    nlinarith only [h2,xp2,mp]
  have r0 : 0≤lam*x*(y-x) := mul_nonneg (mul_nonneg hlam xp.le) (sub_nonneg.mpr xy)
  have reBound : lam*x*(y-x)≤lam*M := by
    have h := mul_le_mul_of_nonneg_left (show y-x≤x by linarith only [y2]) xp.le
    have := mul_le_mul_of_nonneg_left (show x*(y-x)≤M by nlinarith only [h,xp2]) hlam
    linarith only [this]
  have zBound : ‖complexSlope lam θ c x y v‖≤lam*M+4*Real.pi := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_neg,
      abs_of_nonneg r0]
    exact add_le_add reBound (root_step_bound mp hA hm hstep hc hθ)
  have ed : Real.exp (-lam*y*x)≤Real.exp (-lam*M) := by
    apply Real.exp_le_exp.mpr
    have yx := mul_le_mul_of_nonneg_right xy xp.le
    have := mul_le_mul_of_nonneg_left (show (M:ℝ)≤y*x by nlinarith only [yx,xp2]) hlam
    linarith only [this]
  change ‖leftWeight lam θ c x y v j‖≤_
  simp only [leftWeight,weightBill,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),phase_norm,mul_one,norm_pow,Complex.norm_natCast]
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul ed (pow_le_pow_left₀ (norm_nonneg _) zBound _) (by positivity) (Real.exp_pos _).le

theorem rightWeight_norm {M n lam : ℝ} (hM : 0<M) (hlam : 0≤lam) (hn : n∈Icc M (2*M))
    (j : ℕ) : ‖rightWeight lam (Real.sqrt M) (Real.sqrt n) j‖≤1 := by
  let x := Real.sqrt M
  let w := Real.sqrt n
  have xp : 0<x := Real.sqrt_pos.mpr hM
  have xw : x≤w := Real.sqrt_le_sqrt hn.1
  have w2 : w≤2*x := by
    apply Real.sqrt_le_iff.mpr ⟨mul_nonneg (by norm_num) xp.le,?_⟩
    change n≤(2*Real.sqrt M)^2
    nlinarith only [Real.sq_sqrt hM.le,hn.2,hM]
  have c0 : 0≤coord x w := div_nonneg (sub_nonneg.mpr xw) xp.le
  have c1 : coord x w≤1 := (div_le_iff₀ xp).mpr (by linarith only [w2])
  have e1 : Real.exp (-lam*x*(w-x))≤1 := Real.exp_le_one_iff.mpr (by
    have := mul_nonneg (mul_nonneg hlam xp.le) (sub_nonneg.mpr xw)
    linarith only [this])
  change ‖rightWeight lam x w j‖≤1
  simp only [rightWeight,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),abs_of_nonneg c0]
  exact mul_le_one₀ e1 (pow_nonneg c0 _) (pow_le_one₀ c0 c1)

end ImbalancedChen.Part3.OriginalTwistedSqrtTaylor20261113
end
