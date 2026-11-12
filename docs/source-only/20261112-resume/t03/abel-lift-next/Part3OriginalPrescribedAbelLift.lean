import ImbalancedChen.Part3OriginalAbelGaussian

/-! Every mixed log derivative of the actual two-height lift, with a
common positive product floor and arbitrary exponential box weights. -/
namespace ImbalancedChen.Part3.OriginalPrescribedAbelLift20261112
noncomputable section
open scoped ContDiff Topology
open Set Filter Real MeasureTheory Complex
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalAbelGaussian OriginalPrescribedAbelProfile

def H_ab := height
def logLift (ell : D4→ℤ) (Y x y : ℝ) : ℂ := H_ab ell Y (Real.exp x) (Real.exp y)

private def α : ℝ := 4*Real.pi^2
private def atomAt (ell : D4→ℤ) (Y u v : ℝ) (j : ℕ) (r w : ℝ) : ℂ :=
  (Real.exp (u*r+v*w-α*Real.sinh w^2):ℂ)*iteratedDeriv j (f ell Y) (Real.exp r)
private def atom (ell : D4→ℤ) (Y u v : ℝ) (j : ℕ) (x y : ℝ) : ℂ :=
  atomAt ell Y u v j (x+y) ((x-y)/2)

private lemma profile_formula (ell : D4→ℤ) (Y x y : ℝ) :
    logLift ell Y x y=(Real.sqrt Real.pi:ℂ)*
      (atom ell Y (3/2) 1 0 x y + atom ell Y (3/2) (-1) 0 x y) := by
  let r := x+y
  let w := (x-y)/2
  have P : Real.exp x*Real.exp y=Real.exp r := (Real.exp_add x y).symm
  have sq : Real.sqrt (Real.exp r)=Real.exp (r/2) := by
    have q : Real.exp (r/2)^2=Real.exp r := by rw [sq,←Real.exp_add]; congr 1; ring
    rw [←q,Real.sqrt_sq (Real.exp_pos _).le]
  have lr : Real.log (Real.exp x/Real.exp y)/2=w := by rw [←Real.exp_sub,Real.log_exp]
  have angular (v : ℝ) : Real.exp ((3/2)*r+v*w-α*Real.sinh w^2)=
      Real.exp r*Real.exp (r/2)*Real.exp (v*w)*Real.exp (-α*Real.sinh w^2) := by
    rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]; congr 1; ring
  change height ell Y (Real.exp x) (Real.exp y)=(Real.sqrt Real.pi:ℂ)*
    (atomAt ell Y (3/2) 1 0 r w+atomAt ell Y (3/2) (-1) 0 r w)
  rw [height,if_pos ⟨Real.exp_pos _,Real.exp_pos _⟩,P,lr,h,sq]
  simp only [atomAt,angular,iteratedDeriv_zero,one_mul,neg_one_mul,g,
    Real.cosh_eq,α,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_add]
  push_cast; ring

theorem logLift_smooth (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    ContDiff ℝ ∞ (fun z : ℝ×ℝ => logLift ell Y z.1 z.2) := by
  simp_rw [profile_formula,atom,atomAt,iteratedDeriv_zero]
  have hf := f_smooth ell hY
  fun_prop

theorem logLift_below (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (x y : ℝ)
    (hp : Real.exp (x+y)≤(Y/(64*Real.pi))^2) : logLift ell Y x y=0 := by
  have Z := f_jet_below ell hY 0 hp
  simp only [iteratedDeriv_zero] at Z
  simp [logLift,H_ab,height,h,←Real.exp_add,Z]

private lemma amp_jet (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (j : ℕ) (r : ℝ) :
    HasDerivAt (iteratedDeriv j (f ell Y)) (iteratedDeriv (j+1) (f ell Y) r) r := by
  rw [iteratedDeriv_succ]
  exact ((f_smooth ell hY).differentiable_iteratedDeriv j (by simp) r).hasDerivAt

private def atomD (ell : D4→ℤ) (Y u v : ℝ) (j : ℕ) (c r w : ℝ) : ℂ :=
  ((u+c*v:ℝ):ℂ)*atomAt ell Y u v j r w + atomAt ell Y (u+1) v (j+1) r w +
  ((-(α*c/2):ℝ):ℂ)*atomAt ell Y u (v+2) j r w +
  ((α*c/2:ℝ):ℂ)*atomAt ell Y u (v-2) j r w

private lemma along (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (u v : ℝ) (j : ℕ)
    {r w : ℝ→ℝ} {t c : ℝ} (dr : HasDerivAt r 1 t) (dw : HasDerivAt w c t) :
    HasDerivAt (fun z => atomAt ell Y u v j (r z) (w z))
      (atomD ell Y u v j c (r t) (w t)) t := by
  let b := u*r t+v*w t-α*Real.sinh (w t)^2
  have d := (((dr.const_mul u).add (dw.const_mul v)).sub
    ((((Real.hasDerivAt_sinh _).comp t dw).pow 2).const_mul α)).exp
  have e1 := ((amp_jet ell hY j (Real.exp (r t))).scomp t dr.exp)
  convert d.ofReal_comp.mul e1 using 1
  dsimp [atomD,atomAt,b]
  rw [show (u+1)*r t+v*w t-α*Real.sinh (w t)^2 =
      (u*r t+v*w t-α*Real.sinh (w t)^2)+r t by ring,Real.exp_add,
      show u*r t+(v+2)*w t-α*Real.sinh (w t)^2 =
      (u*r t+v*w t-α*Real.sinh (w t)^2)+(w t+w t) by ring,Real.exp_add,
      show u*r t+(v-2)*w t-α*Real.sinh (w t)^2 =
      (u*r t+v*w t-α*Real.sinh (w t)^2)+(-w t + -w t) by ring,Real.exp_add]
  simp only [Real.exp_add,Real.sinh_eq,Real.cosh_eq,Real.exp_neg,
    Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_sub,
    Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_pow]
  push_cast; field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_pos (w t)).ne']; ring

private def Rapid (A : ℝ) (G : ℝ→ℝ→ℂ) : Prop :=
  ∃C:ℝ, 0≤C ∧ ∀x y, ‖G x y‖≤C*Real.exp (-A*(|x|+|y|))

private lemma atom_rapid (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (u v : ℝ) (j : ℕ)
    (A : ℝ) (hA : 0≤A) : Rapid A (atom ell Y u v j) := by
  obtain ⟨C,hC,hj⟩ := f_jet_decay ell hY j
  let m := |Real.log (lo Y)|
  let U := |u|+A
  let V := |v|+2*A
  let K := U^2+U*m+V^2
  refine ⟨C*Real.exp K,by positivity,?_⟩
  intro x y
  let r := x+y
  let w := (x-y)/2
  by_cases hr : Real.exp r≤lo Y
  · simp only [atom,atomAt,show x+y=r from rfl,f_jet_below ell hY j hr,mul_zero,norm_zero]
    positivity
  have lm : -m≤r := by
    have ht := Real.log_le_log (lo_pos hY) (le_of_not_ge hr)
    rw [Real.log_exp] at ht
    exact (neg_abs_le _).trans ht
  have hU : 0≤U := add_nonneg (abs_nonneg _) hA
  have hV : 0≤V := add_nonneg (abs_nonneg _) (by positivity)
  have radial : U*|r|-Real.exp r/2≤U^2+U*m := by
    by_cases rr : 0≤r
    · have hp := Real.pow_div_factorial_le_exp rr 2
      norm_num at hp; rw [abs_of_nonneg rr]
      nlinarith [sq_nonneg (r/2-U),mul_nonneg hU (abs_nonneg (Real.log (lo Y)))]
    · rw [abs_of_nonpos (le_of_not_ge rr)]
      nlinarith [mul_le_mul_of_nonneg_left (by linarith : -r≤m) hU,Real.exp_pos r,sq_nonneg U]
  have sh : |w|≤|Real.sinh w| := (Real.self_le_sinh_iff.mpr (abs_nonneg w)).trans_eq
    (Real.abs_sinh w).symm
  have hs : w^2≤Real.sinh w^2 := (sq_le_sq).mpr sh
  have ha : 1≤α := by dsimp [α]; nlinarith [Real.pi_gt_three,sq_nonneg (Real.pi-3)]
  have tang : V*|w|-α*Real.sinh w^2≤V^2 := by
    nlinarith [sq_nonneg (|w|-V/2),sq_abs w,mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (Real.sinh w)),sq_nonneg V]
  have hx : x=r/2+w := by dsimp [r,w]; ring
  have hy : y=r/2-w := by dsimp [r,w]; ring
  have xy : |x|+|y|≤|r|+2*|w| := by
    calc _ ≤ |r/2|+|w|+(|r/2|+|w|) :=
           add_le_add ((congrArg abs hx).trans_le (abs_add_le _ _))
             ((congrArg abs hy).trans_le (abs_sub _ _))
         _ = _ := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; ring
  have ex : u*r+v*w-α*Real.sinh w^2-Real.exp r/2 ≤ K-A*(|x|+|y|) := by
    have ur := (le_abs_self (u*r)).trans_eq (abs_mul u r)
    have vw := (le_abs_self (v*w)).trans_eq (abs_mul v w)
    have t := mul_le_mul_of_nonneg_left xy hA
    dsimp only [K,U,V] at radial tang ⊢
    nlinarith only [radial,tang,ur,vw,t]
  change ‖(Real.exp _:ℂ)*iteratedDeriv j (f ell Y) (Real.exp r)‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (u*r+v*w-α*Real.sinh w^2)*(C*Real.exp (-Real.exp r/2)) := by gcongr; exact hj _
    _ = C*Real.exp (u*r+v*w-α*Real.sinh w^2-Real.exp r/2) := by
      rw [show u*r+v*w-α*Real.sinh w^2-Real.exp r/2=
        (u*r+v*w-α*Real.sinh w^2)+(-Real.exp r/2) by ring,Real.exp_add]; ring
    _ ≤ C*Real.exp (K-A*(|x|+|y|)) := by gcongr
    _ = _ := by rw [show K-A*(|x|+|y|)=K+(-A*(|x|+|y|)) by ring,Real.exp_add]; ring

private inductive Terms (ell : D4→ℤ) (Y : ℝ) : (ℝ→ℝ→ℂ) → Prop
  | basic (u v : ℝ) (j : ℕ) : Terms ell Y (atom ell Y u v j)
  | add {G J} : Terms ell Y G → Terms ell Y J → Terms ell Y (fun x y => G x y+J x y)
  | scale (z : ℂ) {G} : Terms ell Y G → Terms ell Y (fun x y => z*G x y)

private lemma Terms.smooth {ell : D4→ℤ} {Y : ℝ} (hY : 0<Y) {G} (mem : Terms ell Y G) :
    ContDiff ℝ ∞ (fun p:ℝ×ℝ => G p.1 p.2) := by
  induction mem with
  | basic u v j =>
      have J := smooth_jet (f_smooth ell hY) j
      unfold atom atomAt; fun_prop
  | add h k ih ik => exact ih.add ik
  | scale c h ih => exact contDiff_const.mul ih

private lemma Terms.rapid {ell : D4→ℤ} {Y : ℝ} (hY : 0<Y) {G} (mem : Terms ell Y G)
    (A : ℝ) (hA : 0≤A) : Rapid A G := by
  induction mem with
  | basic u v j => exact atom_rapid ell hY u v j A hA
  | scale z h ih =>
      obtain ⟨C,hC,B⟩ := ih
      exact ⟨‖z‖*C,by positivity,fun x y => by rw [norm_mul,mul_assoc]; gcongr; exact B x y⟩
  | add h k ih ik =>
      obtain ⟨C,hC,B⟩ := ih; obtain ⟨D,hD,H⟩ := ik
      exact ⟨C+D,by positivity,fun x y => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add (B x y) (H x y))⟩

private lemma d_terms (ell : D4→ℤ) (Y u v : ℝ) (j : ℕ) (c : ℝ) :
    Terms ell Y (fun x y => atomD ell Y u v j c (x+y) ((x-y)/2)) :=
  .add (.add (.add (.scale _ (.basic u v j)) (.basic (u+1) v (j+1)))
    (.scale _ (.basic u (v+2) j))) (.scale _ (.basic u (v-2) j))

private lemma both_derivatives {ell : D4→ℤ} {Y : ℝ} (hY : 0<Y) {G} (mem : Terms ell Y G) :
    Terms ell Y (fun x y => deriv (fun z => G z y) x) ∧
    Terms ell Y (fun x y => deriv (G x) y) := by
  induction mem with
  | basic u v j =>
    constructor
    · convert d_terms ell Y u v j (1/2) using 1
      funext x y
      exact (along ell hY u v j (by simpa using (hasDerivAt_id x).add_const y)
        (by simpa using ((hasDerivAt_id x).sub_const y).div_const 2)).deriv
    · convert d_terms ell Y u v j (-1/2) using 1
      funext x y
      exact (along ell hY u v j (by simpa using (hasDerivAt_id y).const_add x)
        (by simpa using ((hasDerivAt_id y).const_sub x).div_const 2)).deriv
  | @add G J h k ih ik =>
    have h1 := h.smooth hY; have h2 := k.smooth hY
    constructor
    · convert Terms.add ih.1 ik.1 using 1; funext x y
      exact deriv_fun_add
        ((h1.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x)
        ((h2.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x)
    · convert Terms.add ih.2 ik.2 using 1; funext x y
      exact deriv_fun_add
        ((h1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y)
        ((h2.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y)
  | scale c h ih =>
    exact ⟨by convert Terms.scale c ih.1 using 1; funext x y; exact deriv_const_mul_field c,
           by convert Terms.scale c ih.2 using 1; funext x y; exact deriv_const_mul_field c⟩

private lemma y_terms (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (j : ℕ) :
    Terms ell Y (fun x y => iteratedDeriv j (logLift ell Y x) y) := by
  have base : Terms ell Y (logLift ell Y) := by
    convert Terms.scale (Real.sqrt Real.pi:ℂ)
      (Terms.add (.basic (ell := ell) (Y := Y) (3/2) 1 0) (.basic (3/2) (-1) 0)) using 1
    funext x y; exact profile_formula ell Y x y
  induction j with
  | zero => exact base
  | succ j ih => simpa only [iteratedDeriv_succ] using (both_derivatives hY ih).2

/-- The order is first in the second height and then in the first. -/
theorem logLift_jets (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (i j : ℕ) (A : ℝ) (hA : 0≤A) :
    ∃C:ℝ, 0≤C ∧ ∀x y, ‖iteratedDeriv i (fun s => iteratedDeriv j (logLift ell Y s) y) x‖
      ≤ C*Real.exp (-A*(|x|+|y|)) := by
  have xs : ∀i:ℕ,Terms ell Y (fun x y => iteratedDeriv i
      (fun s => iteratedDeriv j (logLift ell Y s) y) x) := by
    intro b; induction b with
    | zero => exact y_terms ell hY j
    | succ b ih => simpa only [iteratedDeriv_succ] using (both_derivatives hY ih).1
  exact (xs i).rapid hY A hA

theorem H_ab_below (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) {a b : ℝ}
    (hab : a*b≤(Y/(64*Real.pi))^2) : H_ab ell Y a b=0 := by
  by_cases h₀ : 0<a ∧ 0<b
  · have hz := f_jet_below ell hY 0 hab
    simp only [iteratedDeriv_zero] at hz
    simp [H_ab,height,h₀,h,hz]
  · simp [H_ab,height,h₀]

/-- The logarithmic derivative on physical positive heights. -/
def euler (U : ℝ→ℂ) (a : ℝ) : ℂ := a • deriv U a

private lemma euler_at_log {U V : ℝ→ℂ} (hV : ContDiff ℝ ∞ V)
    (agree : ∀a:ℝ, 0<a → U a=V (Real.log a)) (i : ℕ) :
    ∀a:ℝ, 0<a → (euler^[i] U) a=iteratedDeriv i V (Real.log a) := by
  induction i with
  | zero => exact agree
  | succ i ih =>
    intro a ha
    have near : (euler^[i] U) =ᶠ[𝓝 a] (fun z => iteratedDeriv i V (Real.log z)) := by
      filter_upwards [lt_mem_nhds ha] with z hz
      exact ih z hz
    have H := ((smooth_jet hV i).differentiable (by simp) (Real.log a)).hasDerivAt.scomp a
      (Real.hasDerivAt_log ha.ne')
    rw [Function.iterate_succ_apply',euler,near.deriv_eq,H.deriv,smul_smul,
      mul_inv_cancel₀ ha.ne',one_smul,iteratedDeriv_succ]

/-- Mixed Euler derivatives of the physical H itself, before the
change to log coordinates used for Fourier expansion. -/
theorem H_ab_euler_jets (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (i j : ℕ) (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀a b:ℝ,0<a → 0<b →
      ‖(euler^[i] (fun v => (euler^[j] (H_ab ell Y v)) b)) a‖ ≤
        C*Real.exp (-A*(|Real.log a|+|Real.log b|)) := by
  obtain ⟨C,hC,B⟩ := logLift_jets ell hY i j A hA
  refine ⟨C,hC,?_⟩
  intro a b ha hb
  let V := fun x => iteratedDeriv j (logLift ell Y x) (Real.log b)
  have smoothV : ContDiff ℝ ∞ V :=
    ((y_terms ell hY j).smooth hY).comp (contDiff_id.prodMk contDiff_const)
  have inner (v : ℝ) (hv : 0<v) : (euler^[j] (H_ab ell Y v)) b=V (Real.log v) := by
    have H := (logLift_smooth ell hY).comp
      ((contDiff_const (c := Real.log v)).prodMk contDiff_id)
    apply euler_at_log H _ j b hb
    intro y hy
    simp [logLift,Real.exp_log hv,Real.exp_log hy]
  rw [euler_at_log smoothV inner i a ha]
  exact B (Real.log a) (Real.log b)

end
end ImbalancedChen.Part3.OriginalPrescribedAbelLift20261112
