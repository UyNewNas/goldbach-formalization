import ImbalancedChen.Part3OriginalHolomorphicPoincare
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace ImbalancedChen.Part3.OriginalHeckeFourierKernel20261112

noncomputable section
open Real Complex Set MeasureTheory Filter
open scoped Topology FourierTransform

def resolvent (u : ℝ) : ℂ := ((u:ℂ)+I)⁻¹
def column (u : ℝ) : ℝ := (1+u^2)⁻¹
def realPower (s u : ℝ) : ℝ := (1+u^2)^(-s)
def kernel (k : ℕ) (s M u : ℝ) : ℂ :=
  (resolvent u)^k * (realPower s u : ℂ) * Complex.exp (-I*(M:ℂ)*resolvent u)

def logD (k : ℕ) (s M u : ℝ) : ℂ :=
  -(k:ℂ)*resolvent u-2*(s:ℂ)*u*column u + I*M*resolvent u^2
def logD' (k : ℕ) (s M u : ℝ) : ℂ :=
  (k:ℂ)*resolvent u^2-2*(s:ℂ)*column u+4*(s:ℂ)*((u:ℂ)*column u)^2
    -2*I*M*resolvent u^3

private theorem nz (u : ℝ) : (u:ℂ)+I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi

private theorem resD (u : ℝ) : HasDerivAt resolvent (-(resolvent u)^2) u := by
  have h := ((hasDerivAt_id u).ofReal_comp.add_const I).inv (nz u)
  simpa [resolvent,inv_pow,one_div] using h

private theorem resPowerD (k : ℕ) (u : ℝ) :
    HasDerivAt (fun x => resolvent x^k) (resolvent u^k * (-(k:ℂ)*resolvent u)) u := by
  induction k with
  | zero => simpa using (hasDerivAt_const u (1:ℂ))
  | succ k hk =>
    simpa only [pow_succ,Nat.cast_succ] using
      ((hk.mul (resD u)).congr_deriv (by ring))

private theorem colD (u : ℝ) : HasDerivAt column (-2*u*column u^2) u := by
  have h := (((hasDerivAt_id u).pow 2).const_add 1).inv (by positivity)
  convert h using 1 <;> simp [column,inv_pow,div_eq_mul_inv] <;> ring

private theorem powerD (s u : ℝ) :
    HasDerivAt (realPower s) (realPower s u*(-2*s*u*column u)) u := by
  have h := (((hasDerivAt_id u).pow 2).const_add 1).rpow_const
    (p := -s) (Or.inl (by positivity))
  convert h using 1
  simp only [realPower,column,Real.rpow_sub_one (by positivity : 1+u^2≠0),pow_one]
  ring

theorem kernel_D (k : ℕ) (s M u : ℝ) :
    HasDerivAt (kernel k s M) (kernel k s M u * logD k s M u) u := by
  have h := ((resPowerD k u).mul (powerD s u).ofReal_comp).mul
    (((resD u).const_mul (-I*(M:ℂ))).cexp)
  convert h using 1
  dsimp only [kernel,logD]
  push_cast;ring

private theorem log_D (k : ℕ) (s M u : ℝ) :
    HasDerivAt (logD k s M) (logD' k s M u) u := by
  have h := (((resD u).const_mul (-(k:ℂ))).sub
    ((((hasDerivAt_id u).ofReal_comp).const_mul (2*(s:ℂ))).mul (colD u).ofReal_comp)).add
      (((resD u).pow 2).const_mul (I*(M:ℂ)))
  convert h using 1
  dsimp only [logD']; push_cast;ring

theorem kernel_DD (k : ℕ) (s M u : ℝ) :
    HasDerivAt (fun x => kernel k s M x*logD k s M x)
      (kernel k s M u * (logD k s M u^2+logD' k s M u)) u :=
  ((kernel_D k s M u).mul (log_D k s M u)).congr_deriv (by ring)

private theorem col_bounds (u : ℝ) : 0≤column u ∧ column u≤1 ∧ |u|*column u≤1 := by
  have h : 0<1+u^2 := by positivity
  refine ⟨inv_nonneg.mpr h.le, inv_le_one_of_one_le₀ (by dsimp [column]; nlinarith [sq_nonneg u]),?_⟩
  rw [column,← div_eq_mul_inv,div_le_one h]
  nlinarith [sq_nonneg (|u|-1),sq_abs u]

private theorem res_sq (u : ℝ) : ‖resolvent u‖^2=column u := by
  rw [resolvent,norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply,column]
  congr 1;simp;ring

private theorem exp_norm (M u : ℝ) (hM : 0≤M) :
    ‖Complex.exp (-I*(M:ℂ)*resolvent u)‖≤1 := by
  rw [Complex.norm_exp,Real.exp_le_one_iff]
  simp [resolvent, Complex.inv_im, Complex.mul_re, Complex.mul_im]
  positivity

theorem kernel_le {k : ℕ} (hk : 2≤k) {s M : ℝ} (hs : 0≤s) (hM : 0≤M) (u : ℝ) :
    ‖kernel k s M u‖≤column u := by
  have hr : ‖resolvent u‖≤1 := by nlinarith [res_sq u,(col_bounds u).2.1,norm_nonneg (resolvent u)]
  have hp : ‖(realPower s u : ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg (by dsimp [realPower]; positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg u]) (neg_nonpos.mpr hs)
  rw [kernel,norm_mul,norm_mul,norm_pow,← res_sq]
  simpa using mul_le_mul (mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hr hk) hp
    (norm_nonneg _) (by positivity)) (exp_norm M u hM) (norm_nonneg _) (by positivity)

private theorem log_bounds (k : ℕ) {s M A : ℝ} (hs : s∈Icc (0:ℝ) 1)
    (hM : M∈Icc (0:ℝ) A) (u : ℝ) :
    ‖logD k s M u‖ ≤ k+2+A ∧ ‖logD' k s M u‖ ≤ k+6+2*A := by
  have hr : ‖resolvent u‖≤1 := by nlinarith [res_sq u,(col_bounds u).2.1,norm_nonneg (resolvent u)]
  have h1 : ‖(column u:ℂ)‖≤1 := by simpa [Real.norm_of_nonneg (col_bounds u).1] using (col_bounds u).2.1
  have h2 : ‖(u:ℂ)*(column u:ℂ)‖≤1 := by
    simpa [norm_mul,Real.norm_eq_abs,abs_of_nonneg (col_bounds u).1] using (col_bounds u).2.2
  have hs' : ‖(s:ℂ)‖≤1 := by simpa [Real.norm_of_nonneg hs.1] using hs.2
  have hM' : ‖(M:ℂ)‖≤A := by simpa [Real.norm_of_nonneg hM.1] using hM.2
  constructor
  · unfold logD
    rw [show 2*(s:ℂ)*u*column u = (2*(s:ℂ))*((u:ℂ)*column u) by ring]
    refine (norm_add_le ..).trans ((add_le_add_right (norm_sub_le ..) _).trans ?_)
    simp only [norm_mul,norm_neg,norm_natCast,norm_ofNat,Complex.norm_I,one_mul,norm_pow] at *
    calc
      _ ≤ (k:ℝ)*1+2*1*1+A*1^2 := by gcongr
      _ = _ := by ring
  · unfold logD'
    refine (norm_sub_le ..).trans ((add_le_add_right (norm_add_le ..) _).trans ?_)
    refine (add_le_add_right (add_le_add_right (norm_sub_le ..) _) _).trans ?_
    simp only [norm_mul,norm_natCast,norm_ofNat,Complex.norm_I,one_mul,mul_one,norm_pow] at *
    calc
      _ ≤ (k:ℝ)*1^2+2*1*1+4*1*1^2+2*A*1^3 := by gcongr
      _ = _ := by ring

def fourierCost (k : ℕ) (A : ℝ) := (k+2+A)^2+(k+6+2*A)

private theorem Fourier_L1 (f : ℝ→ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖≤∫ u,‖f u‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  exact .of_forall fun u => by simp [norm_smul,Complex.norm_exp]

/-- Uniform in s∈[0,1] and M∈[0,A]. Both derivatives in the integrations by parts
are those of the original rational–exponential kernel. -/
theorem Fourier_bounds {k : ℕ} (hk : 2≤k) {s M A : ℝ} (hs : s∈Icc (0:ℝ) 1)
    (hM : M∈Icc (0:ℝ) A) (ξ : ℝ) :
    ‖𝓕 (kernel k s M) ξ‖≤Real.pi ∧
      (2*Real.pi*|ξ|)^2 * ‖𝓕 (kernel k s M) ξ‖ ≤ fourierCost k A*Real.pi := by
  let f := kernel k s M
  let f' := fun x => f x*logD k s M x
  let f'' := fun x => f x*(logD k s M x^2+logD' k s M x)
  have hc : Integrable column := integrable_inv_one_add_sq
  have hf (x : ℝ) := kernel_le hk hs.1 hM.1 x
  have h' (x : ℝ) : ‖f' x‖≤((k:ℝ)+2+A)*column x := by
    rw [mul_comm];exact (norm_mul _ _).le.trans (mul_le_mul (hf x) (log_bounds k hs hM x).1
      (norm_nonneg _) (col_bounds x).1)
  have h'' (x : ℝ) : ‖f'' x‖≤fourierCost k A*column x := by
    change ‖f x*(_+_)‖≤_
    rw [norm_mul,mul_comm (fourierCost k A)]
    apply mul_le_mul (hf x) ((norm_add_le ..).trans ?_) (norm_nonneg _) (col_bounds x).1
    rw [norm_pow]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (log_bounds k hs hM x).1 2)
      (log_bounds k hs hM x).2
  have hd : Differentiable ℝ f := fun x => (kernel_D k s M x).differentiableAt
  have hd' : Differentiable ℝ f' := fun x => (kernel_DD k s M x).differentiableAt
  have hs'' : Continuous f'' := by
    dsimp [f'',f,kernel,logD',logD,realPower,resolvent,column]
    fun_prop (disch := first | exact nz _ | positivity)
  have i : Integrable f := hc.mono' hd.continuous.aestronglyMeasurable (.of_forall hf)
  have i' : Integrable f' := (hc.const_mul _).mono' hd'.continuous.aestronglyMeasurable (.of_forall h')
  have i'' : Integrable f'' := (hc.const_mul _).mono' hs''.aestronglyMeasurable (.of_forall h'')
  have D : deriv f=f' := funext fun x => (kernel_D k s M x).deriv
  have D' : deriv f'=f'' := funext fun x => (kernel_DD k s M x).deriv
  have T := congrFun (Real.fourier_deriv i hd (D.symm ▸ i')) ξ
  have T' := congrFun (Real.fourier_deriv i' hd' (D'.symm ▸ i'')) ξ
  rw [D] at T
  rw [D', T] at T'
  have hnorm := congrArg norm T'
  have hcI : (∫ x, column x) = Real.pi := integral_univ_inv_one_add_sq
  constructor
  · exact (Fourier_L1 f ξ).trans ((integral_mono i.norm hc hf).trans_eq hcI)
  · calc
      _ = ‖𝓕 f'' ξ‖ := by
        rw [hnorm];simp [norm_smul,norm_mul,Real.norm_eq_abs,abs_of_pos Real.pi_pos,pow_two,mul_assoc]
      _ ≤ ∫ x,‖f'' x‖ := Fourier_L1 f'' ξ
      _ ≤ ∫ x,fourierCost k A*column x := integral_mono i''.norm (hc.const_mul _) h''
      _ = _ := by rw [integral_const_mul,hcI]

end
end ImbalancedChen.Part3.OriginalHeckeFourierKernel20261112
