import ImbalancedChen.Part3ActualPositiveSmallHeightWaves
import ImbalancedChen.Part3ComplexOrderKEntire
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Removing the common central product before integrating the two heights
removes the zero-order pole without a spectral gap or a parameter integral. -/
namespace ImbalancedChen.Part3.ActualPositiveCenteredKLimit20261112

noncomputable section
open Set Filter Complex
open scoped Topology
open ActualPositiveSmallHeightWaves20261112 ComplexOrderKBridgeSourceOnly ComplexOrderKEntire20261025a

def centered (ν : ℂ) (L w : ℝ) : ℂ :=
  4*(complexOrderK ν (2*Real.exp (L+w))*complexOrderK ν (2*Real.exp (L-w))-
    complexOrderK ν (2*Real.exp L)^2)

def sinhc : ℂ → ℂ := dslope Complex.sinh 0

def limitKernel (ν : ℂ) (w : ℝ) : ℂ :=
  -4*Gamma (1+ν)*Gamma (1-ν)*(w:ℂ)^2*sinhc (ν*(w:ℂ))^2

theorem limit_zero (w : ℝ) : limitKernel 0 w= -4*(w:ℂ)^2 := by
  simp [limitKernel,sinhc,dslope_same,(Complex.hasDerivAt_sinh 0).deriv]

private theorem z_sinhc (z : ℂ) : z*sinhc z=sinh z := by
  simpa only [sub_zero,Complex.sinh_zero,smul_eq_mul,sinhc] using sub_smul_dslope Complex.sinh 0 z

private theorem sinhc_diff : Differentiable ℂ sinhc := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s:=Set.univ) (c:=0) univ_mem).mpr
    Complex.differentiable_sinh.differentiableOn

theorem limit_nonzero {ν : ℂ} (hz : ν≠0) (w : ℝ) :
    limitKernel ν w=4*Gamma ν*Gamma (-ν)*sinh (ν*(w:ℂ))^2 := by
  rw [limitKernel,add_comm 1 ν,show 1-ν=-ν+1 by ring,Gamma_add_one ν hz,
    Gamma_add_one (-ν) (neg_ne_zero.mpr hz),← z_sinhc (ν*(w:ℂ))]
  ring

theorem limit_cosh {ν : ℂ} (hz : ν≠0) (w : ℝ) :
    limitKernel ν w=2*Gamma ν*Gamma (-ν)*(cosh (2*ν*(w:ℂ))-1) := by
  rw [limit_nonzero hz,show 2*ν*(w:ℂ)=2*(ν*(w:ℂ)) by ring,cosh_two_mul]
  linear_combination -2*Gamma ν*Gamma (-ν)*cosh_sq_sub_sinh_sq (ν*(w:ℂ))

private theorem leading_center {ν : ℂ} (hz : ν≠0) (L w : ℝ) :
    4*(leading ν (L+w)*leading ν (L-w)-leading ν L^2)=limitKernel ν w := by
  rw [limit_nonzero hz,Complex.sinh]
  unfold leading part
  simp only [Complex.ofReal_add,Complex.ofReal_sub,mul_add,mul_sub,neg_mul,neg_neg,
    Complex.exp_add,Complex.exp_sub,Complex.exp_neg]
  field_simp [Complex.exp_ne_zero] <;> ring

private theorem centered_entire (L w : ℝ) :
    Differentiable ℂ (fun ν => centered ν L w) := by
  unfold centered
  exact ((complexOrderK_differentiable_all (by positivity)).mul
    (complexOrderK_differentiable_all (by positivity)) |>.sub
    ((complexOrderK_differentiable_all (by positivity)).pow 2)).const_mul _

private theorem limit_diff {ν : ℂ} (hn : ‖ν‖<1) (w : ℝ) :
    DifferentiableAt ℂ (fun u => limitKernel u w) ν := by
  have absV := (abs_re_le_norm ν).trans_lt hn
  have gg (x : ℂ) (hx : 0<x.re) : DifferentiableAt ℂ Gamma x := by
    apply differentiableAt_Gamma
    intro n e
    rw [e,neg_re,Complex.natCast_re] at hx
    linarith [Nat.cast_nonneg (R:=ℝ) n]
  have A := (gg (1+ν) (by simp only [one_re,add_re]; linarith [(abs_lt.mp absV).1])).comp ν
    ((differentiableAt_const (c:=(1:ℂ))).add differentiableAt_id)
  have B := (gg (1-ν) (by simp only [one_re,sub_re]; linarith [(abs_lt.mp absV).2])).comp ν
    ((differentiableAt_const (c:=(1:ℂ))).sub differentiableAt_id)
  have C := (sinhc_diff.differentiableAt (x:=ν*(w:ℂ))).comp ν
    (differentiableAt_id.mul_const (w:ℂ))
  unfold limitKernel
  exact (((A.const_mul _).mul B).mul_const _).mul (C.pow 2)

private theorem product_error {a b c d : ℂ} {A B : ℝ} (b0 : 0≤B) (ba : B≤A)
    (hc : ‖c‖≤A) (hd : ‖d‖≤A) (h1 : ‖a-c‖≤B) (h2 : ‖b-d‖≤B) :
    ‖a*b-c*d‖≤3*A*B := by
  have bd : ‖b‖≤B+A := by linarith only [norm_le_insert' b d,h2,hd]
  rw [show a*b-c*d=(a-c)*b+c*(b-d) by ring]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  calc
    _ ≤ B*(B+A)+A*B := add_le_add (mul_le_mul h1 bd (norm_nonneg _) b0)
      (mul_le_mul hc h2 (norm_nonneg _) (b0.trans ba))
    _ ≤ _ := by nlinarith [mul_nonneg b0 (sub_nonneg.mpr ba)]

private theorem centered_error_of_waves {ν : ℂ} (hz : ν≠0) {C U L w : ℝ}
    (c0 : 0≤C) (uw : |w|≤U) (lh : L≤-U)
    (W : ∀ x : ℝ,x≤0 → ‖leading ν x‖≤C*Real.exp (-radius*x) ∧
      ‖complexOrderK ν (2*Real.exp x)-leading ν x‖≤C*Real.exp ((2-radius)*x)) :
    ‖centered ν L w-limitKernel ν w‖≤24*C^2*Real.exp (2*U)*Real.exp (L/2) := by
  let A := C*Real.exp (-radius*(L-U))
  let B := C*Real.exp ((2-radius)*(L+U))
  have u0 : 0≤U := (abs_nonneg w).trans uw
  have u := abs_le.mp uw
  have ba : B≤A := by dsimp [A,B]; gcongr; dsimp [radius]; linarith
  have b0 : 0≤B := by dsimp [B]; positivity
  have db (x : ℝ) (hlo : L-U≤x) (hhi : x≤L+U) :
      ‖leading ν x‖≤A ∧ ‖complexOrderK ν (2*Real.exp x)-leading ν x‖≤B := by
    obtain ⟨a,b⟩ := W x (by linarith)
    constructor
    · apply a.trans; dsimp [A]; gcongr; dsimp [radius]; linarith
    · apply b.trans; dsimp [B]; gcongr; dsimp [radius]; linarith
  have pl := db (L+w) (by linarith) (by linarith)
  have mi := db (L-w) (by linarith) (by linarith)
  have ce := db L (by linarith) (by linarith)
  have P := product_error b0 ba pl.1 mi.1 pl.2 mi.2
  have Q := product_error b0 ba ce.1 ce.1 ce.2 ce.2
  rw [← leading_center hz L w,centered,show ∀ a b c d : ℂ,4*(a-b)-4*(c-d)=4*((a-c)-(b-d)) by intros; ring,norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num : (0:ℝ)≤4)).trans
  rw [pow_two,pow_two]
  calc
    _ ≤ 4*(3*A*B+3*A*B) := by linarith only [P,Q]
    _ = _ := by
      dsimp [A,B]
      have E : Real.exp (-radius*(L-U))*Real.exp ((2-radius)*(L+U))=Real.exp (2*U)*Real.exp (L/2) := by
        rw [← Real.exp_add,← Real.exp_add]; congr 1; dsimp [radius]; ring
      linear_combination 24*C^2*E

/-- Uniformity through t=0 and all 0≤α<1/2 is proved for bounded w.
The constant here depends on the fixed w-window. -/
theorem disk_error (U : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ ν : ℂ,‖ν‖≤radius → ∀ L : ℝ,L≤-U → ∀ w : ℝ,|w|≤U →
      ‖centered ν L w-limitKernel ν w‖≤C*Real.exp (L/2) := by
  obtain ⟨c,c0,W⟩ := wave_bounds
  refine ⟨24*c^2*Real.exp (2*U),by positivity,fun ν hv L hL w hw => ?_⟩
  have rad : 0<radius := by norm_num [radius]
  let f (u : ℂ) := centered u L w-limitKernel u w
  have D : DifferentiableOn ℂ f (Metric.closedBall 0 radius) := by
    intro u hu
    have ub : ‖u‖≤radius := by simpa [Metric.mem_closedBall,dist_zero_right] using hu
    exact (((centered_entire L w).differentiableAt).sub
      (limit_diff (ub.trans_lt (by norm_num [radius])) w)).differentiableWithinAt
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (f:=f) (U:=Metric.ball 0 radius)
    Metric.isBounded_ball (D.diffContOnCl_ball subset_rfl) _
    (by simpa [closure_ball _ rad.ne',Metric.mem_closedBall,dist_zero_right] using hv)
  intro u hu
  have ub : ‖u‖=radius := by simpa [frontier_ball _ rad.ne',Metric.mem_sphere,dist_zero_right] using hu
  exact centered_error_of_waves (fun z => by norm_num [z,radius] at ub) c0 hw hL (W u ub)

/-- No bound on imaginary t is needed for pointwise convergence. -/
theorem fixed_error {ν : ℂ} (nz : ν≠0) (hv : |ν.re|≤radius) (U : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ L : ℝ,L≤-U → ∀ w : ℝ,|w|≤U →
      ‖centered ν L w-limitKernel ν w‖≤C*Real.exp (L/2) := by
  obtain ⟨c,c0,W⟩ := fixed_waves nz hv
  exact ⟨24*c^2*Real.exp (2*U),by positivity,fun L hL w hw => centered_error_of_waves nz c0 hw hL W⟩

end
end ImbalancedChen.Part3.ActualPositiveCenteredKLimit20261112
