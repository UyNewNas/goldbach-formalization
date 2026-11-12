import ImbalancedChen.Part3ActualPositiveSmallHeightKBound
import ImbalancedChen.Part3ActualComplexKIConnection
import ImbalancedChen.Part3ActualGreenResolventJump
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! First terms of the physical K integral at logarithmic height x. -/
namespace ImbalancedChen.Part3.ActualPositiveSmallHeightWaves20261112

noncomputable section
open Set Filter Complex
open scoped Topology
open GeneralComplexISeriesSourceOnly ComplexOrderKBridgeSourceOnly
open ActualComplexKIConnection ActualImaginaryKIConnectionSourceOnly ActualGreenResolventJumpSourceOnly

def radius : ℝ := 3/4

def core (ν : ℂ) (x : ℝ) : ℂ :=
  Gamma (ν+1)*generalICore ν ((Real.exp x:ℂ)^2)

def part (ν : ℂ) (x : ℝ) : ℂ := Gamma (-ν)/2*exp (ν*(x:ℂ))

def leading (ν : ℂ) (x : ℝ) : ℂ := part ν x+part (-ν) x

private theorem coeff (ν : ℂ) (hv : -radius≤ν.re) (k : ℕ) :
    ‖Gamma (ν+1)*generalICoeff ν k‖≤(4:ℝ)^k/k.factorial := by
  have h : -1<ν.re := by dsimp [radius] at hv; linarith
  have g := Gamma_ne_zero_of_re_pos (s:=ν+1) (by simp only [add_re,one_re]; linarith)
  have a : (1:ℝ)/4≤ν.re+1 := by dsimp [radius] at hv; linarith
  rw [norm_mul]
  calc
    _ ≤ ‖Gamma (ν+1)‖*(‖(Gamma (ν+1))⁻¹‖/((ν.re+1)^k*k.factorial)) := by
      gcongr; exact generalICoeff_norm_le h k
    _ = 1/((ν.re+1)^k*k.factorial) := by rw [norm_inv]; field_simp [(norm_pos_iff.mpr g).ne']
    _ ≤ 1/(((1:ℝ)/4)^k*k.factorial) := by gcongr
    _ = _ := by rw [div_pow,one_pow]; field_simp

/-- The normalized I core is 1 plus a uniform quadratic error on the
whole closed order strip used by the little circle. -/
theorem core_error {ν : ℂ} (hv : -radius≤ν.re) {x : ℝ} (hx : x≤0) :
    ‖core ν x-1‖≤(∑' k : ℕ,(4:ℝ)^(k+1)/(k+1).factorial)*Real.exp (2*x) := by
  let z : ℂ := (Real.exp x:ℂ)^2
  let a (k : ℕ) := Gamma (ν+1)*(generalICoeff ν k*z^k)
  have h : -1<ν.re := by dsimp [radius] at hv; linarith
  have G := Gamma_ne_zero_of_re_pos (s:=ν+1) (by simp only [add_re,one_re]; linarith)
  have A := (generalICore_hasSum h z).mul_left (Gamma (ν+1))
  have t : HasSum a (core ν x) := A
  have z0 : ‖z‖=Real.exp (2*x) := by
    simp only [z,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    rw [two_mul,Real.exp_add,pow_two]
  have z1 : ‖z‖≤1 := by rw [z0,Real.exp_le_one_iff]; linarith
  have a0 : a 0=1 := by simp [a,generalICoeff,G]
  have M := (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial (4:ℝ))
  have D (k : ℕ) : ‖a (k+1)‖≤((4:ℝ)^(k+1)/(k+1).factorial)*Real.exp (2*x) := by
    rw [← z0]
    dsimp only [a]
    rw [← mul_assoc,norm_mul,norm_pow,pow_succ]
    apply mul_le_mul (coeff ν hv _) _ (by positivity) (by positivity)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (norm_nonneg z) z1) (norm_nonneg z)
  have S := Summable.of_nonneg_of_le (fun k => norm_nonneg _) D (M.mul_right _)
  rw [← t.tsum_eq,t.summable.tsum_eq_zero_add,a0,add_sub_cancel_left,← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm S).trans (S.tsum_le_tsum D (M.mul_right _))

private theorem connection {ν : ℂ} (lo : -1<ν.re) (hi : ν.re<1) (nz : ν≠0)
    {q : ℝ} (hq : 0<q) :
    complexOrderK ν q=(Real.pi:ℂ)/(2*sin ((Real.pi:ℂ)*ν))*
      (generalI (-ν) q-generalI ν q) := by
  rcases lt_trichotomy ν.re 0 with h|h|h
  · have A := complexOrderK_eq_generalI_sub (ν := -ν) (by simpa using h)
        (by simp only [neg_re]; linarith) hq
    rw [complexOrderK_neg_order,neg_neg,mul_neg,sin_neg] at A
    rw [A]; ring
  · apply complexOrderK_eq_generalI_sub_of_re_zero h _ hq
    intro hz
    exact nz (Complex.ext (by simpa using h) (by simpa using hz))
  · exact complexOrderK_eq_generalI_sub h hi hq

theorem waves {ν : ℂ} (lo : -1<ν.re) (hi : ν.re<1) (nz : ν≠0) (x : ℝ) :
    complexOrderK ν (2*Real.exp x)=part ν x*core ν x+part (-ν) x*core (-ν) x := by
  have hpow (v : ℂ) : (((Real.exp x:ℝ):ℂ)^v)=exp (v*(x:ℂ)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← ofReal_log (Real.exp_pos _).le,Real.log_exp,mul_comm]
  have gm := Gamma_mul_Gamma_one_sub ν
  have gp := Gamma_mul_Gamma_one_sub (-ν)
  rw [mul_neg,sin_neg,div_neg] at gp
  rw [connection lo hi nz (by positivity),generalI,generalI,
    show 2*Real.exp x/2=Real.exp x by ring,hpow,hpow]
  unfold part core
  rw [neg_neg,show -ν+1=1-ν by ring,show ν+1=1-(-ν) by ring]
  rw [show (Real.pi:ℂ)/(2*sin ((Real.pi:ℂ)*ν))=((Real.pi:ℂ)/sin ((Real.pi:ℂ)*ν))/2 by rw [div_div,mul_comm (sin _ )]]
  linear_combination
    -(exp (ν*(x:ℂ))*generalICore ν ((Real.exp x:ℂ)^2)/2)*gp -
    (exp (-ν*(x:ℂ))*generalICore (-ν) ((Real.exp x:ℂ)^2)/2)*gm

private theorem gamma_cont {ν : ℂ} (h : ‖ν‖=radius) : ContinuousAt Gamma ν := by
  apply (differentiableAt_Gamma ν _).continuousAt
  intro n E
  rw [E,norm_neg,Complex.norm_natCast] at h
  cases n with
  | zero => norm_num [radius] at h
  | succ n => push_cast at h; dsimp [radius] at h; linarith [Nat.cast_nonneg (R:=ℝ) n]

private def remainderMass : ℝ := ∑' k : ℕ,(4:ℝ)^(k+1)/(k+1).factorial

private theorem bounds_of_gamma {ν : ℂ} (nν : ν≠0)
    (hv : -radius≤ν.re ∧ ν.re≤radius) {g : ℝ} (g0 : 0≤g)
    (hGm : ‖Gamma (-ν)‖≤g) (hGp : ‖Gamma ν‖≤g) (x : ℝ) (hx : x≤0) :
    ‖leading ν x‖≤g*(1+remainderMass)*Real.exp (-radius*x) ∧
    ‖complexOrderK ν (2*Real.exp x)-leading ν x‖≤g*(1+remainderMass)*Real.exp ((2-radius)*x) := by
  let B := remainderMass
  have b : 0≤B := tsum_nonneg fun _ => by positivity
  let C := g*(1+B)
  have hb (v : ℂ) (rv : -radius≤v.re) (hGv : ‖Gamma (-v)‖≤g) : ‖part v x‖≤g/2*Real.exp (-radius*x) := by
    rw [part,norm_mul,norm_div,Complex.norm_exp,Complex.mul_re]
    simp only [ofReal_re,ofReal_im,mul_zero,sub_zero,Complex.norm_ofNat]
    exact mul_le_mul (by linarith) (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right rv hx)) (Real.exp_pos _).le (by positivity)
  have l := (norm_add_le (part ν x) (part (-ν) x)).trans
    (add_le_add (hb ν hv.1 hGm) (hb _ (by simpa using hv.2) (by simpa using hGp)))
  have cn : g≤C := by dsimp [C]; nlinarith
  have ascore (v : ℂ) (rv : -radius≤v.re) (hGv : ‖Gamma (-v)‖≤g) :
      ‖part v x*(core v x-1)‖≤(g/2*Real.exp (-radius*x))*(B*Real.exp (2*x)) := by
    rw [norm_mul]; exact mul_le_mul (hb v rv hGv) (core_error rv hx) (norm_nonneg _) (by positivity)
  constructor
  · change ‖part ν x+part (-ν) x‖≤_
    calc
      _ ≤ g*Real.exp (-radius*x) := by linarith only [l]
      _ ≤ _ := by gcongr
  · rw [waves (by dsimp [radius] at hv; linarith [hv.1]) (by dsimp [radius] at hv; linarith [hv.2]) nν]
    rw [leading,show part ν x*core ν x+part (-ν) x*core (-ν) x-(part ν x+part (-ν) x)=
      part ν x*(core ν x-1)+part (-ν) x*(core (-ν) x-1) by ring]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ _ := add_le_add (ascore ν hv.1 hGm) (ascore _ (by simpa using hv.2) (by simpa using hGp))
      _ = g*B*Real.exp ((2-radius)*x) := by
        rw [show (2-radius)*x=(-radius*x)+(2*x) by ring,Real.exp_add]; ring
      _ ≤ _ := by gcongr; dsimp [C]; nlinarith

/-- Both signs of the Gamma waves have one bound on the circle. -/
theorem wave_bounds :
    ∃ C : ℝ,0≤C ∧ ∀ ν : ℂ,‖ν‖=radius → ∀ x : ℝ,x≤0 →
      ‖leading ν x‖≤C*Real.exp (-radius*x) ∧
      ‖complexOrderK ν (2*Real.exp x)-leading ν x‖≤C*Real.exp ((2-radius)*x) := by
  obtain ⟨G,hG⟩ := (isCompact_sphere (0:ℂ) radius).exists_bound_of_continuousOn
    (f:=Gamma) (fun z hz => (gamma_cont (by simpa [Metric.mem_sphere,dist_zero_right] using hz)).continuousWithinAt)
  let g := max G 0
  have b : 0≤remainderMass := tsum_nonneg fun _ => by positivity
  have g0 : 0≤g := le_max_right _ _
  refine ⟨g*(1+remainderMass),by positivity,fun ν hν => ?_⟩
  have nν : ν≠0 := by intro E; norm_num [E,radius] at hν
  have hv : -radius≤ν.re ∧ ν.re≤radius := by rw [← hν]; exact abs_le.mp (abs_re_le_norm ν)
  exact bounds_of_gamma nν hv g0
    ((hG _ (by simpa [Metric.mem_sphere,dist_zero_right] using hν)).trans (le_max_left _ _))
    ((hG _ (by simpa [Metric.mem_sphere,dist_zero_right] using hν)).trans (le_max_left _ _))

/-- Fixed nonzero imaginary orders outside the threshold disk obey the
same height error, with their own Gamma constant. -/
theorem fixed_waves {ν : ℂ} (hz : ν≠0) (hr : |ν.re|≤radius) :
    ∃ C : ℝ,0≤C ∧ ∀ x : ℝ,x≤0 →
      ‖leading ν x‖≤C*Real.exp (-radius*x) ∧
      ‖complexOrderK ν (2*Real.exp x)-leading ν x‖≤C*Real.exp ((2-radius)*x) := by
  let g := max ‖Gamma (-ν)‖ ‖Gamma ν‖
  have g0 : 0≤g := (norm_nonneg _).trans (le_max_right _ _)
  have b : 0≤remainderMass := tsum_nonneg fun _ => by positivity
  exact ⟨g*(1+remainderMass),by positivity,bounds_of_gamma hz (abs_le.mp hr) g0
    (le_max_left _ _) (le_max_right _ _)⟩

end
end ImbalancedChen.Part3.ActualPositiveSmallHeightWaves20261112
