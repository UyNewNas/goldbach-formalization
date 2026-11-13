import ImbalancedChen.Part3OriginalSwitchedScaledCosine

/-! Uniformly bound the physical cosine profile and its third derivative
in L¹ as the input support moves towards zero. -/
namespace ImbalancedChen.Part3.OriginalSwitchedHyperbolicBudget20261113
noncomputable section
open Set MeasureTheory Real Complex
open OriginalSwitchedScaledCosine20261113
open OriginalSwitchedCutoffModes20261113 (mode)
open OriginalSwitchedSchwartzPrices20261113 (weight)
open ActualPositiveCosineProfile20261112 (profile)

private theorem tail {Y : ℝ} (y1 : 1≤Y) (u : ℝ) :
    1+u^2≤8*(1+(Real.log (2*Y))^2)*(1+Y⁻¹*Real.cosh u) := by
  have yp := zero_lt_one.trans_le y1
  let H := Real.log (2*Y)
  have hp : 0≤H := Real.log_nonneg (by linarith)
  have vp : 0≤Y⁻¹*Real.cosh u := by positivity
  by_cases hu : |u|≤H
  · have p := mul_self_le_mul_self (abs_nonneg _) hu
    rw [←sq, sq_abs,←sq] at p
    change 1+u^2≤8*(1+H^2)*(1+Y⁻¹*Real.cosh u)
    nlinarith only [p, mul_nonneg (add_nonneg zero_le_one (sq_nonneg H)) vp, sq_nonneg H]
  · let b := |u|-H
    have bp : 0≤b := sub_nonneg.mpr (le_of_not_ge hu)
    have expb : Real.exp b≤Y⁻¹*Real.cosh u := by
      rw [show Real.exp b=Real.exp |u|/(2*Y) by rw [show b=|u|-Real.log (2*Y) from rfl,Real.exp_sub,Real.exp_log (by positivity)]]
      rw [div_le_iff₀ (by positivity : 0<2*Y)]
      have ec : Real.exp |u|≤2*Real.cosh u := by
        rw [←Real.cosh_abs,Real.cosh_eq]
        linarith only [Real.exp_pos (-|u|)]
      exact ec.trans_eq (by field_simp [yp.ne'] <;> ring)
    have be := Real.pow_div_factorial_le_exp bp 2
    norm_num at be
    have s : u^2≤2*H^2+2*b^2 := by
      have eq : |u|=H+b := by dsimp only [b];ring
      rw [←sq_abs u,eq]
      nlinarith only [sq_nonneg (H-b)]
    change 1+u^2≤8*(1+H^2)*(1+Y⁻¹*Real.cosh u)
    nlinarith only [s,be,expb,mul_nonneg (sq_nonneg H) vp,sq_nonneg H,vp]

private theorem derivative3_bound (k : ℤ) {V : ℝ} (vp : 0<V) (u : ℝ)
    {A : ℝ} (ha : ∀ j : ℕ,j≤3 → ∀ y : ℝ,0≤y →
      (1+y)*y^j*‖iteratedDeriv j (unitCos k) y‖≤A) :
    (1+V*Real.cosh u)*‖iteratedDeriv 3 (profile (mode k) vp) u‖≤5*A := by
  let v := V*Real.cosh u
  let w := V*Real.sinh u
  have vn : 0≤v := by dsimp only [v];positivity
  have wb : |w|≤v := by
    rw [show |w|=V*|Real.sinh u| by rw [show w=V*Real.sinh u from rfl,abs_mul,abs_of_pos vp]]
    exact mul_le_mul_of_nonneg_left (by rw [Real.abs_sinh,←Real.cosh_abs];exact (Real.sinh_lt_cosh _).le) vp.le
  have e : (profile (mode k) vp:ℝ→ℂ)=fun x => unitCos k (V*Real.cosh x) :=
    funext (fun x => scaled_cosine _ vp _)
  rw [e,third_jet]
  change (1+v)*‖(w:ℂ)*deriv (unitCos k) v+3*(w:ℂ)*(v:ℂ)*iteratedDeriv 2 (unitCos k) v+
    (w:ℂ)^3*iteratedDeriv 3 (unitCos k) v‖≤_
  have tri := norm_add_le ((w:ℂ)*deriv (unitCos k) v) (3*(w:ℂ)*(v:ℂ)*iteratedDeriv 2 (unitCos k) v)
  apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add tri le_rfl)) (by positivity : 0≤1+v)).trans
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vn,Complex.norm_ofNat]
  have h1 := ha 1 (by decide) v vn
  have h2 := ha 2 (by decide) v vn
  have h3 := ha 3 le_rfl v vn
  simp only [pow_one,iteratedDeriv_one] at h1
  have B₁ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right wb (norm_nonneg (deriv (unitCos k) v))) (by positivity : 0≤1+v)
  have B₂ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right wb vn)
    (norm_nonneg (iteratedDeriv 2 (unitCos k) v))) (by positivity : 0≤1+v)
  have B₃ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) wb 3)
    (norm_nonneg (iteratedDeriv 3 (unitCos k) v))) (by positivity : 0≤1+v)
  nlinarith only [h1,h2,h3,B₁,B₂,B₃]

/-- Both endpoints of the Fourier integration by parts. The same C,r
work for every Y≥1, and the full Y cost is one squared logarithm. -/
theorem profile_integrals :
    ∃ (r : ℕ) (C : ℝ),0≤C ∧ ∀ (k : ℤ) (Y : ℝ) (y1 : 1≤Y),
      let vp := inv_pos.mpr (zero_lt_one.trans_le y1)
      let F := profile (mode k) vp
      (∫ u : ℝ,‖F u‖)≤C*(1+Real.log (2*Y)^2)*(weight k)^r ∧
      (∫ u : ℝ,‖iteratedDeriv 3 F u‖)≤C*(1+Real.log (2*Y)^2)*(weight k)^r := by
  obtain ⟨r,C,c,U⟩ := unit_jets
  refine ⟨r,40*Real.pi*C,by positivity,fun k Y y1 => ?_⟩
  let vp := inv_pos.mpr (zero_lt_one.trans_le y1)
  let F := profile (mode k) vp
  let A := C*(weight k)^r
  let H := 1+Real.log (2*Y)^2
  have wp : 0≤weight k := (by linarith [OriginalSwitchedSchwartzPrices20261113.w_one k])
  have ap : 0≤A := mul_nonneg c (pow_nonneg wp _)
  have hp : 0≤H := add_nonneg zero_le_one (sq_nonneg _)
  have price (g : ℝ→ℂ) (ig : Integrable g) (b : ∀ u,(1+Y⁻¹*Real.cosh u)*‖g u‖≤5*A) :
      (∫ u,‖g u‖)≤(40*Real.pi*C)*H*(weight k)^r := by
    have maj (u : ℝ) : ‖g u‖≤(40*H*A)*(1+u^2)⁻¹ := by
      rw [←div_eq_mul_inv,le_div_iff₀ (by positivity : 0<1+u^2)]
      have v := mul_le_mul_of_nonneg_right (tail y1 u) (norm_nonneg (g u))
      have d := mul_le_mul_of_nonneg_left (b u) (mul_nonneg (by norm_num : (0:ℝ)≤8) hp)
      dsimp only [H] at v d ⊢
      nlinarith only [v,d]
    apply (integral_mono ig.norm (integrable_inv_one_add_sq.const_mul (40*H*A)) maj).trans_eq
    rw [integral_const_mul,integral_univ_inv_one_add_sq];dsimp only [A];ring
  constructor
  · apply price F F.integrable
    intro u
    change (1+Y⁻¹*Real.cosh u)*‖ActualPositiveCosineProfile20261112.cosineTest (mode k) vp (Real.cosh u)‖≤_
    rw [scaled_cosine]
    have jet := U k 0 (by decide) (Y⁻¹*Real.cosh u) (by positivity)
    simp only [pow_zero,mul_one,iteratedDeriv_zero] at jet
    exact jet.trans (by linarith only [ap])
  · let D := SchwartzMap.derivCLM ℂ ℂ
    have e : (D (D (D F)):ℝ→ℂ)=iteratedDeriv 3 F := by funext u;simp [D,iteratedDeriv_succ]
    apply price _ (e ▸ (D (D (D F))).integrable)
    exact fun u => derivative3_bound k vp u (U k)

end
end ImbalancedChen.Part3.OriginalSwitchedHyperbolicBudget20261113
