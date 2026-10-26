import ImbalancedChen.Part3RoughQuadraticFiniteRectangle
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalNonquadraticConductorLogZeroFree

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual nonquadratic finite rectangle and polynomial reciprocal bound.
The reciprocal estimate constructs a holomorphic logarithm internally and
uses its real-part oscillation plus Borel--Caratheodory. Thus nonvanishing
is converted to a quantitative reciprocal estimate; no unknown left-strip
norm is postulated. Principal characters are excluded explicitly.
-/

namespace ImbalancedChen.Part3.RoughFiniteRectangleReciprocal20261026b
noncomputable section
open Complex Metric Set
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaZeroContribution
open DirichletLGlobalConductorLogValueBound
open RoughQuadraticLowRectangle20261026b RoughQuadraticFiniteRectangle20261026b

def nonquadraticWidth (q : ℕ) (T : ℝ) : ℝ :=
  min (1 / 4) (1 / (274877906944 * rectangleLog q T ^ 9))

theorem nonquadraticWidth_pos (q : ℕ) [NeZero q] (T : ℝ) :
    0 < nonquadraticWidth q T := by
  unfold nonquadraticWidth
  exact lt_min (by norm_num) (one_div_pos.mpr (mul_pos (by norm_num)
    (pow_pos (lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q T)) 9)))

/-- Monotonicity of the actual conductor-height cutoff gives one genuine
width on the entire enlarged finite rectangle. -/
theorem nonquadratic_finite_rectangle {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 ≠ 1) (T : ℝ)
    (s : ℂ) (hslo : 1 - nonquadraticWidth q T ≤ s.re)
    (_hshi : s.re ≤ 2) (hst : |s.im| ≤ T + 1) : χ.LFunction s ≠ 0 := by
  have hχ : χ ≠ 1 := by
    intro h
    exact hχsq (by rw [h,one_pow])
  by_cases hsone : 1 ≤ s.re
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hsone
  have hlocal := heightLog_le_rectangleLog χ hχ hst
  have hlocalpos : 0 < 1 + Real.log (dirichletLConductorHeightCutoff q s.im) := by
    linarith [log_conductorHeightCutoff_pos χ hχ s.im]
  have hden : 274877906944 * (1 + Real.log (dirichletLConductorHeightCutoff q s.im)) ^ 9 ≤
      274877906944 * rectangleLog q T ^ 9 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlocalpos.le hlocal 9) (by norm_num)
  have hw : nonquadraticWidth q T ≤
      1 / (274877906944 * (1 + Real.log (dirichletLConductorHeightCutoff q s.im)) ^ 9) :=
    (min_le_right _ _).trans (one_div_le_one_div_of_le (by positivity) hden)
  have hrepr : (s.re : ℂ) + I * s.im = s := by
    simpa only [mul_comm I] using s.re_add_im
  rw [← hrepr]
  exact norm_LFunction_ne_zero_of_nonquadratic_conductorLog χ hχsq
    ⟨le_trans (sub_le_sub_left hw 1) hslo,lt_of_not_ge hsone⟩

/-- Written as exp of elementary real logarithms to keep the exact cost
visible: this equals (4/delta)*(32*q*(1+|t|)/delta)^4. -/
def reciprocalBudget (q : ℕ) (δ t : ℝ) : ℝ :=
  Real.exp (4 * Real.log (32 * q * (1 + |t|) / δ) - Real.log (δ / 4))

/-- Quantitative reciprocal control from a finite zero-free rectangle.
The anchor and growth inputs are genuine proved L-function estimates.
Only this private analytic core takes hzero; public consumers below supply
it from the exact primary nonquadratic/quadratic theorems. -/
private theorem reciprocal_of_rectangle {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {δ T : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hzero : ∀ z : ℂ, 1 - δ ≤ z.re → z.re ≤ 2 → |z.im| ≤ T + 1 →
      χ.LFunction z ≠ 0)
    (β t : ℝ) (ht : |t| ≤ T) (hβlo : 1 - δ / 2 ≤ β) (hβhi : β ≤ 1 + δ) :
    ‖(χ.LFunction ((β : ℂ) + I * t))⁻¹‖ ≤ reciprocalBudget q δ t := by
  let a : ℂ := (1 + δ / 2 : ℝ) + I * t
  let z : ℂ := (β : ℂ) + I * t
  let B : ℝ := 8 * q * (1 + |t|)
  let b : ℝ := δ / 4
  have hb : 0 < b := by dsimp [b]; positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hbB : b < B := by
    dsimp [b,B]
    nlinarith [abs_nonneg t]
  have hB : 0 < B := hb.trans hbB
  have hR : 0 < 3 * δ / 2 := by positivity
  have ha : a ∈ ball a (3 * δ / 2) := mem_ball_self hR
  have hzdist : dist z a ≤ δ := by
    dsimp [z,a]
    rw [dist_add_right,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hz : z ∈ ball a (3 * δ / 2) := mem_ball.mpr (hzdist.trans_lt (by linarith))
  have hzeroDisk : ∀ w ∈ ball a (3 * δ / 2), χ.LFunction w ≠ 0 := by
    intro w hw
    obtain ⟨hlo,hhi,him⟩ := Eq21FiniteLogDerivative.anchor_disk_subset_rectangle hδ hδ1 ht hw
    exact hzero w hlo hhi him
  obtain ⟨h,hh,hexp⟩ := exists_holomorphicLog_on_ball χ.LFunction a hR
    (χ.differentiable_LFunction hχ).differentiableOn hzeroDisk
  have hre : ∀ w ∈ ball a (3 * δ / 2), (h w).re = Real.log ‖χ.LFunction w‖ := by
    intro w hw
    rw [← hexp hw,Complex.norm_exp,Real.log_exp]
  have hanchor : b ≤ ‖χ.LFunction a‖ :=
    Eq21LocalLog.delta_quarter_le_norm_LFunction_anchor χ hδ hδ1 t
  have hbound : ∀ w ∈ ball a (3 * δ / 2), ‖χ.LFunction w‖ ≤ B :=
    fun w hw => Eq21LocalLog.norm_LFunction_le_on_anchor_disk χ hχ hδ hδ1 t hw
  let A := Real.log (B / b)
  have hA : 0 < A := Real.log_pos ((one_lt_div hb).2 hbB)
  have hosc : ∀ w ∈ ball a (3 * δ / 2), (h w).re - (h a).re ≤ A := by
    intro w hw
    rw [hre w hw,hre a ha]
    dsimp only [A]
    rw [Real.log_div hB.ne' hb.ne']
    exact sub_le_sub (Real.log_le_log (norm_pos_iff.mpr (hzeroDisk w hw)) (hbound w hw))
      (Real.log_le_log hb hanchor)
  let H : ℂ → ℂ := fun w => h (a + w) - h a
  have hHd : DifferentiableOn ℂ H (ball 0 (3 * δ / 2)) := by
    intro w hw
    have haw : a + w ∈ ball a (3 * δ / 2) := by
      simpa [mem_ball,dist_comm] using hw
    exact (((hh (a+w) haw).differentiableAt (isOpen_ball.mem_nhds haw)).comp w
      (by fun_prop) |>.sub (differentiableAt_const _)).differentiableWithinAt
  have hHre : MapsTo H (ball 0 (3 * δ / 2)) {w : ℂ | w.re ≤ A} := by
    intro w hw
    exact hosc (a+w) (by simpa [mem_ball,dist_comm] using hw)
  have hH0 : H 0 = 0 := by simp [H]
  have hn : ‖z-a‖ ≤ δ := by simpa only [dist_eq_norm] using hzdist
  have hmem : z-a ∈ ball 0 (3 * δ / 2) := by
    simp only [mem_ball,dist_zero_right]
    linarith
  have hbc := borelCaratheodory_zero hA hHd hHre hR hmem hH0
  have hden : 0 < 3 * δ / 2 - ‖z-a‖ := by linarith
  have hrat : 2 * ‖z-a‖ / (3 * δ / 2 - ‖z-a‖) * A ≤ 4 * A := by
    apply mul_le_mul_of_nonneg_right _ hA.le
    apply (div_le_iff₀ hden).2
    linarith
  have hnorm : ‖h z-h a‖ ≤ 4*A := by
    apply (show ‖h z-h a‖ ≤ _ from by simpa [H] using hbc).trans
    convert hrat using 1 <;> ring
  have hreDiff : (h a).re - (h z).re ≤ 4*A := by
    have hhRe := (abs_le.mp (Complex.abs_re_le_norm (h z-h a))).1
    simp only [sub_re] at hhRe
    linarith
  have hreAnchor : Real.log b ≤ (h a).re := by
    rw [hre a ha]
    exact Real.log_le_log hb hanchor
  have hinv : ‖(χ.LFunction z)⁻¹‖ = Real.exp (-(h z).re) := by
    rw [← hexp hz,norm_inv,Complex.norm_exp,Real.exp_neg]
  rw [hinv]
  have hcost : 4*A-Real.log b =
      4*Real.log (32*q*(1+|t|)/δ)-Real.log (δ/4) := by
    dsimp only [A,B,b]
    congr 2
    field_simp
    ring
  change Real.exp (-(h z).re) ≤ reciprocalBudget q δ t
  unfold reciprocalBudget
  rw [← hcost]
  exact Real.exp_le_exp.mpr (by linarith)

theorem nonquadratic_reciprocal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 ≠ 1)
    (T β t : ℝ) (ht : |t| ≤ T)
    (hβlo : 1 - nonquadraticWidth q T / 2 ≤ β)
    (hβhi : β ≤ 1 + nonquadraticWidth q T) :
    ‖(χ.LFunction ((β : ℂ) + I*t))⁻¹‖ ≤ reciprocalBudget q (nonquadraticWidth q T) t := by
  have hχ : χ ≠ 1 := by intro h; exact hχsq (by rw [h,one_pow])
  exact reciprocal_of_rectangle χ hχ (nonquadraticWidth_pos q T) (min_le_left _ _)
    (nonquadratic_finite_rectangle χ hχsq T) β t ht hβlo hβhi

theorem exists_quadratic_reciprocal (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ ^ 2 = 1 → χ ≠ 1 → c*(q : ℝ)^(-η) ≤ (χ.LFunction 1).re →
        ∀ T : ℝ, 0 ≤ T → ∀ β t : ℝ,
          let δ := quadraticRectangleWidth A η q T (c*(q : ℝ)^(-η))
          |t| ≤ T → 1-δ/2 ≤ β → β ≤ 1+δ →
          ‖(χ.LFunction ((β : ℂ)+I*t))⁻¹‖ ≤ reciprocalBudget q δ t := by
  obtain ⟨A,hA,hzero⟩ := exists_quadratic_finite_rectangle c η hc hη
  refine ⟨A,hA,?_⟩
  intro q _ χ hquad hχ hL T hT β t
  dsimp only
  have hr : 0 < c*(q : ℝ)^(-η) :=
    mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos q) _)
  exact reciprocal_of_rectangle χ hχ (quadraticRectangleWidth_pos hA q hT hr)
    (quadraticRectangleWidth_le_quarter A η q T _)
    (hzero q χ hquad hχ hL T hT) β t

end
end ImbalancedChen.Part3.RoughFiniteRectangleReciprocal20261026b
