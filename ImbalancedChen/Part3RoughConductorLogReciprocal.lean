import ImbalancedChen.Part3RoughFiniteRectangleReciprocal

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A genuine improvement of the actual finite-rectangle reciprocal bound.
The original widths already obey delta<=1/D, D=1+log(q*(floor(T+1)+1)).
The exact primary conductor-log value estimate then gives |L|<=32D on
all of the anchor disk. Constructing its logarithm and using
Borel--Caratheodory yields (4/delta)*(128D/delta)^4, with logarithmic
rather than polynomial growth in the height. No unknown left-strip norm,
zero-free premise or SW premise is left in the public consumers.
-/

namespace ImbalancedChen.Part3.RoughConductorLogReciprocal20261026b
noncomputable section
open Complex Metric Set
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.TatuzawaZeroContribution
open DirichletLGlobalConductorLogValueBound
open RoughQuadraticLowRectangle20261026b RoughQuadraticFiniteRectangle20261026b
open RoughFiniteRectangleReciprocal20261026b

def logarithmicReciprocalBudget (q : ℕ) (T δ : ℝ) : ℝ :=
  Real.exp (4*Real.log (128*rectangleLog q T/δ)-Real.log (δ/4))
private theorem reciprocal_from_conductorlog {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {δ T : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hsmall : δ ≤ 1 / rectangleLog q T)
    (hzero : ∀ z : ℂ, 1 - δ ≤ z.re → z.re ≤ 2 → |z.im| ≤ T + 1 →
      χ.LFunction z ≠ 0)
    (β t : ℝ) (ht : |t| ≤ T) (hβlo : 1 - δ / 2 ≤ β) (hβhi : β ≤ 1 + δ) :
    ‖(χ.LFunction ((β : ℂ) + I * t))⁻¹‖ ≤ logarithmicReciprocalBudget q T δ := by
  let a : ℂ := (1 + δ / 2 : ℝ) + I * t
  let z : ℂ := (β : ℂ) + I * t
  let B : ℝ := 32 * rectangleLog q T
  let b : ℝ := δ / 4
  have hb : 0 < b := by dsimp [b]; positivity
  have hD : 1 ≤ rectangleLog q T := one_le_rectangleLog q T
  have hbB : b < B := by
    dsimp [b,B]
    linarith
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
  have hbound : ∀ w ∈ ball a (3 * δ / 2), ‖χ.LFunction w‖ ≤ B := by
    intro w hw
    obtain ⟨hwlo,hwhi,hwim⟩ :=
      Eq21FiniteLogDerivative.anchor_disk_subset_rectangle hδ hδ1 ht hw
    have hlog := heightLog_le_rectangleLog χ hχ hwim
    have hlogpos := log_conductorHeightCutoff_pos χ hχ w.im
    have hinv : 1 / rectangleLog q T ≤
        1 / Real.log (dirichletLConductorHeightCutoff q w.im) :=
      one_div_le_one_div_of_le hlogpos (by linarith)
    have hhalf : 1 / 2 ≤ w.re := by linarith
    have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q w.im) ≤ w.re := by
      linarith [hsmall.trans hinv]
    have hv := norm_LFunction_le_thirtytwo_mul_one_add_log_conductorHeightCutoff
      χ hχ hhalf hwhi hnear
    have hrepr : (w.re : ℂ) + I*w.im = w := by
      simpa only [mul_comm I] using w.re_add_im
    rw [hrepr] at hv
    exact hv.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))
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
      4*Real.log (128*rectangleLog q T/δ)-Real.log (δ/4) := by
    dsimp only [A,B,b]
    congr 2
    field_simp
    ring
  change Real.exp (-(h z).re) ≤ logarithmicReciprocalBudget q T δ
  unfold logarithmicReciprocalBudget
  rw [← hcost]
  exact Real.exp_le_exp.mpr (by linarith)

theorem nonquadraticWidth_le_inverse_rectangleLog (q : ℕ) [NeZero q] (T : ℝ) :
    nonquadraticWidth q T ≤ 1 / rectangleLog q T := by
  have hD := one_le_rectangleLog q T
  have hDpos : 0 < rectangleLog q T := lt_of_lt_of_le zero_lt_one hD
  have hpow : rectangleLog q T ≤ rectangleLog q T ^ 9 := by
    calc
      _ = rectangleLog q T ^ 1 := by ring
      _ ≤ rectangleLog q T ^ 9 := pow_le_pow_right₀ hD (by norm_num)
  have hden : rectangleLog q T ≤ 274877906944 * rectangleLog q T ^ 9 :=
    hpow.trans (le_mul_of_one_le_left (pow_nonneg hDpos.le 9) (by norm_num))
  exact (min_le_right _ _).trans (one_div_le_one_div_of_le hDpos hden)

theorem quadraticRectangleWidth_le_inverse_rectangleLog
    (A η : ℝ) (q : ℕ) (T r : ℝ) :
    quadraticRectangleWidth A η q T r ≤ 1 / rectangleLog q T :=
  (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

/-- The actual nonquadratic primary width is unchanged. All disk-growth
and zero-free hypotheses have been discharged from their exact sources. -/
theorem nonquadratic_logarithmic_reciprocal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 ≠ 1)
    (T β t : ℝ) (ht : |t| ≤ T)
    (hβlo : 1 - nonquadraticWidth q T / 2 ≤ β)
    (hβhi : β ≤ 1 + nonquadraticWidth q T) :
    ‖(χ.LFunction ((β : ℂ)+I*t))⁻¹‖ ≤
      logarithmicReciprocalBudget q T (nonquadraticWidth q T) := by
  have hχ : χ ≠ 1 := by intro h; exact hχsq (by rw [h,one_pow])
  exact reciprocal_from_conductorlog χ hχ (nonquadraticWidth_pos q T) (min_le_left _ _)
    (nonquadraticWidth_le_inverse_rectangleLog q T)
    (nonquadratic_finite_rectangle χ hχsq T) β t ht hβlo hβhi

/-- The uniform constant A precedes the original character and height.
The actual L(1) lower bound is the only retained quadratic analytic input;
no left-strip magnitude or rectangle nonvanishing is assumed. -/
theorem exists_quadratic_logarithmic_reciprocal
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ ^ 2 = 1 → χ ≠ 1 → c*(q : ℝ)^(-η) ≤ (χ.LFunction 1).re →
        ∀ T : ℝ, 0 ≤ T → ∀ β t : ℝ,
          let δ := quadraticRectangleWidth A η q T (c*(q : ℝ)^(-η))
          |t| ≤ T → 1-δ/2 ≤ β → β ≤ 1+δ →
          ‖(χ.LFunction ((β : ℂ)+I*t))⁻¹‖ ≤ logarithmicReciprocalBudget q T δ := by
  obtain ⟨A,hA,hzero⟩ := exists_quadratic_finite_rectangle c η hc hη
  refine ⟨A,hA,?_⟩
  intro q _ χ hquad hχ hL T hT β t
  dsimp only
  have hr : 0 < c*(q : ℝ)^(-η) :=
    mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos q) _)
  exact reciprocal_from_conductorlog χ hχ (quadraticRectangleWidth_pos hA q hT hr)
    (quadraticRectangleWidth_le_quarter A η q T _)
    (quadraticRectangleWidth_le_inverse_rectangleLog A η q T _)
    (hzero q χ hquad hχ hL T hT) β t

end
end ImbalancedChen.Part3.RoughConductorLogReciprocal20261026b

