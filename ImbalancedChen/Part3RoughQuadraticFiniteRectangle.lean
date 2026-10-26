import ImbalancedChen.Part3RoughQuadraticLowRectangle
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLZeroFreeFiniteRectangleLogDerivative

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A genuine finite-height quadratic zero-free rectangle. Near t=0 we use
the proved low-height two-segment estimate; away from zero we bound the
ACTUAL H(q,t), including its reciprocal-height term, and use the pinned
quadratic headline. The positive L(1) lower bound is retained explicitly.
The finite-rectangle logarithmic derivative is then obtained with its
zero-free premise discharged. No uniform all-height strip is asserted.
-/

namespace ImbalancedChen.Part3.RoughQuadraticFiniteRectangle20261026b
noncomputable section
open Complex Set
open AnalyticNumberTheory.LargeSieve
open DirichletLGlobalConductorLogValueBound
open RoughQuadraticLowRectangle20261026b

def quadraticHeightBound (q : ℕ) (T r : ℝ) : ℝ :=
  2 + Real.log (rectangleCutoff q T) + Real.log (2 * (T + 1) + 2) +
    1 / (2 * lowHeight q T r)

theorem quadraticHeightBound_pos (q : ℕ) [NeZero q]
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 < r) :
    0 < quadraticHeightBound q T r := by
  have hM : (1 : ℝ) ≤ rectangleCutoff q T := by
    exact_mod_cast rectangleCutoff_pos q T
  have hlogM := Real.log_nonneg hM
  have hlogT : 0 ≤ Real.log (2 * (T + 1) + 2) := Real.log_nonneg (by linarith)
  have hinv : 0 < 1 / (2 * lowHeight q T r) :=
    one_div_pos.mpr (mul_pos (by norm_num) (lowHeight_pos q T hr))
  unfold quadraticHeightBound
  linarith

/-- The genuine quadratic H is uniformly bounded only after removing a
low-height box. Its reciprocal-height term has not been dropped. -/
theorem quadraticH_le_heightBound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {T r t : ℝ}
    (hT : 0 ≤ T) (hr : 0 < r) (ht : |t| ≤ T + 1)
    (htlow : lowHeight q T r ≤ |t|) :
    dirichletLQuadraticConditionalPowerZeroFreeH q t ≤ quadraticHeightBound q T r := by
  have hτ := lowHeight_pos q T hr
  have htpos : 0 < |t| := hτ.trans_le htlow
  have htne : t ≠ 0 := abs_pos.mp htpos
  have hcut := heightLog_le_rectangleLog χ hχ ht
  have hlog : Real.log (|2 * t| + 2) ≤ Real.log (2 * (T + 1) + 2) := by
    apply Real.log_le_log (by positivity)
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hinv : 1 / |2 * t| ≤ 1 / (2 * lowHeight q T r) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  simp only [dirichletLQuadraticConditionalPowerZeroFreeH, htne, ↓reduceDIte]
  unfold quadraticHeightBound rectangleLog at *
  linarith

def quadraticRectangleWidth (A η : ℝ) (q : ℕ) (T r : ℝ) : ℝ :=
  min (lowWidth q T r)
    (min (1 / 4) (A * (q : ℝ) ^ (-2 * η) / quadraticHeightBound q T r ^ 12))

theorem quadraticRectangleWidth_pos {A η T r : ℝ} (hA : 0 < A)
    (q : ℕ) [NeZero q] (hT : 0 ≤ T) (hr : 0 < r) :
    0 < quadraticRectangleWidth A η q T r := by
  unfold quadraticRectangleWidth
  exact lt_min (lowWidth_pos q T hr) (lt_min (by norm_num)
    (div_pos (mul_pos hA (Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos q) _))
      (pow_pos (quadraticHeightBound_pos q hT hr) 12)))

theorem quadraticRectangleWidth_le_quarter (A η : ℝ) (q : ℕ) (T r : ℝ) :
    quadraticRectangleWidth A η q T r ≤ 1 / 4 :=
  (min_le_right _ _).trans (min_le_left _ _)

/-- The constant A is supplied by the actual primary quadratic theorem,
before q, the original character, height, beta and moving imaginary part.
Only its genuine actual-L(1) lower input remains explicit. -/
theorem exists_quadratic_finite_rectangle (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ ^ 2 = 1 → χ ≠ 1 → c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        ∀ T : ℝ, 0 ≤ T →
          ∀ s : ℂ,
            1 - quadraticRectangleWidth A η q T (c * (q : ℝ) ^ (-η)) ≤ s.re →
            s.re ≤ 2 → |s.im| ≤ T + 1 → χ.LFunction s ≠ 0 := by
  obtain ⟨A,hA,hzero⟩ := exists_dirichletL_quadratic_conditional_powerZeroFree c η hc hη
  refine ⟨A,hA,?_⟩
  intro q _ χ hquad hχ hL T hT s hslo _hshi hst
  let r := c * (q : ℝ) ^ (-η)
  have hr : 0 < r := mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos q) _)
  by_cases hsone : 1 ≤ s.re
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hsone
  have hshi : s.re < 1 := lt_of_not_ge hsone
  have hrepr : (s.re : ℂ) + I * s.im = s := by
    simpa only [mul_comm I] using s.re_add_im
  rw [← hrepr]
  by_cases hlow : |s.im| ≤ lowHeight q T r
  · apply quadratic_low_rectangle χ hquad hχ hr hL hst hlow
    · exact le_trans (sub_le_sub_left (min_le_left _ _) 1) hslo
    · exact hshi.le
  have hhigh : lowHeight q T r ≤ |s.im| := (lt_of_not_ge hlow).le
  have hH := one_le_dirichletLQuadraticConditionalPowerZeroFreeH q s.im
  have hHpos : 0 < dirichletLQuadraticConditionalPowerZeroFreeH q s.im :=
    lt_of_lt_of_le zero_lt_one hH
  have hbound := quadraticH_le_heightBound χ hχ hT hr hst hhigh
  have hnum : 0 ≤ A * (q : ℝ) ^ (-2 * η) := by positivity
  have hratio :
      A * (q : ℝ) ^ (-2 * η) / quadraticHeightBound q T r ^ 12 ≤
        A * (q : ℝ) ^ (-2 * η) /
          dirichletLQuadraticConditionalPowerZeroFreeH q s.im ^ 12 :=
    div_le_div_of_nonneg_left hnum (pow_pos hHpos 12)
      (pow_le_pow_left₀ hHpos.le hbound 12)
  have hw : quadraticRectangleWidth A η q T r ≤
      A * (q : ℝ) ^ (-2 * η) /
        dirichletLQuadraticConditionalPowerZeroFreeH q s.im ^ 12 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans hratio
  apply hzero q χ s.re s.im hquad hχ hL
  exact ⟨le_trans (sub_le_sub_left hw 1) hslo,hshi⟩

/-- The finite-rectangle log derivative consumes derived nonvanishing,
not a newly assumed hzero and not a constant-width all-height premise. -/
theorem exists_quadratic_finite_rectangle_logDeriv
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ ^ 2 = 1 → χ ≠ 1 → c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        ∀ T : ℝ, 0 ≤ T → ∀ β t : ℝ,
          let δ := quadraticRectangleWidth A η q T (c * (q : ℝ) ^ (-η))
          |t| ≤ T → 1 - δ / 2 ≤ β → β ≤ 1 + δ →
          ‖logDeriv χ.LFunction ((β : ℂ) + I * t)‖ ≤
            40 / δ * Real.log (32 * q * (1 + |t|) / δ) := by
  obtain ⟨A,hA,hzero⟩ := exists_quadratic_finite_rectangle c η hc hη
  refine ⟨A,hA,?_⟩
  intro q _ χ hquad hχ hL T hT β t
  dsimp only
  have hr : 0 < c * (q : ℝ) ^ (-η) :=
    mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos q) _)
  exact Eq21FiniteLogDerivative.norm_logDeriv_LFunction_le_of_zeroFree_rectangle χ hχ
    (quadraticRectangleWidth_pos hA q hT hr)
    (quadraticRectangleWidth_le_quarter A η q T _) hT
    (hzero q χ hquad hχ hL T hT) t β

end
end ImbalancedChen.Part3.RoughQuadraticFiniteRectangle20261026b
