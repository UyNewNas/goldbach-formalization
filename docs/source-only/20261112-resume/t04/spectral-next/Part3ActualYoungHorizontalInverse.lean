import ImbalancedChen.Part3ActualYoungCriticalProjection
import Batteries.Tactic.OpenPrivate

/-! A vertical-uniform lower bound, rather than just nonvanishing, for
the original finite divisor determinant at every positive occupied level.
The bound keeps the factors of every prime of every divisor of L. -/
namespace ImbalancedChen.Part3.ActualYoungHorizontalInverse20261112

noncomputable section
open Complex Set Matrix
open scoped BigOperators Classical
open ActualYoungDilationInverse20261110 ActualYoungCuspCoefficients20261110
open ActualYoungCriticalProjection20261110 ActualCuspDenominatorClasses20261110
open private matrix_factor lower_det squared from ImbalancedChen.Part3ActualYoungDilationInverse

private def localRadius (p : ℕ) : ℝ := Real.exp (-(1/2 : ℝ)*Real.log p)
private def localFloor (p : ℕ) : ℝ := 1-(localRadius p)^2

private theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hn : 1 ≤ (n : ℝ))

private theorem twist_radius {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1/2 ≤ s.re) (n : ℕ) : ‖twist χ s n‖ ≤ localRadius n := by
  have h := log_nat_nonneg n
  rw [twist,norm_mul,posPower,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply (mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hs) h

private theorem floor_pos {p : ℕ} (hp : p.Prime) : 0 < localFloor p := by
  have hlog := Real.log_pos (by exact_mod_cast hp.one_lt : 1 < (p : ℝ))
  have h : localRadius p < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h' : 0 ≤ localRadius p := (Real.exp_pos _).le
  unfold localFloor
  nlinarith [mul_pos (sub_pos.mpr h) (by linarith : 0 < 1+localRadius p)]

private theorem squared_floor {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1/2 ≤ s.re) {p : ℕ} (hp : p.Prime) :
    localFloor p ≤ ‖1-squared χ s p‖ := by
  have h := twist_radius χ s hs p
  have R : ‖squared χ s p‖ ≤ (localRadius p)^2 := by
    change ‖if p=0 then (0 : ℂ) else (twist χ s p)^2‖ ≤ _
    rw [if_neg hp.ne_zero,norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have V := norm_sub_norm_le (1 : ℂ) (squared χ s p)
  rw [norm_one] at V
  unfold localFloor
  linarith

def divisorFloor (L : ℕ) : ℝ := ∏ d : Div L, ∏ p ∈ d.val.primeFactors, localFloor p

theorem divisorFloor_pos (L : ℕ) : 0 < divisorFloor L := by
  apply Finset.prod_pos
  intro d _
  exact Finset.prod_pos (fun p hp => floor_pos (Nat.prime_of_mem_primeFactors hp))

/-- A bound uniform through the critical line; even repeated prime factors
of a nonsquarefree level are retained through the product over divisors. -/
theorem det_lower {q : ℕ} (χ : DirichletCharacter ℂ q) (L : ℕ) (hL : 0 < L)
    {s : ℂ} (hs : 1/2 ≤ s.re) : divisorFloor L ≤ ‖(kernelMatrix χ s L).det‖ := by
  classical
  rw [divisorFloor,matrix_factor χ s L hL,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
    lower_det χ s L hL,Matrix.det_diagonal,one_mul,mul_one,norm_prod]
  apply Finset.prod_le_prod (fun d _ => (Finset.prod_pos
    (fun p hp => floor_pos (Nat.prime_of_mem_primeFactors hp))).le)
  intro d _
  have hd := (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 hL).ne'
  change _ ≤ ‖if d.val=0 then (0 : ℂ) else ∏ p ∈ d.val.primeFactors, (1-squared χ s p)‖
  rw [if_neg hd,norm_prod]
  exact Finset.prod_le_prod (fun p hp => (floor_pos (Nat.prime_of_mem_primeFactors hp)).le)
    (fun p hp => squared_floor χ hs (Nat.prime_of_mem_primeFactors hp))

private def signMass (ι : Type*) [Fintype ι] [DecidableEq ι] : ℝ :=
  ∑ σ : Equiv.Perm ι, ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖

private theorem det_upper {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (H : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ signMass ι := by
  classical
  rw [Matrix.det_apply']
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro σ _
  rw [norm_mul,norm_prod]
  exact mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun i _ => H (σ i) i))

private theorem adj_upper {q L : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1/2 ≤ s.re)
    (j b : Div L) : ‖(kernelMatrix χ s L).adjugate j b‖ ≤ signMass (Div L) := by
  classical
  have hTw (n : ℕ) : ‖twist χ s n‖ ≤ 1 := (twist_radius χ s hs n).trans
    (Real.exp_le_one_iff.mpr (by nlinarith [log_nat_nonneg n]))
  rw [Matrix.adjugate_apply]
  apply det_upper
  intro i k
  by_cases h : i=b
  · subst i
    rw [Matrix.updateRow_self]
    by_cases e : k=j <;> simp [Pi.single_apply,e,eq_comm]
  · rw [Matrix.updateRow_ne h]
    change ‖twist χ s _ * twist χ s _‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ (hTw _) (norm_nonneg _) (hTw _)

/-- The coefficient is Cramer's original adjugate divided by both genuine
denominators; no bound for an assumed inverse matrix enters. -/
theorem dilation_strip_bound {q L : ℕ} (χ : DirichletCharacter ℂ q) (hL : 0 < L)
    (j b : Div L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → ‖dilationCoefficient χ s j b‖ ≤ B := by
  let u := Real.log (((q^2*L : ℕ) : ℝ)/(band (q^2*L) (q*j.val) : ℝ))
  let D := divisorFloor L * Real.exp (-2*|u|)
  have hD : 0 < D := mul_pos (divisorFloor_pos L) (Real.exp_pos _)
  have hS : 0 ≤ signMass (Div L) := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨signMass (Div L)/D,div_nonneg hS hD.le,?_⟩
  intro s hs ht
  have U : Real.exp (-2*|u|) ≤ ‖levelFactor (q^2*L) (q*j.val) s‖ := by
    rw [levelFactor,posPower,Complex.norm_exp]
    change Real.exp _ ≤ Real.exp ((s*(u : ℂ)).re)
    rw [Complex.re_mul_ofReal]
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left (neg_abs_le u) (show 0 ≤ s.re by linarith)
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2-s.re) (abs_nonneg u)]
  have V := mul_le_mul (det_lower χ L hL hs) U (Real.exp_pos _).le (norm_nonneg _)
  rw [dilationCoefficient,norm_div,norm_mul]
  exact div_le_div₀ hS (adj_upper χ hs j b) hD V

end
end ImbalancedChen.Part3.ActualYoungHorizontalInverse20261112
