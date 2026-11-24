import ImbalancedChen.P4BSmoothProfileMixedFrechetBudget
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Actual prime Euler operators and all finite coordinate words

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The operator here is the actual p_i partial_i on prime-variable functions:
the Frechet derivative is evaluated on p_i times the i-th coordinate vector.
Finite words are recursively composed operators, not derivatives defined
by a chart. The chart identity is proved from its actual Jacobian and the
iterated Frechet derivative recursion. The actual profile's mixed chart
budget consequently bounds the genuine Euler words at every fixed order.
-/

namespace ImbalancedChen.P4B

noncomputable section

/-- The i-th coordinate vector in the original sup-norm plane. -/
def primeEulerCoordinateUnit (i : Fin 2) : Fin 2 → ℝ :=
  fun j => if j = i then 1 else 0

theorem primeEulerCoordinateUnit_norm_le (i : Fin 2) :
    ‖primeEulerCoordinateUnit i‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  by_cases hji : j = i <;> simp [primeEulerCoordinateUnit, hji]

/-- The actual prime-variable operator p_i partial_i. -/
def primeEulerOperator (i : Fin 2) (F : (Fin 2 → ℝ) → ℝ)
    (p : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ F p (p i • primeEulerCoordinateUnit i)

theorem primeEulerOperator_eq_coordinate_derivative
    (i : Fin 2) (F : (Fin 2 → ℝ) → ℝ) (p : Fin 2 → ℝ) :
    primeEulerOperator i F p = p i * fderiv ℝ F p (primeEulerCoordinateUnit i) := by
  simp only [primeEulerOperator, map_smul, smul_eq_mul]

/-- Ordered words in the actual operators; the head is the outer operator. -/
def primeEulerWord : (k : ℕ) → (Fin k → Fin 2) →
    ((Fin 2 → ℝ) → ℝ) → (Fin 2 → ℝ) → ℝ
  | 0, _, F => F
  | k + 1, w, F => primeEulerOperator (w 0) (primeEulerWord k (Fin.tail w) F)

theorem isOpen_positivePrimeOrthant_forEuler : IsOpen positivePrimeOrthant := by
  have heq : positivePrimeOrthant =
      ⋂ i : Fin 2, {p : Fin 2 → ℝ | 0 < p i} := by
    ext p
    simp [positivePrimeOrthant]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))

theorem primeEulerChart_mem_positivePrimeOrthant
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant) (z : Fin 2 → ℝ) :
    primeEulerChart p z ∈ positivePrimeOrthant := by
  intro i
  exact mul_pos (hp i) (Real.exp_pos _)

@[simp] theorem primeEulerChart_zero (p : Fin 2 → ℝ) : primeEulerChart p 0 = p := by
  funext i
  simp [primeEulerChart]

theorem contDiff_primeEulerChart (p : Fin 2 → ℝ) : ContDiff ℝ ∞ (primeEulerChart p) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.mul (contDiff_apply ℝ ℝ i).exp

/-- The actual diagonal derivative of the multiplicative coordinate chart. -/
def primeEulerChartJacobian (p z : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    primeEulerChart p z i • (ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ))

theorem hasFDerivAt_primeEulerChart (p z : Fin 2 → ℝ) :
    HasFDerivAt (primeEulerChart p) (primeEulerChartJacobian p z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  simpa only [primeEulerChart, smul_smul] using
    ((hasFDerivAt_apply (𝕜 := ℝ) i z).exp.const_mul (p i))

theorem primeEulerChartJacobian_coordinate (p z : Fin 2 → ℝ) (i : Fin 2) :
    primeEulerChartJacobian p z (primeEulerCoordinateUnit i) =
      primeEulerChart p z i • primeEulerCoordinateUnit i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [primeEulerChartJacobian, primeEulerCoordinateUnit]
  · simp [primeEulerChartJacobian, primeEulerCoordinateUnit, hji]

/-- First derivative conjugacy, assuming only differentiability of F at
the actual chart point. This is the p_i partial_i operator, not a chart definition. -/
theorem primeEulerOperator_chart_conjugacy
    (F : (Fin 2 → ℝ) → ℝ) (p z : Fin 2 → ℝ) (i : Fin 2)
    (hF : DifferentiableAt ℝ F (primeEulerChart p z)) :
    primeEulerOperator i F (primeEulerChart p z) =
      fderiv ℝ (fun y => F (primeEulerChart p y)) z (primeEulerCoordinateUnit i) := by
  have hchain := hF.hasFDerivAt.comp z (hasFDerivAt_primeEulerChart p z)
  rw [hchain.fderiv, ContinuousLinearMap.comp_apply, primeEulerChartJacobian_coordinate]
  rfl

/-- Euler differentiation preserves actual smoothness on the positive
open domain. No derivative-size bound is used for this closure property. -/
theorem contDiffOn_primeEulerOperator
    (F : (Fin 2 → ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F positivePrimeOrthant) (i : Fin 2) :
    ContDiffOn ℝ ∞ (primeEulerOperator i F) positivePrimeOrthant := by
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ F) positivePrimeOrthant :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_positivePrimeOrthant_forEuler).mp hF).2
  exact hDf.clm_apply ((contDiff_apply ℝ ℝ i).contDiffOn.smul contDiffOn_const)

theorem contDiffOn_primeEulerWord
    (F : (Fin 2 → ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F positivePrimeOrthant)
    (k : ℕ) (w : Fin k → Fin 2) :
    ContDiffOn ℝ ∞ (primeEulerWord k w F) positivePrimeOrthant := by
  induction k generalizing w with
  | zero => exact hF
  | succ k ih =>
      exact contDiffOn_primeEulerOperator (primeEulerWord k (Fin.tail w) F)
        (ih (Fin.tail w)) (w 0)

/-- Every finite ordered word in the actual Euler operators equals the
mixed chart tensor on its corresponding ordered coordinate vectors.
The proof uses the true operator recursion and the native tensor recursion. -/
theorem primeEulerWord_chart_conjugacy
    (F : (Fin 2 → ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F positivePrimeOrthant)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (k : ℕ) (w : Fin k → Fin 2) (z : Fin 2 → ℝ) :
    primeEulerWord k w F (primeEulerChart p z) =
      iteratedFDeriv ℝ k (fun y => F (primeEulerChart p y)) z
        (fun j => primeEulerCoordinateUnit (w j)) := by
  have hG : ContDiff ℝ ∞ (fun y => F (primeEulerChart p y)) :=
    hF.comp_contDiff (contDiff_primeEulerChart p)
      (primeEulerChart_mem_positivePrimeOrthant hp)
  induction k generalizing w z with
  | zero => simp [primeEulerWord]
  | succ k ih =>
      let H := primeEulerWord k (Fin.tail w) F
      have hH : ContDiffOn ℝ ∞ H positivePrimeOrthant :=
        contDiffOn_primeEulerWord F hF k (Fin.tail w)
      have hHdiff : DifferentiableAt ℝ H (primeEulerChart p z) :=
        (hH.contDiffAt (isOpen_positivePrimeOrthant_forEuler.mem_nhds
          (primeEulerChart_mem_positivePrimeOrthant hp z))).differentiableAt (by simp)
      have hIH : (fun y => H (primeEulerChart p y)) =
          fun y => iteratedFDeriv ℝ k (fun a => F (primeEulerChart p a)) y
            (fun j => primeEulerCoordinateUnit (Fin.tail w j)) := by
        funext y
        exact ih (Fin.tail w) y
      have hD : DifferentiableAt ℝ
          (iteratedFDeriv ℝ k (fun y => F (primeEulerChart p y))) z :=
        hG.contDiffAt.differentiableAt_iteratedFDeriv (by simp)
      change primeEulerOperator (w 0) H (primeEulerChart p z) = _
      rw [primeEulerOperator_chart_conjugacy H p z (w 0) hHdiff, hIH]
      symm
      exact hD.iteratedFDeriv_succ_apply_left'

/-- At time zero the chart base point is the original prime-variable point. -/
theorem primeEulerWord_eq_mixed_chart_tensor
    (F : (Fin 2 → ℝ) → ℝ) (hF : ContDiffOn ℝ ∞ F positivePrimeOrthant)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (k : ℕ) (w : Fin k → Fin 2) :
    primeEulerWord k w F p =
      iteratedFDeriv ℝ k (fun y => F (primeEulerChart p y)) 0
        (fun j => primeEulerCoordinateUnit (w j)) := by
  simpa only [primeEulerChart_zero] using primeEulerWord_chart_conjugacy F hF hp k w 0

/-- Actual arbitrary mixed Euler-operator words of the physical P4B
prime-variable profile. The constant is chosen before all widths, targets,
cutoffs, positive prime-variable points and coordinate words. -/
theorem exists_smoothPrimeVariableProfile_EulerWord_budget (k : ℕ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ p : Fin 2 → ℝ,
      p ∈ positivePrimeOrthant → ∀ w : Fin k → Fin 2,
        |primeEulerWord k w (smoothPrimeVariableProfile b N T width) p| ≤
          C / width ^ k := by
  obtain ⟨C, hC, hbudget⟩ := exists_smoothPrimeVariableProfile_mixed_chart_apply_budget k b
  refine ⟨C, hC, ?_⟩
  intro width hwidth N hN T p hp w
  rw [primeEulerWord_eq_mixed_chart_tensor (smoothPrimeVariableProfile b N T width)
    (contDiffOn_smoothPrimeVariableProfile b N T width) hp k w]
  exact hbudget width hwidth N hN T p hp 0
    (fun j => primeEulerCoordinateUnit (w j))
    (fun j => primeEulerCoordinateUnit_norm_le (w j))

end

end ImbalancedChen.P4B
