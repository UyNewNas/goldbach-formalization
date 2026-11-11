import ImbalancedChen.P3HBWeightedOriginalChildrenL1
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
P3.6 / pinned manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F), original HB six-slot chart.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Pinned Lean v4.33.0-rc1 and Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

This module differentiates an ACTUAL coupled six-slot HB child in one
original log coordinate.  Unlike the preceding zero-order common-W
integral, W varies with this coordinate.  The derivative of W is paid
by a genuine HasDerivAt hypothesis on its coordinate restriction; the
HB derivative is derived from the existing genuine smooth logChild,
not assumed.  Only the ordinary one-axis Leibniz rule is claimed:
nothing here says the physical W_T supplies that hypothesis uniformly,
or identifies a full 2S mixed derivative, Fourier tail, arithmetic
discrepancy, or PP bound.
-/

namespace ImbalancedChen.P3HBWeightedAxisLeibniz
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogTensorRestoration

/-- The five original HB positional factors untouched when coordinate i
varies. The original label and multiplicity of each slot are retained. -/
def remainingTensor (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ) (i : Fin 6) : ℂ :=
  ∏ j ∈ (Finset.univ : Finset (Fin 6)).erase i,
    iteratedDeriv (orders j) (logChild chi (child j)) (u j)

/-- Factor the ACTUAL original six-slot separated derivative tensor at i.
No independent replacement tensor or symmetrization is introduced. -/
theorem logTensorMixed_axis_factor (chi : ℝ → ℂ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i : Fin 6) :
    iteratedDeriv (orders i) (logChild chi (child i)) (u i) *
      remainingTensor chi orders child u i =
        logTensorMixed chi orders child u := by
  classical
  unfold remainingTensor logTensorMixed
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin 6))
    (fun j => iteratedDeriv (orders j)
      (logChild chi (child j)) (u j)) (Finset.mem_univ i)]
  ring

/-- Actual original geometry evaluated on the i-th coordinate slice,
times the original HB derivative child with all other positional slots
frozen. The actual coupled weight is NOT assumed to factor by groups. -/
def coupledAxis (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ) (i : Fin 6)
    (W : (Fin 6 → ℝ) → ℂ) (t : ℝ) : ℂ :=
  (W (Function.update u i t) *
    iteratedDeriv (orders i) (logChild chi (child i)) t) *
      remainingTensor chi orders child u i

/-- The exact original tensor is recovered at the unchanged base point.
The function update is written literally to preserve all six positions. -/
theorem coupledAxis_at (chi : ℝ → ℂ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i : Fin 6)
    (W : (Fin 6 → ℝ) → ℂ) :
    coupledAxis chi orders child u i W (u i) =
      W (Function.update u i (u i)) *
        logTensorMixed chi orders child u := by
  change (W (Function.update u i (u i)) *
      iteratedDeriv (orders i) (logChild chi (child i)) (u i)) *
      remainingTensor chi orders child u i = _
  rw [mul_assoc, logTensorMixed_axis_factor]

/-- The first real directional derivative of the true common-W coupled
HB child. The only new analytic premise is differentiability of the
actual geometry on this coordinate slice; the child derivative comes
from the fixed C-infinity cutoff and iteratedDeriv_succ. -/
theorem coupledAxis_hasDerivAt (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i : Fin 6)
    (W : (Fin 6 → ℝ) → ℂ) (Wprime : ℂ)
    (hW : HasDerivAt (fun t : ℝ => W (Function.update u i t))
      Wprime (u i)) :
    HasDerivAt (coupledAxis chi orders child u i W)
      ((Wprime *
          iteratedDeriv (orders i) (logChild chi (child i)) (u i) +
        W (Function.update u i (u i)) *
          iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i)) *
        remainingTensor chi orders child u i)
      (u i) := by
  have hdiff : Differentiable ℝ
      (iteratedDeriv (orders i) (logChild chi (child i))) :=
    (logChild_contDiff chi hchi (child i)).differentiable_iteratedDeriv
      (orders i) (by simp)
  have hF : HasDerivAt
      (iteratedDeriv (orders i) (logChild chi (child i)))
      (iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i))
      (u i) := by
    simpa only [iteratedDeriv_succ] using (hdiff (u i)).hasDerivAt
  simpa only [coupledAxis] using
    (hW.mul hF).mul_const (remainingTensor chi orders child u i)

/-- Quantitative first-axis Leibniz cost for the SAME original child.
Bounds M0 and M1 concern genuine geometry value and coordinate
derivative, not Fourier discrepancy or a target-equivalent condition.
No claim of T/m-uniform physical admissibility is made. -/
theorem coupledAxis_derivative_norm_le (chi : ℝ → ℂ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i : Fin 6)
    (W : (Fin 6 → ℝ) → ℂ) (Wprime : ℂ)
    (K : ℕ) (C M0 M1 : ℝ)
    (hC : ∀ k a t, k ≤ K →
      ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (hk : orders i + 1 ≤ K)
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hW0 : ‖W (Function.update u i (u i))‖ ≤ M0)
    (hW1 : ‖Wprime‖ ≤ M1) :
    ‖(Wprime *
        iteratedDeriv (orders i) (logChild chi (child i)) (u i) +
      W (Function.update u i (u i)) *
        iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i)) *
      remainingTensor chi orders child u i‖ ≤
        ((M1 + M0) * C) *
          ‖remainingTensor chi orders child u i‖ := by
  have hk0 : orders i ≤ K := (Nat.le_succ _).trans hk
  have h1 :
      ‖Wprime *
        iteratedDeriv (orders i) (logChild chi (child i)) (u i)‖
        ≤ M1 * C := by
    rw [norm_mul]
    exact mul_le_mul hW1
      (hC (orders i) (child i) (u i) hk0) (norm_nonneg _) hM1
  have h0 :
      ‖W (Function.update u i (u i)) *
        iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i)‖
        ≤ M0 * C := by
    rw [norm_mul]
    exact mul_le_mul hW0
      (hC (orders i + 1) (child i) (u i) hk) (norm_nonneg _) hM0
  have hsum :
      ‖Wprime *
          iteratedDeriv (orders i) (logChild chi (child i)) (u i) +
        W (Function.update u i (u i)) *
          iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i)‖
        ≤ (M1 + M0) * C := by
    calc
      _ ≤ ‖Wprime *
            iteratedDeriv (orders i) (logChild chi (child i)) (u i)‖ +
          ‖W (Function.update u i (u i)) *
            iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i)‖ :=
        norm_add_le _ _
      _ ≤ M1 * C + M0 * C := add_le_add h1 h0
      _ = (M1 + M0) * C := by ring
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

end
end ImbalancedChen.P3HBWeightedAxisLeibniz
