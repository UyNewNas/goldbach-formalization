import ImbalancedChen.P3HBWeightedTwoAxisLeibniz

/-!
P3.6, frozen paper 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion section 4 (F).
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Canonical actual coordinate derivatives of the SAME nonseparable geometric W,
rather than freely supplied Di/Dj symbols. No W_T admissibility, uniform
T/m(N) envelope, Fourier-H tail, PP, arithmetic modulus or external (M).
-/

namespace ImbalancedChen.P3HBCanonicalGeometryDerivative
noncomputable section

open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBWeightedAxisLeibniz
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz

/-- Real-coordinate derivative of the actual complex geometry on the
original six-position chart, not a new independent jet field. -/
def actualAxisDeriv (W : (Fin 6 → ℝ) → ℂ)
    (i : Fin 6) (u : Fin 6 → ℝ) : ℂ :=
  deriv (fun t : ℝ => W (Function.update u i t)) (u i)

/-- Identifies the earlier freely written first-axis Leibniz expression
with the GENUINE derivative of the coupled original HB six-slot weight.
The only analytic assumption is pointwise differentiability of the
actual coordinate slice of W; the HB derivative comes from C-infinity chi.
-/
theorem actualAxisDeriv_weightedChild
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i : Fin 6)
    (W : (Fin 6 → ℝ) → ℂ)
    (hWi : DifferentiableAt ℝ
      (fun t : ℝ => W (Function.update u i t)) (u i)) :
    actualAxisDeriv
      (fun v => W v * logTensorMixed chi orders child v) i u =
      firstAxisLeibniz chi orders child u i W (actualAxisDeriv W i) := by
  have hW : HasDerivAt
      (fun t : ℝ => W (Function.update u i t))
      (actualAxisDeriv W i u) (u i) := by
    simpa only [actualAxisDeriv] using hWi.hasDerivAt
  have hCoupled := coupledAxis_hasDerivAt
    chi hchi orders child u i W (actualAxisDeriv W i u) hW
  have hu : Function.update u i (u i) = u := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_noteq hj]
  have hslice :
      (fun t : ℝ =>
        W (Function.update u i t) *
          logTensorMixed chi orders child (Function.update u i t)) =
        coupledAxis chi orders child u i W := by
    funext t
    exact (coupledAxis_eq_weighted_slice
      chi orders child u i W t).symm
  change deriv
      (fun t : ℝ =>
        W (Function.update u i t) *
          logTensorMixed chi orders child (Function.update u i t))
      (u i) =
        firstAxisLeibniz chi orders child u i W (actualAxisDeriv W i)
  rw [hslice]
  calc
    deriv (coupledAxis chi orders child u i W) (u i) =
        ((actualAxisDeriv W i u *
            iteratedDeriv (orders i) (logChild chi (child i)) (u i) +
          W (Function.update u i (u i)) *
            iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i)) *
          remainingTensor chi orders child u i) := hCoupled.deriv
    _ = ((actualAxisDeriv W i u *
            iteratedDeriv (orders i) (logChild chi (child i)) (u i) +
          W u *
            iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i)) *
          remainingTensor chi orders child u i) := by rw [hu]
    _ = firstAxisLeibniz chi orders child u i W
          (actualAxisDeriv W i) := by
      simpa only [firstAxisLeibniz] using
        (axis_expansion chi orders child u i (W u) (actualAxisDeriv W i u))

/-- True iterated coordinate derivative, including repeated i=j:
D_j(D_i(W * genuine HB child)). Di is now provably the derivative of W,
and D_j Di is its genuine iterated derivative, not an arbitrary field.
Assumptions are ordinary differentiability of W slices everywhere and
the explicitly selected slice of Di W. Not a uniform physical W_T bound.
-/
theorem actualTwoAxisDeriv_weightedChild
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i j : Fin 6)
    (W : (Fin 6 → ℝ) → ℂ)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (hDi : DifferentiableAt ℝ
      (fun t : ℝ =>
        actualAxisDeriv W i (Function.update u j t)) (u j)) :
    actualAxisDeriv
      (actualAxisDeriv
        (fun v => W v * logTensorMixed chi orders child v) i) j u =
      ((actualAxisDeriv (actualAxisDeriv W i) j u *
          logTensorMixed chi orders child u +
        actualAxisDeriv W i u *
          logTensorMixed chi (raiseOrder orders j) child u) +
       (actualAxisDeriv W j u *
          logTensorMixed chi (raiseOrder orders i) child u +
        W u *
          logTensorMixed chi
            (raiseOrder (raiseOrder orders i) j) child u)) := by
  have hSlice :
      (fun t : ℝ =>
        actualAxisDeriv
          (fun v => W v * logTensorMixed chi orders child v) i
          (Function.update u j t)) =
      (fun t : ℝ =>
        firstAxisLeibniz chi orders child (Function.update u j t)
          i W (actualAxisDeriv W i)) := by
    funext t
    exact actualAxisDeriv_weightedChild chi hchi orders child
      (Function.update u j t) i W (hW _ i)
  have hDj : HasDerivAt
      (fun t : ℝ => W (Function.update u j t))
      (actualAxisDeriv W j u) (u j) := by
    simpa only [actualAxisDeriv] using (hW u j).hasDerivAt
  have hDji : HasDerivAt
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t))
      (actualAxisDeriv (actualAxisDeriv W i) j u) (u j) := by
    simpa only [actualAxisDeriv] using hDi.hasDerivAt
  have hfour := firstAxisLeibniz_second_four_terms
    chi hchi orders child u i j
    W (actualAxisDeriv W i) (actualAxisDeriv W j)
    (actualAxisDeriv (actualAxisDeriv W i) j) hDji hDj
  change deriv
      (fun t : ℝ =>
        actualAxisDeriv
          (fun v => W v * logTensorMixed chi orders child v) i
          (Function.update u j t)) (u j) = _
  rw [hSlice]
  exact hfour.deriv

end
end ImbalancedChen.P3HBCanonicalGeometryDerivative
