import ImbalancedChen.P3HBWeightedAxisLeibniz
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
P3.6 / frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F). Lean v4.33.0-rc1, pinned Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

SOURCE_ONLY, NOT LEAN-ELABORATED, NOT KERNEL-VERIFIED.

A second genuine coordinate differentiation of the previous one-axis
coupled original six-slot HB expression. Both geometry derivative branches
are retained. The W derivative in the first direction must be supplied by
the actual geometry, and its derivative in the second direction is a
genuine additional analytic prerequisite, not an external (M) input.
Nothing asserts that the physical W_T/U5/trim family already supplies
these derivatives uniformly in T or growing m(N). No Fourier or PP claim.
-/

namespace ImbalancedChen.P3HBWeightedTwoAxisLeibniz
noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBWeightedAxisLeibniz

/-- Increment precisely one ORIGINAL HB derivative slot. -/
def raiseOrder (orders : Fin 6 → ℕ) (i : Fin 6) : Fin 6 → ℕ :=
  Function.update orders i (orders i + 1)

/-- All other original ordered slots remain unchanged when the i-th
physical log coordinate is varied. -/
theorem remainingTensor_update_axis
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ)
    (i : Fin 6) (t : ℝ) :
    remainingTensor chi orders child (Function.update u i t) i =
      remainingTensor chi orders child u i := by
  unfold remainingTensor
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Function.update_noteq hji]

/-- Exact original coordinate slice of the SAME coupled W and all
six HB slots, not a substitute separable geometry. -/
theorem coupledAxis_eq_weighted_slice
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ)
    (i : Fin 6) (W : (Fin 6 → ℝ) → ℂ) (t : ℝ) :
    coupledAxis chi orders child u i W t =
      W (Function.update u i t) *
        logTensorMixed chi orders child (Function.update u i t) := by
  have hfactor :=
    logTensorMixed_axis_factor chi orders child (Function.update u i t) i
  rw [remainingTensor_update_axis, Function.update_same] at hfactor
  unfold coupledAxis
  calc
    (W (Function.update u i t) *
      iteratedDeriv (orders i) (logChild chi (child i)) t) *
      remainingTensor chi orders child u i =
        W (Function.update u i t) *
          (iteratedDeriv (orders i) (logChild chi (child i)) t *
            remainingTensor chi orders child u i) := by ring
    _ = W (Function.update u i t) *
          logTensorMixed chi orders child (Function.update u i t) := by
      rw [hfactor]

/-- First-axis product-rule expression. The weight Di is meant to be
the real directional derivative of W in direction i, and is NOT assumed
to be a factor of W or a target-equivalent PP bound. -/
def firstAxisLeibniz (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ) (i : Fin 6)
    (W Di : (Fin 6 → ℝ) → ℂ) : ℂ :=
  Di u * logTensorMixed chi orders child u +
    W u * logTensorMixed chi (raiseOrder orders i) child u

/-- The actual second-coordinate slice of the first-axis Leibniz
expression is the sum of TWO original coupled-axis slices. -/
theorem firstAxisLeibniz_slice_eq
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ)
    (i j : Fin 6) (W Di : (Fin 6 → ℝ) → ℂ) :
    (fun t : ℝ =>
      firstAxisLeibniz chi orders child (Function.update u j t) i W Di) =
    (fun t : ℝ =>
      coupledAxis chi orders child u j Di t +
        coupledAxis chi (raiseOrder orders i) child u j W t) := by
  funext t
  unfold firstAxisLeibniz
  rw [coupledAxis_eq_weighted_slice, coupledAxis_eq_weighted_slice]

/-- Second coordinate derivative of the first-axis expression.
Genuine HasDerivAt prerequisites record D_j(D_i W) and D_j W.
The four terms arise from differentiating both coupled summands.
Even when i=j the two branches remain (and combine into the usual
factor 2); no mixed-Frechet or physical W_T admissibility is claimed. -/
theorem firstAxisLeibniz_second_hasDerivAt
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i j : Fin 6)
    (W Di Dj Dji : (Fin 6 → ℝ) → ℂ)
    (hDji : HasDerivAt
      (fun t : ℝ => Di (Function.update u j t)) (Dji u) (u j))
    (hDj : HasDerivAt
      (fun t : ℝ => W (Function.update u j t)) (Dj u) (u j)) :
    HasDerivAt
      (fun t : ℝ =>
        firstAxisLeibniz chi orders child (Function.update u j t) i W Di)
      (((Dji u *
          iteratedDeriv (orders j) (logChild chi (child j)) (u j) +
        Di (Function.update u j (u j)) *
          iteratedDeriv (orders j + 1) (logChild chi (child j)) (u j)) *
          remainingTensor chi orders child u j) +
       ((Dj u *
          iteratedDeriv ((raiseOrder orders i) j)
            (logChild chi (child j)) (u j) +
        W (Function.update u j (u j)) *
          iteratedDeriv ((raiseOrder orders i) j + 1)
            (logChild chi (child j)) (u j)) *
          remainingTensor chi (raiseOrder orders i) child u j))
      (u j) := by
  have hfirst :=
    coupledAxis_hasDerivAt chi hchi orders child u j Di (Dji u) hDji
  have hsecond :=
    coupledAxis_hasDerivAt chi hchi (raiseOrder orders i)
      child u j W (Dj u) hDj
  simpa only [firstAxisLeibniz_slice_eq] using hfirst.add hsecond

/-- Raising derivative order at slot j leaves the product of the other
five original HB positions intact. -/
theorem remainingTensor_raiseOrder
    (chi : ℝ → ℂ) (orders : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (u : Fin 6 → ℝ) (j : Fin 6) :
    remainingTensor chi (raiseOrder orders j) child u j =
      remainingTensor chi orders child u j := by
  unfold remainingTensor
  apply Finset.prod_congr rfl
  intro k hk
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [raiseOrder, Function.update_noteq hkj]

/-- Expand a genuine one-axis differentiated coupled factor into the
two corresponding complete original six-slot derivative tensors. -/
theorem axis_expansion (chi : ℝ → ℂ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (j : Fin 6) (V DV : ℂ) :
    ((DV * iteratedDeriv (orders j) (logChild chi (child j)) (u j) +
       V * iteratedDeriv (orders j + 1) (logChild chi (child j)) (u j)) *
       remainingTensor chi orders child u j) =
       DV * logTensorMixed chi orders child u +
         V * logTensorMixed chi (raiseOrder orders j) child u := by
  have h0 := logTensorMixed_axis_factor chi orders child u j
  have h1 := logTensorMixed_axis_factor
    chi (raiseOrder orders j) child u j
  rw [remainingTensor_raiseOrder] at h1
  simp only [raiseOrder, Function.update_same] at h1
  calc
    _ = DV *
        (iteratedDeriv (orders j) (logChild chi (child j)) (u j) *
          remainingTensor chi orders child u j) +
        V *
        (iteratedDeriv (orders j + 1) (logChild chi (child j)) (u j) *
          remainingTensor chi orders child u j) := by ring
    _ = DV * logTensorMixed chi orders child u +
          V * logTensorMixed chi (raiseOrder orders j) child u := by
      rw [h0, h1]

/-- Four-term genuine second-axis product rule, with the cross derivative
D_j D_i W and all ordered HB derivative orders kept separately. The
formula is conditional on ordinary geometric derivatives, not an
assumption about Fourier truncation, PP, rho, or modulus discrepancy. -/
theorem firstAxisLeibniz_second_four_terms
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i j : Fin 6)
    (W Di Dj Dji : (Fin 6 → ℝ) → ℂ)
    (hDji : HasDerivAt
      (fun t : ℝ => Di (Function.update u j t)) (Dji u) (u j))
    (hDj : HasDerivAt
      (fun t : ℝ => W (Function.update u j t)) (Dj u) (u j)) :
    HasDerivAt
      (fun t : ℝ =>
        firstAxisLeibniz chi orders child (Function.update u j t) i W Di)
      ((Dji u * logTensorMixed chi orders child u +
          Di u * logTensorMixed chi (raiseOrder orders j) child u) +
        (Dj u * logTensorMixed chi (raiseOrder orders i) child u +
          W u * logTensorMixed chi
            (raiseOrder (raiseOrder orders i) j) child u))
      (u j) := by
  have h := firstAxisLeibniz_second_hasDerivAt
    chi hchi orders child u i j W Di Dj Dji hDji hDj
  have hu : Function.update u j (u j) = u := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [Function.update_noteq hk]
  rw [hu] at h
  have hfirst := axis_expansion chi orders child u j (Di u) (Dji u)
  have hsecond := axis_expansion chi (raiseOrder orders i)
    child u j (W u) (Dj u)
  simpa only [hfirst, hsecond] using h

end
end ImbalancedChen.P3HBWeightedTwoAxisLeibniz
