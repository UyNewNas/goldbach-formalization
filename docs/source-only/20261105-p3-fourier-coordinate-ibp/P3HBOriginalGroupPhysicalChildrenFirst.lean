import ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
import ImbalancedChen.P3HBWeightedTwoAxisLeibniz
import ImbalancedChen.P3HBSmoothLogTensorRestoration
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
P3.6 — first actual mixed axis of the literal original group-product ×
ONE complete physical-product trim × each of the 3^6 original labelled
smooth HB children, followed by the exact 729-child restoration.

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 and §4 (F), original physical dyadic scale and labels.

There is no prescribed derivative oracle: the geometry derivative is
formed with actualAxisDeriv of originalGroupPhysicalTrim and discharged
via the real coordinate-slice product rule. Repeated original HB positions
are not merged; the child is the exact old logTensorMixed indexed by the
same Fin 6 and Fin 3. No rho, physical modulus or mean is changed.

This is FIRST order on this one original six-position chart only.
It does NOT prove the m(N)-uniform 2S integrated L1, the remaining U5
geometry, full HB source admission, quantitative Fourier H tail, or PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Lean v4.33.0-rc1; pinned Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalGroupPhysicalChildrenFirst
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBWeightedAxisLeibniz
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz

/-- Exact original HB positional child weighted by ALL actual original
group occurrences and the ONE complete physical-product smooth trim. -/
def physicalOriginalChild {g : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) : ℂ :=
  originalGroupPhysicalTrim chi eta c J s u *
    logTensorMixed chi orders child u

/-- Actual coordinate derivative of ONE true physical labelled child.
This instantiates the previous generic coupled-axis formula with the
literal grouped geometry and its literal physical trim; neither of their
jets is supplied as an independent derivative-valued structure field. -/
theorem physicalOriginalChild_axisDeriv {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (physicalOriginalChild chi eta c J s orders child) i u =
      actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u *
        logTensorMixed chi orders child u +
      originalGroupPhysicalTrim chi eta c J s u *
        logTensorMixed chi (raiseOrder orders i) child u := by
  let W : (Fin 6 → ℝ) → ℂ := originalGroupPhysicalTrim chi eta c J s
  have hWDifferentiable :
      DifferentiableAt ℝ (fun t : ℝ => W (Function.update u i t)) (u i) := by
    change DifferentiableAt ℝ
      (fun t : ℝ =>
        originalGroupProduct chi c J (Function.update u i t) *
          physicalTrim eta s (Function.update u i t)) (u i)
    exact
      (originalGroupProduct_slice_differentiable chi hchi c J u i).mul
        (physicalTrim_slice_differentiable eta heta s u i)
  have hW : HasDerivAt
      (fun t : ℝ => W (Function.update u i t))
      (actualAxisDeriv W i u) (u i) := by
    simpa only [actualAxisDeriv] using hWDifferentiable.hasDerivAt
  have haxis := coupledAxis_hasDerivAt chi hchi orders child u i
    W (actualAxisDeriv W i u) hW
  have heq :
      (fun t : ℝ =>
        physicalOriginalChild chi eta c J s orders child
          (Function.update u i t)) =
      coupledAxis chi orders child u i W := by
    funext t
    exact (coupledAxis_eq_weighted_slice chi orders child u i W t).symm
  have hu : Function.update u i (u i) = u := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_noteq hj]
  change deriv
    (fun t : ℝ =>
      physicalOriginalChild chi eta c J s orders child
        (Function.update u i t)) (u i) = _
  rw [heq]
  rw [haxis.deriv]
  change
    ((actualAxisDeriv W i u *
        iteratedDeriv (orders i) (logChild chi (child i)) (u i) +
      W (Function.update u i (u i)) *
        iteratedDeriv (orders i + 1) (logChild chi (child i)) (u i)) *
      remainingTensor chi orders child u i) = _
  rw [hu]
  exact axis_expansion chi orders child u i
    (W u) (actualAxisDeriv W i u)

/-- The first physical derivative restores ALL 729 original labelled
children BEFORE norms. Both the derivative on the genuine geometry and
the derivative on the original six-slot HB tensor remain present. -/
theorem physicalOriginalChildren_axisDeriv_restoration {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (u : Fin 6 → ℝ) (i : Fin 6) :
    (∑ child ∈ smoothChildren,
      actualAxisDeriv (physicalOriginalChild chi eta c J s orders child) i u) =
      actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u *
        (∏ j : Fin 6,
          iteratedDeriv (orders j)
            (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v)) (u j)) +
      originalGroupPhysicalTrim chi eta c J s u *
        (∏ j : Fin 6,
          iteratedDeriv ((raiseOrder orders i) j)
            (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v)) (u j)) := by
  calc
    _ = ∑ child ∈ smoothChildren,
        (actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u *
          logTensorMixed chi orders child u +
        originalGroupPhysicalTrim chi eta c J s u *
          logTensorMixed chi (raiseOrder orders i) child u) := by
      apply Finset.sum_congr rfl
      intro child _
      exact physicalOriginalChild_axisDeriv chi eta hchi heta
        c J s orders child u i
    _ = actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u *
          (∑ child ∈ smoothChildren, logTensorMixed chi orders child u) +
        originalGroupPhysicalTrim chi eta c J s u *
          (∑ child ∈ smoothChildren,
            logTensorMixed chi (raiseOrder orders i) child u) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [logTensorMixed_children_sum chi hchi orders u,
        logTensorMixed_children_sum chi hchi (raiseOrder orders i) u]

/-- One genuine physical child derivative is controlled by the two
literal differentiated pieces, not an abstract prescribed jet mass. -/
theorem physicalOriginalChild_axisDeriv_norm_le {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i : Fin 6) :
    ‖actualAxisDeriv (physicalOriginalChild chi eta c J s orders child) i u‖ ≤
      ‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖ *
        ‖logTensorMixed chi orders child u‖ +
      ‖originalGroupPhysicalTrim chi eta c J s u‖ *
        ‖logTensorMixed chi (raiseOrder orders i) child u‖ := by
  rw [physicalOriginalChild_axisDeriv chi eta hchi heta
    c J s orders child u i]
  simpa only [norm_mul] using
    (norm_add_le
      (actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u *
        logTensorMixed chi orders child u)
      (originalGroupPhysicalTrim chi eta c J s u *
        logTensorMixed chi (raiseOrder orders i) child u))

/-- The full labelled 729-child first-derivative absolute mass is paid
by the TWO original tensor norms. No single fibre-relative Theta
requirement or Fourier-discrepancy bound appears in the premises. -/
theorem physicalOriginalChildren_axisDeriv_mass_le {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (u : Fin 6 → ℝ) (i : Fin 6) :
    (∑ child ∈ smoothChildren,
      ‖actualAxisDeriv (physicalOriginalChild chi eta c J s orders child) i u‖) ≤
      ‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖ *
        (∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖) +
      ‖originalGroupPhysicalTrim chi eta c J s u‖ *
        (∑ child ∈ smoothChildren,
          ‖logTensorMixed chi (raiseOrder orders i) child u‖) := by
  calc
    _ ≤ ∑ child ∈ smoothChildren,
        (‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖ *
          ‖logTensorMixed chi orders child u‖ +
        ‖originalGroupPhysicalTrim chi eta c J s u‖ *
          ‖logTensorMixed chi (raiseOrder orders i) child u‖) := by
      apply Finset.sum_le_sum
      intro child _
      exact physicalOriginalChild_axisDeriv_norm_le
        chi eta hchi heta c J s orders child u i
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.mul_sum]

end
end ImbalancedChen.P3HBOriginalGroupPhysicalChildrenFirst
