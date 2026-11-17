import ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
import ImbalancedChen.P3HBOriginalGroupFinCons
import ImbalancedChen.P3HBOriginalGroupJetLeibnizStep
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
P3.6 — literal all-order derivative of the original occurrence-indexed
HB dyadic group product times ONE smooth complete physical-product trim.

Frozen paper UyNewNas/chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b,
PP-completion §2 and §4(F).
No substitute weight, omitted original slot, derivative-valued structure field,
Fourier-distribution estimate or shifted integer rho. Ordered repetitions remain.

This proof candidate uses real coordinate deriv, actual fixed C-infinity
profiles, the existing Fin.cons group allocation, and an exact binary
choice for each derivative occurrence. SOURCE_ONLY, uncompiled, kernel
unverified. Lean v4.33.0-rc1; Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalGroupTrimAllOrder
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupJetLeibnizStep
open ImbalancedChen.P3HBOriginalGroupFinCons
open ImbalancedChen.P3HBActualCompleteProductTrim
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst

/-- Every genuine grouped-product higher jet can be differentiated again
in a physical coordinate, via the already defined finite group-jet sum. -/
theorem groupJet_slice_differentiable {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (axes : List (Fin 6)) (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ
      (fun t : ℝ => originalOrderedAxisDeriv axes
        (originalGroupProduct chi c J) (Function.update u i t)) (u i) := by
  classical
  let a : Fin axes.length → Fin 6 := fun r => axes.get r
  have ha : List.ofFn a = axes := by
    simp [a]
  have heq :
      (fun t : ℝ => originalOrderedAxisDeriv axes
        (originalGroupProduct chi c J) (Function.update u i t)) =
      (fun t : ℝ => allocatedGroupJetSum chi c J a
        (Function.update u i t)) := by
    funext t
    rw [← ha]
    exact originalGroupProduct_ordered_eq_allocation chi hchi
      c J axes.length a (Function.update u i t)
  rw [heq]
  unfold allocatedGroupJetSum
  apply DifferentiableAt.fun_finsetSum
  intro owner ho
  exact allocatedGroupJetProduct_slice_differentiable
    chi hchi c J a owner u i

/-- Every ordered trim jet is differentiable, from the actual smooth
eta and exp; no separately prescribed trim derivative is assumed. -/
theorem trimJet_slice_differentiable
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (s : ℝ) (axes : List (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ
      (fun t : ℝ => originalOrderedAxisDeriv axes
        (physicalTrim eta s) (Function.update u i t)) (u i) := by
  have hp : ContDiff ℝ ⊤ (trimLogProfile eta s) := by
    unfold trimLogProfile
    fun_prop
  have hj : Differentiable ℝ
      (iteratedDeriv axes.length (trimLogProfile eta s)) :=
    (contDiff_iff_iteratedDeriv.mp hp).2 axes.length (by simp)
  have hsum : Differentiable ℝ
      (fun t : ℝ => originalGroupSum Finset.univ
        (Function.update u i t)) :=
    groupSum_slice_differentiable Finset.univ u i
  have heq :
      (fun t : ℝ => originalOrderedAxisDeriv axes
        (physicalTrim eta s) (Function.update u i t)) =
      (fun t : ℝ => iteratedDeriv axes.length (trimLogProfile eta s)
        (originalGroupSum Finset.univ (Function.update u i t))) := by
    funext t
    exact physicalTrim_orderedDeriv_exact eta s axes (Function.update u i t)
  rw [heq]
  exact (hj.comp hsum).differentiableAt

/-- Binary owner 0: the full genuine group product. Owner 1:
the SINGLE full physical-product trim. Every repeated axis is allocated. -/
def binaryTerm {g k : ℕ} (chi eta : ℝ → ℂ)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (owner : Fin k → Fin 2)
    (u : Fin 6 → ℝ) : ℂ :=
  originalOrderedAxisDeriv (axesAssigned axes owner 0)
    (originalGroupProduct chi c J) u *
  originalOrderedAxisDeriv (axesAssigned axes owner 1)
    (physicalTrim eta s) u

def binarySum {g k : ℕ} (chi eta : ℝ → ℂ)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) : ℂ :=
  ∑ owner : Fin k → Fin 2, binaryTerm chi eta c J s axes owner u

/-- One more actual coordinate derivative creates exactly two terms. -/
theorem binaryTerm_axisDeriv {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (owner : Fin k → Fin 2)
    (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (binaryTerm chi eta c J s axes owner) i u =
      originalOrderedAxisDeriv (i :: axesAssigned axes owner 0)
        (originalGroupProduct chi c J) u *
      originalOrderedAxisDeriv (axesAssigned axes owner 1)
        (physicalTrim eta s) u +
      originalOrderedAxisDeriv (axesAssigned axes owner 0)
        (originalGroupProduct chi c J) u *
      originalOrderedAxisDeriv (i :: axesAssigned axes owner 1)
        (physicalTrim eta s) u := by
  have hG := groupJet_slice_differentiable chi hchi c J
    (axesAssigned axes owner 0) u i
  have hT := trimJet_slice_differentiable eta heta s
    (axesAssigned axes owner 1) u i
  have hu : Function.update u i (u i) = u := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_noteq hj]
  change deriv (fun t : ℝ =>
    originalOrderedAxisDeriv (axesAssigned axes owner 0)
      (originalGroupProduct chi c J) (Function.update u i t) *
    originalOrderedAxisDeriv (axesAssigned axes owner 1)
      (physicalTrim eta s) (Function.update u i t)) (u i) = _
  simpa only [actualAxisDeriv, originalOrderedAxisDeriv, hu] using
    (hG.hasDerivAt.mul hT.hasDerivAt).deriv

/-- The actual coordinate derivative passes through the finite
binary allocation sum, without changing derivative word order. -/
theorem binarySum_axisDeriv {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (binarySum chi eta c J s axes) i u =
      ∑ owner : Fin k → Fin 2,
        (originalOrderedAxisDeriv (i :: axesAssigned axes owner 0)
          (originalGroupProduct chi c J) u *
         originalOrderedAxisDeriv (axesAssigned axes owner 1)
          (physicalTrim eta s) u +
         originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupProduct chi c J) u *
         originalOrderedAxisDeriv (i :: axesAssigned axes owner 1)
          (physicalTrim eta s) u) := by
  classical
  have hu : Function.update u i (u i) = u := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_noteq hj]
  have hd := deriv_fun_sum
    (u := (Finset.univ : Finset (Fin k → Fin 2)))
    (A := fun owner t => binaryTerm chi eta c J s axes owner
      (Function.update u i t))
    (x := u i) (by
      intro owner ho
      exact (groupJet_slice_differentiable chi hchi c J
        (axesAssigned axes owner 0) u i).mul
        (trimJet_slice_differentiable eta heta s
          (axesAssigned axes owner 1) u i))
  have hsum :
      actualAxisDeriv (binarySum chi eta c J s axes) i u =
        ∑ owner : Fin k → Fin 2,
          actualAxisDeriv (binaryTerm chi eta c J s axes owner) i u := by
    simpa only [hu, actualAxisDeriv, binarySum] using hd
  rw [hsum]
  apply Finset.sum_congr rfl
  intro owner ho
  exact binaryTerm_axisDeriv chi eta hchi heta c J s axes owner u i

/-- Exact Fin.cons two-owner reindex. In particular the binary allocation
contains no artificially multiplied or discarded empty-word terms. -/
theorem binarySum_cons {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) (i : Fin 6) :
    binarySum chi eta c J s (Fin.cons i axes) u =
      ∑ owner : Fin k → Fin 2,
        (originalOrderedAxisDeriv (i :: axesAssigned axes owner 0)
          (originalGroupProduct chi c J) u *
         originalOrderedAxisDeriv (axesAssigned axes owner 1)
          (physicalTrim eta s) u +
         originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupProduct chi c J) u *
         originalOrderedAxisDeriv (i :: axesAssigned axes owner 1)
          (physicalTrim eta s) u) := by
  classical
  unfold binarySum
  rw [sum_owner_cons]
  apply Finset.sum_congr rfl
  intro owner ho
  rw [Fin.sum_univ_two]
  simp [binaryTerm, axesAssigned_cons]

/-- All finite ordered mixed derivatives of the literal GROUP product
times the ONE complete-product trim equal the true binary Leibniz sum.
No derivative values are supplied as a premise. -/
theorem originalGroupPhysicalTrim_ordered_eq_binary {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    ∀ (k : ℕ) (axes : Fin k → Fin 6) (u : Fin 6 → ℝ),
      originalOrderedAxisDeriv (List.ofFn axes)
        (originalGroupPhysicalTrim chi eta c J s) u =
      binarySum chi eta c J s axes u := by
  intro k
  induction k with
  | zero =>
      intro axes u
      simp [binarySum, binaryTerm, originalOrderedAxisDeriv,
        originalGroupPhysicalTrim, axesAssigned]
  | succ k ih =>
      intro axes u
      let rest : Fin k → Fin 6 := Fin.tail axes
      let first : Fin 6 := axes 0
      have hfun :
          originalOrderedAxisDeriv (List.ofFn rest)
            (originalGroupPhysicalTrim chi eta c J s) =
          binarySum chi eta c J s rest := by
        funext v
        exact ih rest v
      calc
        originalOrderedAxisDeriv (List.ofFn axes)
            (originalGroupPhysicalTrim chi eta c J s) u =
          actualAxisDeriv (binarySum chi eta c J s rest) first u := by
          rw [← Fin.cons_self_tail axes, List.ofFn_cons]
          change actualAxisDeriv
            (originalOrderedAxisDeriv (List.ofFn rest)
              (originalGroupPhysicalTrim chi eta c J s)) first u = _
          rw [hfun]
        _ = ∑ owner : Fin k → Fin 2,
            (originalOrderedAxisDeriv (first :: axesAssigned rest owner 0)
              (originalGroupProduct chi c J) u *
             originalOrderedAxisDeriv (axesAssigned rest owner 1)
              (physicalTrim eta s) u +
             originalOrderedAxisDeriv (axesAssigned rest owner 0)
              (originalGroupProduct chi c J) u *
             originalOrderedAxisDeriv (first :: axesAssigned rest owner 1)
              (physicalTrim eta s) u) :=
          binarySum_axisDeriv chi eta hchi heta c J s rest u first
        _ = binarySum chi eta c J s axes u := by
          simpa only [Fin.cons_self_tail] using
            (binarySum_cons chi eta c J s rest u first).symm

/-- Nonnegative source-specific mass: not yet an integrated 2S or PP
estimate. The next step must pay the actual six-chart integrated norm. -/
def binaryMass {g k : ℕ} (chi eta : ℝ → ℂ)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) : ℝ :=
  ∑ owner : Fin k → Fin 2,
    ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
      (originalGroupProduct chi c J) u‖ *
    ‖originalOrderedAxisDeriv (axesAssigned axes owner 1)
      (physicalTrim eta s) u‖

theorem originalGroupPhysicalTrim_ordered_norm_le_binaryMass {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) :
    ‖originalOrderedAxisDeriv (List.ofFn axes)
      (originalGroupPhysicalTrim chi eta c J s) u‖ ≤
      binaryMass chi eta c J s axes u := by
  rw [originalGroupPhysicalTrim_ordered_eq_binary
    chi eta hchi heta c J s k axes u]
  unfold binarySum binaryMass
  calc
    ‖∑ owner : Fin k → Fin 2,
      binaryTerm chi eta c J s axes owner u‖ ≤
      ∑ owner : Fin k → Fin 2,
        ‖binaryTerm chi eta c J s axes owner u‖ :=
      norm_sum_le _ _
    _ = ∑ owner : Fin k → Fin 2,
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupProduct chi c J) u‖ *
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 1)
          (physicalTrim eta s) u‖ := by
      apply Finset.sum_congr rfl
      intro owner ho
      simp [binaryTerm, norm_mul]

end
end ImbalancedChen.P3HBOriginalGroupTrimAllOrder
