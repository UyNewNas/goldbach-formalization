import ImbalancedChen.P3HBOriginalGroupJets729NoMeas
import ImbalancedChen.P3HBCanonicalGeometryDerivative
import ImbalancedChen.P3HBWeightedTwoAxisLeibniz
import ImbalancedChen.P3HBOriginalGroupFinCons
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
P3.6: genuinely differentiated ALL-ORDER original HB child:
literal occurrence-indexed group product * ONE full-product physical trim
* one of the original six-position, three-way smooth children.

This uses genuine originalOrderedAxisDeriv, repeated ordered coordinate
occurrences and a literal Fin k -> Fin 2 derivative allocation.
The 729 children are not merged and no rho/physical modulus is changed.
Only the exact derivative identity is covered, not its integrated
uniform 2S bound, complete W_T/U5/hats, Fourier tail or arithmetic PP.

Paper: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
sections 2 and 4(F). Lean v4.33.0-rc1;
Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/
namespace ImbalancedChen.P3HBOriginalWholeChildAllOrder
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBWeightedAxisLeibniz
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupFinCons
open ImbalancedChen.P3HBOriginalGroupTrimAllOrder
open ImbalancedChen.P3HBOriginalGroupJets729NoMeas
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst

/-- Exact ordered original HB tensor derivative indices.
New coordinates are prepended; repeated axes are not deduplicated. -/
def childOrdersAfter (orders : Fin 6 → ℕ) : List (Fin 6) → Fin 6 → ℕ
  | [] => orders
  | i :: rest => raiseOrder (childOrdersAfter orders rest) i

/-- One actual physical-coordinate derivative of the original smooth HB
tensor increments just that positional slot. Derive from an old genuine
coupled derivative with constant weight, not an independent jet field. -/
theorem logTensorMixed_actualAxisDeriv
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (i : Fin 6) (u : Fin 6 → ℝ) :
    actualAxisDeriv (logTensorMixed chi orders child) i u =
      logTensorMixed chi (raiseOrder orders i) child u := by
  have hconst : DifferentiableAt ℝ
      (fun t : ℝ => (1 : ℂ)) (u i) := by fun_prop
  have h := actualAxisDeriv_weightedChild
    chi hchi orders child u i (fun _ => (1 : ℂ)) hconst
  simpa [firstAxisLeibniz, actualAxisDeriv] using h

/-- Exact high-order genuine tensor derivative; mixed axis order and
repetitions are kept, no assumption that partials commute. -/
theorem logTensorMixed_ordered_derivative
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3) :
    ∀ (axes : List (Fin 6)) (u : Fin 6 → ℝ),
      originalOrderedAxisDeriv axes (logTensorMixed chi orders child) u =
        logTensorMixed chi (childOrdersAfter orders axes) child u := by
  intro axes
  induction axes with
  | nil =>
      intro u
      rfl
  | cons i rest ih =>
      intro u
      have hfun :
          originalOrderedAxisDeriv rest (logTensorMixed chi orders child) =
            logTensorMixed chi (childOrdersAfter orders rest) child := by
        funext v
        exact ih v
      change actualAxisDeriv
        (originalOrderedAxisDeriv rest (logTensorMixed chi orders child))
        i u = _
      rw [hfun]
      exact logTensorMixed_actualAxisDeriv chi hchi
        (childOrdersAfter orders rest) child i u

/-- Every actual group*one-trim ordered jet is differentiable again:
use the existing exact finite binary derivative formula and the literal
smooth scalar group/trim factors. -/
theorem geometryJet_slice_differentiable {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : List (Fin 6)) (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ (fun t : ℝ =>
      originalOrderedAxisDeriv axes
        (originalGroupPhysicalTrim chi eta c J s)
        (Function.update u i t)) (u i) := by
  classical
  let a : Fin axes.length → Fin 6 := fun r => axes.get r
  have ha : List.ofFn a = axes := by simp [a]
  have heq :
      (fun t : ℝ => originalOrderedAxisDeriv axes
        (originalGroupPhysicalTrim chi eta c J s)
        (Function.update u i t)) =
      (fun t : ℝ => binarySum chi eta c J s a
        (Function.update u i t)) := by
    funext t
    rw [← ha]
    exact originalGroupPhysicalTrim_ordered_eq_binary
      chi eta hchi heta c J s axes.length a (Function.update u i t)
  rw [heq]
  unfold binarySum
  apply DifferentiableAt.fun_finsetSum
  intro owner ho
  exact (groupJet_slice_differentiable chi hchi c J
    (axesAssigned a owner 0) u i).mul
    (trimJet_slice_differentiable eta heta s
      (axesAssigned a owner 1) u i)

/-- One actual Leibniz allocation: derivative occurrences assigned to
geometry are literal ordered jets, others raise the actual HB slot orders. -/
def wholeChildTerm {g k : ℕ} (chi eta : ℝ → ℂ)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (axes : Fin k → Fin 6) (owner : Fin k → Fin 2)
    (u : Fin 6 → ℝ) : ℂ :=
  originalOrderedAxisDeriv (axesAssigned axes owner 0)
    (originalGroupPhysicalTrim chi eta c J s) u *
  logTensorMixed chi
    (childOrdersAfter orders (axesAssigned axes owner 1)) child u

def wholeChildSum {g k : ℕ} (chi eta : ℝ → ℂ)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) : ℂ :=
  ∑ owner : Fin k → Fin 2,
    wholeChildTerm chi eta c J s orders child axes owner u

/-- Two genuine branches from differentiating one allocated term.
The necessary geometry differentiability follows above, not from
a supplied derivative-valued structure or an analytic PP hypothesis. -/
theorem wholeChildTerm_axisDeriv {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (axes : Fin k → Fin 6) (owner : Fin k → Fin 2)
    (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (wholeChildTerm chi eta c J s orders child axes owner) i u =
      originalOrderedAxisDeriv (i :: axesAssigned axes owner 0)
        (originalGroupPhysicalTrim chi eta c J s) u *
      logTensorMixed chi
        (childOrdersAfter orders (axesAssigned axes owner 1)) child u +
      originalOrderedAxisDeriv (axesAssigned axes owner 0)
        (originalGroupPhysicalTrim chi eta c J s) u *
      logTensorMixed chi
        (raiseOrder (childOrdersAfter orders (axesAssigned axes owner 1)) i)
        child u := by
  have hslice := geometryJet_slice_differentiable
    chi eta hchi heta c J s (axesAssigned axes owner 0) u i
  have h := actualAxisDeriv_weightedChild chi hchi
    (childOrdersAfter orders (axesAssigned axes owner 1)) child u i
    (originalOrderedAxisDeriv (axesAssigned axes owner 0)
      (originalGroupPhysicalTrim chi eta c J s)) hslice
  change actualAxisDeriv (fun v =>
    originalOrderedAxisDeriv (axesAssigned axes owner 0)
      (originalGroupPhysicalTrim chi eta c J s) v *
    logTensorMixed chi (childOrdersAfter orders
      (axesAssigned axes owner 1)) child v) i u = _
  simpa only [firstAxisLeibniz, originalOrderedAxisDeriv] using h

/-- Genuine finite-sum differentiation, no missing assignment. -/
theorem wholeChildSum_axisDeriv {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (wholeChildSum chi eta c J s orders child axes) i u =
      ∑ owner : Fin k → Fin 2,
        (originalOrderedAxisDeriv (i :: axesAssigned axes owner 0)
          (originalGroupPhysicalTrim chi eta c J s) u *
         logTensorMixed chi
           (childOrdersAfter orders (axesAssigned axes owner 1)) child u +
         originalOrderedAxisDeriv (axesAssigned axes owner 0)
           (originalGroupPhysicalTrim chi eta c J s) u *
         logTensorMixed chi
           (raiseOrder (childOrdersAfter orders (axesAssigned axes owner 1)) i)
           child u) := by
  classical
  have hu : Function.update u i (u i) = u := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_noteq hj]
  have hd := deriv_fun_sum
    (u := (Finset.univ : Finset (Fin k → Fin 2)))
    (A := fun owner t =>
      wholeChildTerm chi eta c J s orders child axes owner
        (Function.update u i t))
    (x := u i) (by
      intro owner ho
      have hW := geometryJet_slice_differentiable
        chi eta hchi heta c J s (axesAssigned axes owner 0) u i
      have hW' : HasDerivAt (fun t : ℝ =>
          originalOrderedAxisDeriv (axesAssigned axes owner 0)
            (originalGroupPhysicalTrim chi eta c J s)
            (Function.update u i t))
          (actualAxisDeriv
            (originalOrderedAxisDeriv (axesAssigned axes owner 0)
              (originalGroupPhysicalTrim chi eta c J s)) i u) (u i) := by
        simpa only [actualAxisDeriv] using hW.hasDerivAt
      have hc := coupledAxis_hasDerivAt chi hchi
        (childOrdersAfter orders (axesAssigned axes owner 1)) child u i
        (originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupPhysicalTrim chi eta c J s))
        (actualAxisDeriv (originalOrderedAxisDeriv
          (axesAssigned axes owner 0)
          (originalGroupPhysicalTrim chi eta c J s)) i u) hW'
      have heq :
          (fun t : ℝ => wholeChildTerm
            chi eta c J s orders child axes owner (Function.update u i t)) =
          coupledAxis chi (childOrdersAfter orders
            (axesAssigned axes owner 1)) child u i
            (originalOrderedAxisDeriv (axesAssigned axes owner 0)
              (originalGroupPhysicalTrim chi eta c J s)) := by
        funext t
        exact (coupledAxis_eq_weighted_slice
          chi (childOrdersAfter orders (axesAssigned axes owner 1))
          child u i _ t)
            .symm
      rw [heq]
      exact hc.differentiableAt)
  have hsum :
      actualAxisDeriv (wholeChildSum chi eta c J s orders child axes) i u =
        ∑ owner : Fin k → Fin 2,
          actualAxisDeriv
            (wholeChildTerm chi eta c J s orders child axes owner) i u := by
    simpa only [hu, actualAxisDeriv, wholeChildSum] using hd
  rw [hsum]
  apply Finset.sum_congr rfl
  intro owner ho
  exact wholeChildTerm_axisDeriv
    chi eta hchi heta c J s orders child axes owner u i

/-- Exact binary Fin.cons owner reindex, including empty-word cases. -/
theorem wholeChildSum_cons {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) (i : Fin 6) :
    wholeChildSum chi eta c J s orders child (Fin.cons i axes) u =
      ∑ owner : Fin k → Fin 2,
        (originalOrderedAxisDeriv (i :: axesAssigned axes owner 0)
          (originalGroupPhysicalTrim chi eta c J s) u *
         logTensorMixed chi (childOrdersAfter orders
           (axesAssigned axes owner 1)) child u +
         originalOrderedAxisDeriv (axesAssigned axes owner 0)
           (originalGroupPhysicalTrim chi eta c J s) u *
         logTensorMixed chi (raiseOrder
           (childOrdersAfter orders (axesAssigned axes owner 1)) i)
           child u) := by
  classical
  unfold wholeChildSum
  rw [sum_owner_cons]
  apply Finset.sum_congr rfl
  intro owner ho
  rw [Fin.sum_univ_two]
  simp [wholeChildTerm, axesAssigned_cons, childOrdersAfter]

/-- Whole original HB child: all ordered derivative occurrences and
all 2^k genuine allocations, no replacement field or dropped labels.
The summand remains COMPLEX before applying triangle inequalities. -/
theorem originalWholeChild_ordered_eq_allocation {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3) :
    ∀ (k : ℕ) (axes : Fin k → Fin 6) (u : Fin 6 → ℝ),
      originalOrderedAxisDeriv (List.ofFn axes)
        (fun v => originalGroupPhysicalTrim chi eta c J s v *
          logTensorMixed chi orders child v) u =
      wholeChildSum chi eta c J s orders child axes u := by
  intro k
  induction k with
  | zero =>
      intro axes u
      simp [wholeChildSum, wholeChildTerm, originalOrderedAxisDeriv,
        axesAssigned, childOrdersAfter]
  | succ k ih =>
      intro axes u
      let rest : Fin k → Fin 6 := Fin.tail axes
      let first : Fin 6 := axes 0
      have hfun :
          originalOrderedAxisDeriv (List.ofFn rest)
            (fun v => originalGroupPhysicalTrim chi eta c J s v *
              logTensorMixed chi orders child v) =
          wholeChildSum chi eta c J s orders child rest := by
        funext v
        exact ih rest v
      calc
        originalOrderedAxisDeriv (List.ofFn axes)
          (fun v => originalGroupPhysicalTrim chi eta c J s v *
            logTensorMixed chi orders child v) u =
          actualAxisDeriv
            (wholeChildSum chi eta c J s orders child rest) first u := by
          rw [← Fin.cons_self_tail axes, List.ofFn_cons]
          change actualAxisDeriv
            (originalOrderedAxisDeriv (List.ofFn rest)
              (fun v => originalGroupPhysicalTrim chi eta c J s v *
                logTensorMixed chi orders child v)) first u = _
          rw [hfun]
        _ = ∑ owner : Fin k → Fin 2,
          (originalOrderedAxisDeriv (first :: axesAssigned rest owner 0)
            (originalGroupPhysicalTrim chi eta c J s) u *
           logTensorMixed chi (childOrdersAfter orders
             (axesAssigned rest owner 1)) child u +
           originalOrderedAxisDeriv (axesAssigned rest owner 0)
             (originalGroupPhysicalTrim chi eta c J s) u *
           logTensorMixed chi (raiseOrder
             (childOrdersAfter orders (axesAssigned rest owner 1)) first)
             child u) :=
          wholeChildSum_axisDeriv
            chi eta hchi heta c J s orders child rest u first
        _ = wholeChildSum chi eta c J s orders child axes u := by
          simpa only [Fin.cons_self_tail] using
            (wholeChildSum_cons chi eta c J s orders child rest u first).symm

end
end ImbalancedChen.P3HBOriginalWholeChildAllOrder
