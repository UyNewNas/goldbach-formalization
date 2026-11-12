import ImbalancedChen.P3HBOriginalGroupIncidenceSupport
import ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
P3.6 — actual one-axis differentiation of occurrence-indexed ORIGINAL
higher group jets, and then of their finite allocation sum.

Pinned paper: UyNewNas/chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b, PP §4 (F).
Pinned Lean: v4.33.0-rc1; Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

This proves the genuine differentiability needed to differentiate an
ALREADY ASSIGNED finite group-jet product. It does not assume any derivative
of that product as a field. The original group occurrences j:Fin g,
positive physical scales and repeated ordered axes remain literal.

The final reindexing by a new owner Fin (k+1) -> Fin g, which is required
to identify ALL k-th derivatives of the original complete product with
the allocation sum, is still OPEN. Nothing here is a PP or Fourier estimate.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalGroupJetLeibnizStep
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBCanonicalGeometryDerivative

/-- C-infinity of the LITERAL scalar psi(c*exp(s)) follows from chi,
without any differentiability assumptions on the derived jets. -/
theorem originalGroupProfile_contDiff
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi) (c : ℝ) :
    ContDiff ℝ ⊤ (groupDyadicLogProfile chi c) := by
  have he : ContDiff ℝ ⊤ (fun s : ℝ => c * Real.exp s) := by
    fun_prop
  have he2 : ContDiff ℝ ⊤ (fun s : ℝ => 2 * (c * Real.exp s)) := by
    fun_prop
  unfold groupDyadicLogProfile
  exact (hchi.comp he).sub (hchi.comp he2)

/-- Every finite-order LITERAL scalar derivative of the original smooth
profile is itself differentiable. This is not a postulated jet class. -/
theorem originalGroupProfile_iteratedDeriv_differentiable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : ℝ) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n (groupDyadicLogProfile chi c)) := by
  have hs := originalGroupProfile_contDiff chi hchi c
  exact (contDiff_iff_iteratedDeriv.mp hs).2 n (by simp)

/-- Any genuine ordered original-group derivative (including repetitions)
remains differentiable in the next physical original coordinate. This
uses the proved scalar/group-sum identity and genuine smoothness. -/
theorem originalGroupJet_slice_differentiable
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : ℝ) (J : Finset (Fin 6)) (axes : List (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ
      (fun t : ℝ => originalOrderedAxisDeriv axes
        (originalGroupDyadicFactor chi c J) (Function.update u i t))
      (u i) := by
  classical
  by_cases hall : axesWithinGroup J axes
  · have hfun :
        (fun t : ℝ => originalOrderedAxisDeriv axes
          (originalGroupDyadicFactor chi c J) (Function.update u i t)) =
        (fun t : ℝ => iteratedDeriv axes.length
          (groupDyadicLogProfile chi c)
          (originalGroupSum J (Function.update u i t))) := by
      funext t
      rw [originalGroupOrderedDeriv_exact chi c J axes]
      simp [hall]
    rw [hfun]
    exact ((originalGroupProfile_iteratedDeriv_differentiable
      chi hchi c axes.length).comp
        (groupSum_slice_differentiable J u i)).differentiableAt
  · have hfun :
        (fun t : ℝ => originalOrderedAxisDeriv axes
          (originalGroupDyadicFactor chi c J) (Function.update u i t)) =
        (fun _ : ℝ => (0 : ℂ)) := by
      funext t
      rw [originalGroupOrderedDeriv_exact chi c J axes]
      simp [hall]
    rw [hfun]
    fun_prop

/-- Product of true original grouped factor derivatives for one literal
allocation; COMPLEX valued, unlike the previous norm-only mass. -/
def allocatedGroupJetProduct {g k : ℕ}
    (chi : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (axes : Fin k → Fin 6)
    (owner : Fin k → Fin g) (u : Fin 6 → ℝ) : ℂ :=
  ∏ j : Fin g,
    originalOrderedAxisDeriv (axesAssigned axes owner j)
      (originalGroupDyadicFactor chi (c j) (J j)) u

/-- Each finite product of actual assigned jets is differentiable on
the next original physical coordinate, including repeated axes. -/
theorem allocatedGroupJetProduct_slice_differentiable {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (owner : Fin k → Fin g)
    (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ
      (fun t : ℝ => allocatedGroupJetProduct chi c J axes owner
        (Function.update u i t)) (u i) := by
  classical
  unfold allocatedGroupJetProduct
  exact DifferentiableAt.fun_finsetProd
    (u := (Finset.univ : Finset (Fin g)))
    (f := fun j t => originalOrderedAxisDeriv
      (axesAssigned axes owner j)
      (originalGroupDyadicFactor chi (c j) (J j)) (Function.update u i t))
    (x := u i) (by
      intro j hj
      exact originalGroupJet_slice_differentiable
        chi hchi (c j) (J j) (axesAssigned axes owner j) u i)

/-- TRUE derivative of a finite product of original group jets.
The new outer axis is prepended, not commuted or deduplicated. -/
theorem allocatedGroupJetProduct_axisDeriv {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (owner : Fin k → Fin g)
    (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (allocatedGroupJetProduct chi c J axes owner) i u =
      ∑ j : Fin g,
        (∏ l ∈ (Finset.univ.erase j),
          originalOrderedAxisDeriv (axesAssigned axes owner l)
            (originalGroupDyadicFactor chi (c l) (J l)) u) *
        originalOrderedAxisDeriv (i :: axesAssigned axes owner j)
          (originalGroupDyadicFactor chi (c j) (J j)) u := by
  classical
  have hupdate : Function.update u i (u i) = u := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_noteq h]
  have hd := deriv_fun_finsetProd
    (u := (Finset.univ : Finset (Fin g)))
    (f := fun j t => originalOrderedAxisDeriv
      (axesAssigned axes owner j)
      (originalGroupDyadicFactor chi (c j) (J j)) (Function.update u i t))
    (x := u i) (by
      intro j hj
      exact originalGroupJet_slice_differentiable
        chi hchi (c j) (J j) (axesAssigned axes owner j) u i)
  change deriv (fun t : ℝ => ∏ j : Fin g,
      originalOrderedAxisDeriv (axesAssigned axes owner j)
        (originalGroupDyadicFactor chi (c j) (J j))
          (Function.update u i t)) (u i) = _
  simpa only [hupdate, smul_eq_mul, actualAxisDeriv,
    originalOrderedAxisDeriv] using hd

/-- Finite COMPLEX sum across all ordered allocation maps. -/
def allocatedGroupJetSum {g k : ℕ}
    (chi : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) : ℂ :=
  ∑ owner : Fin k → Fin g, allocatedGroupJetProduct chi c J axes owner u

/-- TRUE derivative of the whole finite allocation sum.
The remaining combinatorial Fin.cons reindexing needed to obtain
D_(i::axes)(originalGroupProduct) is NOT asserted here. -/
theorem allocatedGroupJetSum_axisDeriv {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (allocatedGroupJetSum chi c J axes) i u =
      ∑ owner : Fin k → Fin g,
        ∑ j : Fin g,
          (∏ l ∈ (Finset.univ.erase j),
            originalOrderedAxisDeriv (axesAssigned axes owner l)
              (originalGroupDyadicFactor chi (c l) (J l)) u) *
          originalOrderedAxisDeriv (i :: axesAssigned axes owner j)
            (originalGroupDyadicFactor chi (c j) (J j)) u := by
  classical
  have hupdate : Function.update u i (u i) = u := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_noteq h]
  have hd := deriv_fun_sum
    (u := (Finset.univ : Finset (Fin k → Fin g)))
    (A := fun owner t => allocatedGroupJetProduct chi c J axes owner
      (Function.update u i t))
    (x := u i) (by
      intro owner ho
      exact allocatedGroupJetProduct_slice_differentiable
        chi hchi c J axes owner u i)
  have hsum :
      actualAxisDeriv (allocatedGroupJetSum chi c J axes) i u =
        ∑ owner : Fin k → Fin g,
          actualAxisDeriv (allocatedGroupJetProduct chi c J axes owner) i u := by
    simpa only [hupdate, actualAxisDeriv, allocatedGroupJetSum] using hd
  rw [hsum]
  apply Finset.sum_congr rfl
  intro owner ho
  exact allocatedGroupJetProduct_axisDeriv chi hchi c J axes owner u i

end
end ImbalancedChen.P3HBOriginalGroupJetLeibnizStep
