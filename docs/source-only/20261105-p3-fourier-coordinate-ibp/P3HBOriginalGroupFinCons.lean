import ImbalancedChen.P3HBOriginalGroupJetLeibnizStep
import ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
P3.6 manuscript-internal: the actual Fin.cons allocation reindex for
the LITERAL product of original occurrence-indexed physical dyadic groups.

Original paper: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b
paper/source/modules/distribution-prime-product-completion-20261010.txt, §4 (F).
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Every derivative occurrence is retained (including repeated coordinates);
every group occurrence and its independent physical positive scale are
retained. No commutation of mixed partials or quotient by repeated groups.
This is the missing COMBINATORIAL step following the actual differentiable
jet-product formula in P3HBOriginalGroupJetLeibnizStep.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalGroupFinCons
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupJetLeibnizStep

/-- The original ordered derivative occurrences allocated to l after
prepending a coordinate and its chosen owner. The newly prepended
occurrence belongs to j only; all older occurrences keep their order. -/
theorem axesAssigned_cons {g k : ℕ}
    (axes : Fin k → Fin 6) (owner : Fin k → Fin g)
    (i : Fin 6) (j l : Fin g) :
    axesAssigned (Fin.cons i axes) (Fin.cons j owner) l =
      if j = l then i :: axesAssigned axes owner l
      else axesAssigned axes owner l := by
  classical
  have hfin :
      List.finRange (k + 1) =
        (0 : Fin (k + 1)) :: (List.finRange k).map Fin.succ := by
    calc
      List.finRange (k + 1) =
          List.ofFn (fun r : Fin (k + 1) => r) :=
        (List.ofFn_id _).symm
      _ = (0 : Fin (k + 1)) ::
          List.ofFn (fun r : Fin k => r.succ) := by
        rw [List.ofFn_succ]
      _ = (0 : Fin (k + 1)) ::
          (List.finRange k).map Fin.succ := by
        rw [List.ofFn_eq_map]
  have htail (rs : List (Fin k)) :
      (((rs.map Fin.succ).filter
        (fun r => decide ((Fin.cons j owner) r = l))).map
          (Fin.cons i axes)) =
        ((rs.filter (fun r => decide (owner r = l))).map axes) := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
        by_cases hr : owner r = l
        · simp [hr, ih]
        · simp [hr, ih]
  unfold axesAssigned
  rw [hfin]
  by_cases h : j = l
  · simpa [h] using congrArg (List.cons i) (htail (List.finRange k))
  · simpa [h] using (htail (List.finRange k))

/-- Exact sum reindex: all (k+1)-step owner functions correspond
bijectively to the new owner and the old owner function. This includes
g=0, k=0, and repeated old owners, without added multiplicity. -/
theorem sum_owner_cons {g k : ℕ}
    (F : (Fin (k + 1) → Fin g) → ℂ) :
    (∑ newOwner : Fin (k + 1) → Fin g, F newOwner) =
      ∑ owner : Fin k → Fin g, ∑ j : Fin g,
        F (Fin.cons j owner) := by
  classical
  let e : (Fin (k + 1) → Fin g) ≃
      Fin g × (Fin k → Fin g) :=
    (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)).symm
  calc
    (∑ newOwner : Fin (k + 1) → Fin g, F newOwner) =
        ∑ p : Fin g × (Fin k → Fin g),
          F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv e
      intro newOwner
      simp [e, Fin.cons_self_tail]
    _ = ∑ j : Fin g, ∑ owner : Fin k → Fin g,
          F (Fin.cons j owner) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ owner : Fin k → Fin g, ∑ j : Fin g,
          F (Fin.cons j owner) := Finset.sum_comm

/-- Splitting the original complete (k+1)-assignment product by the
new owner's literal group occurrence. The other g-1 factors are unchanged;
the receiving occurrence receives i at the FRONT of its assigned list. -/
theorem allocatedGroupJetProduct_cons {g k : ℕ}
    (chi : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (owner : Fin k → Fin g)
    (u : Fin 6 → ℝ) (i : Fin 6) (j : Fin g) :
    allocatedGroupJetProduct chi c J (Fin.cons i axes)
        (Fin.cons j owner) u =
      (∏ l ∈ (Finset.univ.erase j),
        originalOrderedAxisDeriv (axesAssigned axes owner l)
          (originalGroupDyadicFactor chi (c l) (J l)) u) *
      originalOrderedAxisDeriv (i :: axesAssigned axes owner j)
        (originalGroupDyadicFactor chi (c j) (J j)) u := by
  classical
  unfold allocatedGroupJetProduct
  calc
    (∏ l : Fin g,
      originalOrderedAxisDeriv
        (axesAssigned (Fin.cons i axes) (Fin.cons j owner) l)
        (originalGroupDyadicFactor chi (c l) (J l)) u) =
      (∏ l ∈ (Finset.univ.erase j),
        originalOrderedAxisDeriv
          (axesAssigned (Fin.cons i axes) (Fin.cons j owner) l)
          (originalGroupDyadicFactor chi (c l) (J l)) u) *
      originalOrderedAxisDeriv
        (axesAssigned (Fin.cons i axes) (Fin.cons j owner) j)
        (originalGroupDyadicFactor chi (c j) (J j)) u := by
      symm
      exact Finset.prod_erase_mul (Finset.mem_univ j)
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl
        intro l hl
        have hne : j ≠ l := by
          exact Ne.symm (Finset.ne_of_mem_erase hl)
        rw [axesAssigned_cons]
        simp [hne]
      · rw [axesAssigned_cons]
        simp

/-- This is the exact reindexing missing from the previous true
allocated-jet Leibniz step: its double sum is the allocation sum for
Fin (k+1), with no artificially inserted derivative identity. -/
theorem allocatedGroupJetSum_cons {g k : ℕ}
    (chi : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) (i : Fin 6) :
    allocatedGroupJetSum chi c J (Fin.cons i axes) u =
      ∑ owner : Fin k → Fin g,
        ∑ j : Fin g,
          (∏ l ∈ (Finset.univ.erase j),
            originalOrderedAxisDeriv (axesAssigned axes owner l)
              (originalGroupDyadicFactor chi (c l) (J l)) u) *
          originalOrderedAxisDeriv (i :: axesAssigned axes owner j)
            (originalGroupDyadicFactor chi (c j) (J j)) u := by
  classical
  unfold allocatedGroupJetSum
  rw [sum_owner_cons]
  apply Finset.sum_congr rfl
  intro owner ho
  apply Finset.sum_congr rfl
  intro j hj
  exact allocatedGroupJetProduct_cons chi c J axes owner u i j

/-- Full candidate for the actual ORIGINAL ordered product derivative.
No derivative-valued hypothesis: induction uses the previous true
finite-jet-sum differentiation and the above exact owner reindex.
The order of repeated coordinates is not changed. -/
theorem originalGroupProduct_ordered_eq_allocation {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) :
    ∀ (k : ℕ) (axes : Fin k → Fin 6) (u : Fin 6 → ℝ),
      originalOrderedAxisDeriv (List.ofFn axes)
        (originalGroupProduct chi c J) u =
      allocatedGroupJetSum chi c J axes u := by
  intro k
  induction k with
  | zero =>
      intro axes u
      simp [allocatedGroupJetSum, allocatedGroupJetProduct,
        originalGroupProduct, axesAssigned, originalOrderedAxisDeriv]
  | succ k ih =>
      intro axes u
      let rest : Fin k → Fin 6 := Fin.tail axes
      let first : Fin 6 := axes 0
      have hfun :
          originalOrderedAxisDeriv (List.ofFn rest)
            (originalGroupProduct chi c J) =
          allocatedGroupJetSum chi c J rest := by
        funext v
        exact ih rest v
      calc
        originalOrderedAxisDeriv (List.ofFn axes)
            (originalGroupProduct chi c J) u =
          actualAxisDeriv (allocatedGroupJetSum chi c J rest)
            first u := by
          rw [← Fin.cons_self_tail axes, List.ofFn_cons]
          change actualAxisDeriv
            (originalOrderedAxisDeriv (List.ofFn rest)
              (originalGroupProduct chi c J)) first u = _
          rw [hfun]
        _ = ∑ owner : Fin k → Fin g,
            ∑ j : Fin g,
              (∏ l ∈ (Finset.univ.erase j),
                originalOrderedAxisDeriv (axesAssigned rest owner l)
                  (originalGroupDyadicFactor chi (c l) (J l)) u) *
              originalOrderedAxisDeriv (first :: axesAssigned rest owner j)
                (originalGroupDyadicFactor chi (c j) (J j)) u := by
          exact allocatedGroupJetSum_axisDeriv
            chi hchi c J rest u first
        _ = allocatedGroupJetSum chi c J axes u := by
          simpa only [Fin.cons_self_tail] using
            (allocatedGroupJetSum_cons chi c J rest u first).symm

/-- The exact earlier allocation mass now bounds the true whole
occurrence-product derivative, still without any W_T/U5/trim or
growing-m(N) uniformity assertion. -/
theorem originalGroupProduct_ordered_norm_le_mass {g k : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) :
    ‖originalOrderedAxisDeriv (List.ofFn axes)
        (originalGroupProduct chi c J) u‖ ≤
      allocationMass chi c J axes u := by
  rw [originalGroupProduct_ordered_eq_allocation chi hchi c J k axes u]
  unfold allocatedGroupJetSum allocationMass
  calc
    ‖∑ owner : Fin k → Fin g,
        allocatedGroupJetProduct chi c J axes owner u‖ ≤
      ∑ owner : Fin k → Fin g,
        ‖allocatedGroupJetProduct chi c J axes owner u‖ :=
          norm_sum_le _ _
    _ = ∑ owner : Fin k → Fin g,
        allocationTerm chi c J axes owner u := by
          apply Finset.sum_congr rfl
          intro owner ho
          simp [allocatedGroupJetProduct, allocationTerm, norm_prod]

end
end ImbalancedChen.P3HBOriginalGroupFinCons
