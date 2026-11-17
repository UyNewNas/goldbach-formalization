import ImbalancedChen.P3HBOriginalPhysicalChildrenFirstPolynomial
import ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
import ImbalancedChen.P3HBOriginalGroupFinCons
import Mathlib.Tactic

/-!
P3.6 — ALL ordered physical six-coordinate derivatives of the ACTUAL
occurrence-indexed dyadic group product: polynomial, not exponential,
dependence on the number g of original groups at each fixed order k.

Frozen paper: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 (smooth nonnegative dyadic partition) and §4(F).

The original hpsi : ‖chi t - chi (2*t)‖ ≤ 1 is EXPLICIT and must
still be discharged for the actual selected nonnegative partition.
Unlike the old bound (3*C)^g, each unassigned ORIGINAL group costs 1.
Only at most k groups receive one or more derivative occurrences.
The full original g^k allocation multiplicity remains, with all
repeated coordinates, group occurrences and positive scales intact.

This is a manuscript-INTERNAL SOURCE_ONLY proof candidate, not compiled,
kernel-checked, an estimate for complete W_T or a same-rho PP theorem.
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalGroupPolynomialAllOrder
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupFinCons
open ImbalancedChen.P3HBOriginalPhysicalChildrenFirstPolynomial

/-- No group outside the image of the actual derivative-owner map
can receive an axis. The empty assigned word retains the zeroth jet. -/
theorem axesAssigned_nil_outside_image {g k : ℕ}
    (axes : Fin k → Fin 6) (owner : Fin k → Fin g)
    (j : Fin g)
    (hj : j ∉ (Finset.univ : Finset (Fin k)).image owner) :
    axesAssigned axes owner j = [] := by
  classical
  have hnot (r : Fin k) : owner r ≠ j := by
    intro hr
    apply hj
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hr⟩
  have hfilter (rs : List (Fin k)) :
      rs.filter (fun r => decide (owner r = j)) = [] := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [hnot r, ih]
  unfold axesAssigned
  rw [hfilter]
  rfl

/-- The number of original group OCCURRENCES touched by a k-letter
ordered derivative word is at most k; repetitions count only once
as active groups, but are not erased from their assigned words. -/
theorem active_group_count_le {g k : ℕ} (owner : Fin k → Fin g) :
    ((Finset.univ : Finset (Fin k)).image owner).card ≤ k := by
  calc
    ((Finset.univ : Finset (Fin k)).image owner).card ≤
        (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

/-- In a product of g factors, only the active image of the k
derivative owners pays B; all other factors pay exactly 1. This is
pure finite combinatorics, INCLUDING g=0 and k=0. -/
theorem indicator_product_bound {g k : ℕ}
    (B : ℝ) (hB : 1 ≤ B) (owner : Fin k → Fin g) :
    (∏ j : Fin g,
      if j ∈ (Finset.univ : Finset (Fin k)).image owner then B else 1)
      ≤ B ^ k := by
  classical
  let active : Finset (Fin g) :=
    (Finset.univ : Finset (Fin k)).image owner
  have hmask (S : Finset (Fin g)) :
      (∏ j ∈ S, if j ∈ active then B else 1) =
        B ^ (S.filter (fun j => j ∈ active)).card := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
        by_cases ha : j ∈ active
        · simp [hj, ha, ih, pow_succ, mul_comm]
        · simp [hj, ha, ih]
  have hall :
      (∏ j : Fin g, if j ∈ active then B else 1) =
        B ^ active.card := by
    simpa [active] using (hmask Finset.univ)
  change (∏ j : Fin g, if j ∈ active then B else 1) ≤ B ^ k
  rw [hall]
  exact pow_le_pow_right₀ hB (active_group_count_le owner)

/-- A single TRUE group-allocation term costs B^k, not B^g:
zero assigned words have the genuine contractive zeroth jet.
B>=1 is fixed BEFORE g, owner, original scales, derivative word and u. -/
theorem allocationTerm_le_polynomial
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (K : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)),
        (∀ j, 0 < c j) →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (owner : Fin k → Fin g) (u : Fin 6 → ℝ),
        allocationTerm chi c J axes owner u ≤ B ^ k := by
  classical
  obtain ⟨C, hC, hjet⟩ :=
    originalGroupOrderedDeriv_uniform_scale
      chi hchi hsmall hlarge K
  let B : ℝ := max 1 (3 * C)
  have hB : 1 ≤ B := le_max_left _ _
  have hjetB : 3 * C ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro g k c J hc axes hk owner u
  have hfactor (j : Fin g) :
      ‖originalOrderedAxisDeriv (axesAssigned axes owner j)
          (originalGroupDyadicFactor chi (c j) (J j)) u‖ ≤
        if j ∈ (Finset.univ : Finset (Fin k)).image owner
          then B else 1 := by
    by_cases hj : j ∈ (Finset.univ : Finset (Fin k)).image owner
    · simpa only [if_pos hj] using
        (hjet (c j) (hc j) (J j)
          (axesAssigned axes owner j)
          ((axesAssigned_length_le axes owner j).trans hk)
          u).trans hjetB
    · have hnil := axesAssigned_nil_outside_image axes owner j hj
      simp only [if_neg hj]
      rw [hnil]
      change ‖originalGroupDyadicFactor chi (c j) (J j) u‖ ≤ 1
      exact originalGroupFactor_norm_le_one chi hpsi (c j) (J j) u
  unfold allocationTerm
  calc
    (∏ j : Fin g,
      ‖originalOrderedAxisDeriv (axesAssigned axes owner j)
        (originalGroupDyadicFactor chi (c j) (J j)) u‖) ≤
      ∏ j : Fin g,
        (if j ∈ (Finset.univ : Finset (Fin k)).image owner
          then B else 1) := by
        apply Finset.prod_le_prod
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          exact hfactor j
    _ ≤ B ^ k := indicator_product_bound B hB owner

/-- All g^k original owner assignments are summed exactly. This is a
polynomial in g at each fixed derivative order k (and retains g=0).
No bound uniform in unbounded k is claimed. -/
theorem allocationMass_le_polynomial
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (K : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)),
        (∀ j, 0 < c j) →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (u : Fin 6 → ℝ),
        allocationMass chi c J axes u ≤ (g : ℝ) ^ k * B ^ k := by
  obtain ⟨B, hB, hterm⟩ :=
    allocationTerm_le_polynomial chi hchi hsmall hlarge hpsi K
  refine ⟨B, hB, ?_⟩
  intro g k c J hc axes hk u
  unfold allocationMass
  calc
    (∑ owner : Fin k → Fin g,
      allocationTerm chi c J axes owner u) ≤
        ∑ _owner : Fin k → Fin g, B ^ k := by
          apply Finset.sum_le_sum
          intro owner ho
          exact hterm g k c J hc axes hk owner u
    _ = (g : ℝ) ^ k * B ^ k := by
          simp [Finset.sum_const, nsmul_eq_mul, allocation_card]

/-- TRUE original repeated ordered mixed derivative, not a prescribed
jet field: the preceding actual Fin.cons product Leibniz identity
transfers the polynomial mass bound to the physical group product. -/
theorem originalGroupProduct_ordered_polynomial
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (K : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)),
        (∀ j, 0 < c j) →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (u : Fin 6 → ℝ),
        ‖originalOrderedAxisDeriv (List.ofFn axes)
            (originalGroupProduct chi c J) u‖ ≤
          (g : ℝ) ^ k * B ^ k := by
  obtain ⟨B, hB, hmass⟩ :=
    allocationMass_le_polynomial chi hchi hsmall hlarge hpsi K
  refine ⟨B, hB, ?_⟩
  intro g k c J hc axes hk u
  exact (originalGroupProduct_ordered_norm_le_mass
    chi hchi c J axes u).trans (hmass g k c J hc axes hk u)

end
end ImbalancedChen.P3HBOriginalGroupPolynomialAllOrder
