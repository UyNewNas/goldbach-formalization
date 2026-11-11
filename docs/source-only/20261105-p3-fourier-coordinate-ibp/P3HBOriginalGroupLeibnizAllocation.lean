import ImbalancedChen.P3HBOriginalGroupCoordinateMixed
import Mathlib.Tactic

/-!
P3.6 manuscript-internal actual original group derivative allocation budget.
Pinned paper UyNewNas/chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b §4 (F).
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

The group j : Fin g is an OCCURRENCE, not a distinct subset of axes.
Two occurrences of the same group keep their separate positive physical
scales. The axis r : Fin k is an ordered derivative OCCURRENCE, not
a distinct coordinate: repeats i=i are preserved, including their order.

This pays the actual grouped-factor jet terms and the exact g^k
combinatorial count for a future full-product Leibniz identity. It does
NOT establish that derivative identity, full W_T/U5/trim, the common
T,m(N) budget, Fourier tails, or same-integer-rho PP.
SOURCE_ONLY / NOT COMPILED / KERNEL NOT VERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed

/-- Original derivative occurrences owned by group j, in original order.
Filtering original INDEX positions retains repeated coordinate values. -/
def axesAssigned {g k : ℕ} (axes : Fin k → Fin 6)
    (owner : Fin k → Fin g) (j : Fin g) : List (Fin 6) :=
  ((List.finRange k).filter (fun r => decide (owner r = j))).map axes

/-- Allocation cannot increase derivative order. -/
theorem axesAssigned_length_le {g k : ℕ} (axes : Fin k → Fin 6)
    (owner : Fin k → Fin g) (j : Fin g) :
    (axesAssigned axes owner j).length ≤ k := by
  classical
  have hfilter :
      ((List.finRange k).filter (fun r => decide (owner r = j))).length ≤
        (List.finRange k).length :=
    List.length_filter_le _ _
  simpa [axesAssigned] using hfilter

/-- Product of ACTUAL original grouped-factor jet norms for one allocation.
Occurrence-indexed c and J cannot silently merge equal groups. -/
def allocationTerm {g k : ℕ}
    (chi : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (axes : Fin k → Fin 6)
    (owner : Fin k → Fin g) (u : Fin 6 → ℝ) : ℝ :=
  ∏ j : Fin g,
    ‖originalOrderedAxisDeriv (axesAssigned axes owner j)
      (originalGroupDyadicFactor chi (c j) (J j)) u‖

/-- Finite positive mass of all literal original-group allocations.
Not yet identified with the derivative of the whole product. -/
def allocationMass {g k : ℕ}
    (chi : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) : ℝ :=
  ∑ owner : Fin k → Fin g, allocationTerm chi c J axes owner u

/-- A derivative assigned outside its true group forces this actual
term to vanish. There is no need to pay this allocation. -/
theorem allocationTerm_zero_of_wrong_group {g k : ℕ}
    (chi : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (axes : Fin k → Fin 6)
    (owner : Fin k → Fin g) (u : Fin 6 → ℝ) (j : Fin g)
    (hwrong : ¬ axesWithinGroup (J j) (axesAssigned axes owner j)) :
    allocationTerm chi c J axes owner u = 0 := by
  classical
  unfold allocationTerm
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [originalGroupOrderedDeriv_exact chi (c j) (J j)
    (axesAssigned axes owner j) u]
  simp [hwrong]

/-- All allocations, including empty cases, are counted as g^k.
These are derivative occurrences, not distinct axes. -/
theorem allocation_card (g k : ℕ) :
    Fintype.card (Fin k → Fin g) = g ^ k := by
  simp [Fintype.card_fun]

/-- Uniform positive-scale bound for EACH actual original-group allocation.
The finite K is fixed before g, all physical scales and chosen axes. -/
theorem allocationTerm_le_fixed_order
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)),
        (∀ j, 0 < c j) →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
          ∀ (owner : Fin k → Fin g) (u : Fin 6 → ℝ),
            allocationTerm chi c J axes owner u ≤ (3 * C) ^ g := by
  obtain ⟨C, hC, hbound⟩ :=
    originalGroupOrderedDeriv_uniform_scale chi hchi hsmall hlarge K
  refine ⟨C, hC, ?_⟩
  intro g k c J hc axes hk owner u
  unfold allocationTerm
  calc
    (∏ j : Fin g, ‖originalOrderedAxisDeriv
        (axesAssigned axes owner j)
        (originalGroupDyadicFactor chi (c j) (J j)) u‖)
        ≤ ∏ _j : Fin g, (3 * C) := by
          apply Finset.prod_le_prod
          · intro j hj
            positivity
          · intro j hj
            exact hbound (c j) (hc j) (J j) _
              ((axesAssigned_length_le axes owner j).trans hk) u
    _ = (3 * C) ^ g := by simp

/-- Exact finite-combinatorial upper envelope for actual grouped jets.
For fixed group count g this costs g^k; the factor (3C)^g is NOT
uniform in an arbitrarily growing number of groups. The product
derivative = allocation sum remains a separate manuscript obligation. -/
theorem allocationMass_le_fixed_order
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)),
        (∀ j, 0 < c j) →
        ∀ (axes : Fin k → Fin 6), k ≤ K → ∀ (u : Fin 6 → ℝ),
          allocationMass chi c J axes u ≤ (g : ℝ) ^ k * (3 * C) ^ g := by
  obtain ⟨C, hC, hterm⟩ :=
    allocationTerm_le_fixed_order chi hchi hsmall hlarge K
  refine ⟨C, hC, ?_⟩
  intro g k c J hc axes hk u
  unfold allocationMass
  calc
    (∑ owner : Fin k → Fin g, allocationTerm chi c J axes owner u)
      ≤ ∑ _owner : Fin k → Fin g, (3 * C) ^ g := by
        apply Finset.sum_le_sum
        intro owner ho
        exact hterm g k c J hc axes hk owner u
    _ = (g : ℝ) ^ k * (3 * C) ^ g := by
        simp [Finset.sum_const, nsmul_eq_mul, allocation_card]

end
end ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
