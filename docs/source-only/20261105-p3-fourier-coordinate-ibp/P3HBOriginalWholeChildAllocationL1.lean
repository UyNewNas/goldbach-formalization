import ImbalancedChen.P3HBOriginalWholeChildAllOrder
import ImbalancedChen.P3HBOriginalGroupJets729NoMeas
import Mathlib.Tactic

/-!
P3.6: pay ALL binary owner allocations in the six-dimensional L1
ledger, for every one of the original 3^6 labelled HB children.

This is the actual occurrence-indexed group product times ONE
complete-physical-product trim times the original positional HB tensor.
The inherited exact ordered Leibniz identity is used, not postulated.
Repeated axes and labels retain multiplicity.

For k <= K, each HB order can increase by at most k, so the predecessor
jet-times-tensor integral is applied at FIXED order 2*K, not at the
unjustified original cutoff K. All 2^k binary allocations are paid,
including the empty derivative word. The source does NOT yet assert
L1 of the whole derivative without a separate domination transfer,
nor the U5/full hats, growing m(T), Fourier or same-integer-rho PP.

Manuscript UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b
paper/source/modules/distribution-prime-product-completion-20261010.txt
sections 2 and 4(F). Fixed Lean v4.33.0-rc1,
Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalWholeChildAllocationL1
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalWholeChildAllOrder
open ImbalancedChen.P3HBOriginalGroupJets729Integrated
open ImbalancedChen.P3HBOriginalGroupJets729NoMeas

/-- A literal HB derivative word can raise each positional order by no
more than its length. Repeated occurrences are NOT collapsed. -/
theorem childOrdersAfter_le_add_length
    (orders : Fin 6 → ℕ) :
    ∀ (xs : List (Fin 6)) (i : Fin 6),
      childOrdersAfter orders xs i ≤ orders i + xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro i
      simp [childOrdersAfter]
  | cons j tail ih =>
      intro i
      have htail := ih i
      by_cases h : j = i
      · subst j
        simp only [childOrdersAfter, List.length_cons,
          raiseOrder, Function.update_same]
        omega
      · simp only [childOrdersAfter, List.length_cons,
          raiseOrder, Function.update_noteq h]
        omega

/-- Exact ORIGINAL owner term, summed over all 729 child labels before
integrating, not over a replacement set of smooth profiles. -/
def wholeOwnerChildrenMass {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (owner : Fin k → Fin 2) (u : Fin 6 → ℝ) : ℝ :=
  ∑ child ∈ smoothChildren,
    ‖wholeChildTerm chi eta c J s orders child axes owner u‖

/-- All 2^k original binary derivative allocations, each with 3^6
literal HB labels. Nothing is divided by an artificial label count. -/
def wholeAllocationChildrenMass {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) : ℝ :=
  ∑ owner : Fin k → Fin 2,
    wholeOwnerChildrenMass chi eta c J s orders axes owner u

/-- Each actual binary owner fibre is exactly the previous
geometry-jet x HB-tensor mass with the corresponding RAISED orders. -/
theorem wholeOwnerChildrenMass_eq_jet {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (owner : Fin k → Fin 2) (u : Fin 6 → ℝ) :
    wholeOwnerChildrenMass chi eta c J s orders axes owner u =
      originalGroupJetChildrenMass chi eta c J s
        (fun r : Fin (axesAssigned axes owner 0).length =>
          (axesAssigned axes owner 0).get r)
        (childOrdersAfter orders (axesAssigned axes owner 1)) u := by
  classical
  have hlist : List.ofFn
      (fun r : Fin (axesAssigned axes owner 0).length =>
        (axesAssigned axes owner 0).get r) =
      axesAssigned axes owner 0 := by simp
  unfold wholeOwnerChildrenMass originalGroupJetChildrenMass
  simp only [wholeChildTerm, hlist]

/-- Each literal original complete-child derivative is bounded by
the sum of ALL its actual binary owner terms. This uses the previous
exact differentiated product, NOT an assumed derivative family. -/
def wholeDerivativeChildrenMass {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) : ℝ :=
  ∑ child ∈ smoothChildren,
    ‖originalOrderedAxisDeriv (List.ofFn axes)
      (fun v => originalGroupPhysicalTrim chi eta c J s v *
        logTensorMixed chi orders child v) u‖

theorem wholeDerivativeChildrenMass_le_allocation {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) :
    wholeDerivativeChildrenMass chi eta c J s orders axes u ≤
      wholeAllocationChildrenMass chi eta c J s orders axes u := by
  classical
  unfold wholeDerivativeChildrenMass wholeAllocationChildrenMass
  calc
    (∑ child ∈ smoothChildren,
      ‖originalOrderedAxisDeriv (List.ofFn axes)
        (fun v => originalGroupPhysicalTrim chi eta c J s v *
          logTensorMixed chi orders child v) u‖) ≤
      ∑ child ∈ smoothChildren,
        ∑ owner : Fin k → Fin 2,
          ‖wholeChildTerm chi eta c J s orders child axes owner u‖ := by
        apply Finset.sum_le_sum
        intro child _
        rw [originalWholeChild_ordered_eq_allocation
          chi eta hchi heta c J s orders child k axes u]
        exact norm_sum_le _ _
    _ = ∑ owner : Fin k → Fin 2,
          wholeOwnerChildrenMass chi eta c J s orders axes owner u := by
        rw [Finset.sum_comm]
        rfl

/-- Genuine integrated payment of ALL 2^k owner allocations and ALL
3^6 labelled children. Constant choices precede g, physical scales,
orders, axes, owner and u; the only analytic data are the inherited
admissible smooth cutoffs and exact previously integrated jet estimate.

The 2^k in front pays the number of owners, the second 2^k pays the
group x trim jet Leibniz estimate: combined growth is 4^k.
Orders for the HB child are checked at 2*K, not silently at K. -/
theorem wholeAllocationChildren_integrable_polynomial
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ B Ceta C : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧ 0 ≤ C ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (orders : Fin 6 → ℕ), (∀ i, orders i ≤ K) →
        Integrable (wholeAllocationChildrenMass
          chi eta c J s orders axes) ∧
        (∫ u : Fin 6 → ℝ,
          wholeAllocationChildrenMass chi eta c J s orders axes u) ≤
          (2 : ℝ)^k *
          (((2 : ℝ)^k * (((g : ℝ) + 1) * B)^k * Ceta) *
            ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6)) := by
  classical
  obtain ⟨B, Ceta, C, hB, hCeta, hC, hjet⟩ :=
    originalGroupJetChildren_integrable_polynomial_no_meas
      chi eta hchi heta hsmall hlarge hpsi hetaSmall hetaLarge (K + K)
  refine ⟨B, Ceta, C, hB, hCeta, hC, ?_⟩
  intro g k c J hc s hs axes hk orders horders
  let A : ℝ := ((g : ℝ) + 1) * B
  let R : ℝ := (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6
  let M : ℝ := ((2 : ℝ)^k * A^k * Ceta) * R
  have hA : 1 ≤ A := by
    dsimp [A]
    have hg : (1 : ℝ) ≤ (g : ℝ) + 1 := by
      have hg0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
      linarith
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((g : ℝ) + 1) * B :=
        mul_le_mul hg hB (by norm_num) (by positivity)
  have hR : 0 ≤ R := by
    have hlog : 0 ≤ Real.log (2 : ℝ) :=
      Real.log_nonneg (by norm_num)
    dsimp [R]
    positivity
  have howner (owner : Fin k → Fin 2) :
      Integrable (wholeOwnerChildrenMass
        chi eta c J s orders axes owner) ∧
      (∫ u : Fin 6 → ℝ,
        wholeOwnerChildrenMass chi eta c J s orders axes owner u) ≤ M := by
    let geo := axesAssigned axes owner 0
    let subAxes : Fin geo.length → Fin 6 := fun r => geo.get r
    let raised := childOrdersAfter orders (axesAssigned axes owner 1)
    have hlength : geo.length ≤ K + K := by
      have hlen := axesAssigned_length_le axes owner 0
      omega
    have hraised (i : Fin 6) : raised i ≤ K + K := by
      have hword := childOrdersAfter_le_add_length
        orders (axesAssigned axes owner 1) i
      have hlen := axesAssigned_length_le axes owner 1
      have hi := horders i
      dsimp [raised]
      omega
    have hsub : List.ofFn subAxes = geo := by simp [subAxes]
    have hEq : wholeOwnerChildrenMass chi eta c J s orders axes owner =
      originalGroupJetChildrenMass chi eta c J s subAxes raised := by
        funext u
        exact wholeOwnerChildrenMass_eq_jet
          chi eta c J s orders axes owner u
    obtain ⟨hint, hbound⟩ :=
      hjet g geo.length c J hc s hs subAxes hlength raised hraised
    have hpow2 : (2 : ℝ)^geo.length ≤ (2 : ℝ)^k :=
      pow_le_pow_right₀ (by norm_num) (axesAssigned_length_le axes owner 0)
    have hpowA : A^geo.length ≤ A^k :=
      pow_le_pow_right₀ hA (axesAssigned_length_le axes owner 0)
    have hprod : (2 : ℝ)^geo.length * A^geo.length ≤
        (2 : ℝ)^k * A^k :=
      mul_le_mul hpow2 hpowA (by positivity) (by positivity)
    have hlocal :
        (∫ u : Fin 6 → ℝ,
          wholeOwnerChildrenMass chi eta c J s orders axes owner u) ≤
          ((2 : ℝ)^geo.length * A^geo.length * Ceta) * R := by
      rw [hEq]
      exact hbound
    have hlocalM :
        ((2 : ℝ)^geo.length * A^geo.length * Ceta) * R ≤ M := by
      dsimp [M]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hprod (by linarith : 0 ≤ Ceta)) hR
    exact ⟨by rw [hEq]; exact hint, hlocal.trans hlocalM⟩
  constructor
  · unfold wholeAllocationChildrenMass
    apply integrable_finset_sum
    intro owner _
    exact (howner owner).1
  · have hsum :
        (∫ u : Fin 6 → ℝ,
          wholeAllocationChildrenMass chi eta c J s orders axes u) =
        ∑ owner : Fin k → Fin 2,
          (∫ u : Fin 6 → ℝ,
            wholeOwnerChildrenMass chi eta c J s orders axes owner u) := by
      unfold wholeAllocationChildrenMass
      exact integral_finset_sum _ (fun owner _ => (howner owner).1)
    rw [hsum]
    calc
      (∑ owner : Fin k → Fin 2,
        (∫ u : Fin 6 → ℝ,
          wholeOwnerChildrenMass chi eta c J s orders axes owner u)) ≤
        ∑ _owner : Fin k → Fin 2, M := by
          apply Finset.sum_le_sum
          intro owner _
          exact (howner owner).2
      _ = (2 : ℝ)^k * M := by
          simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fun]
      _ = (2 : ℝ)^k *
          (((2 : ℝ)^k * (((g : ℝ) + 1) * B)^k * Ceta) *
            ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6)) := rfl

end
end ImbalancedChen.P3HBOriginalWholeChildAllocationL1
