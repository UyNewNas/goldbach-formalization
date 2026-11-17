import ImbalancedChen.P3HBOriginalWholeChildAllocationL1
import ImbalancedChen.P3HBOriginalGroupJets729NoMeas
import ImbalancedChen.P3HBSmoothLogTensorRestoration
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
P3.6: transfer the ACTUAL complete derivative of every original HB child
to L1 using the already integrated all-owner mass. Preserve all 729
positional labels, repeated derivative coordinates, occurrence-indexed
original groups and the unique full physical product trim.
This is manuscript-internal and does not pay U5, every HB hat,
growing m(T), Fourier/H-box, or same-integer-rho arithmetic.
Pinned paper: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
sections 2 and 4(F). Lean v4.33.0-rc1; Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalWholeDerivativeL1
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupJets729NoMeas
open ImbalancedChen.P3HBOriginalWholeChildAllOrder
open ImbalancedChen.P3HBOriginalWholeChildAllocationL1

/-- The literal six-slot HB tensor with arbitrary finite order is continuous. -/
theorem logTensorMixed_continuous
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3) :
    Continuous (logTensorMixed chi orders child) := by
  unfold logTensorMixed
  apply continuous_finsetProd Finset.univ
  intro i _
  exact ((logChild_contDiff chi hchi (child i))
    .continuous_iteratedDeriv (orders i) le_top).comp (continuous_apply i)

/-- Genuine allocation term: smooth geometry jet times the actual tensor. -/
theorem wholeChildTerm_continuous {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (axes : Fin k → Fin 6) (owner : Fin k → Fin 2) :
    Continuous (wholeChildTerm chi eta c J s orders child axes owner) := by
  let word := axesAssigned axes owner 0
  let wordFn : Fin word.length → Fin 6 := fun r => word.get r
  have hword : List.ofFn wordFn = word := by simp [wordFn]
  have hW : Continuous
      (originalOrderedAxisDeriv word
        (originalGroupPhysicalTrim chi eta c J s)) := by
    rw [← hword]
    exact originalGroupPhysicalTrimJet_continuous
      chi eta hchi heta c J s wordFn
  unfold wholeChildTerm
  exact hW.mul (logTensorMixed_continuous chi hchi
    (childOrdersAfter orders (axesAssigned axes owner 1)) child)

/-- Continuity of the true finite sum over all ordered binary owners. -/
theorem wholeChildSum_continuous {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (axes : Fin k → Fin 6) :
    Continuous (wholeChildSum chi eta c J s orders child axes) := by
  classical
  unfold wholeChildSum
  apply continuous_finsetSum Finset.univ
  intro owner _
  exact wholeChildTerm_continuous
    chi eta hchi heta c J s orders child axes owner

/-- The full derivative mass is continuous by exact ordered Leibniz,
not by assuming derivative measurability or an abstract envelope. -/
theorem wholeDerivativeChildrenMass_continuous {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6) :
    Continuous (wholeDerivativeChildrenMass chi eta c J s orders axes) := by
  classical
  have hrepr :
      wholeDerivativeChildrenMass chi eta c J s orders axes =
        (fun u => ∑ child ∈ smoothChildren,
          ‖wholeChildSum chi eta c J s orders child axes u‖) := by
    funext u
    unfold wholeDerivativeChildrenMass
    apply Finset.sum_congr rfl
    intro child _
    rw [originalWholeChild_ordered_eq_allocation
      chi eta hchi heta c J s orders child k axes u]
  rw [hrepr]
  apply continuous_finsetSum smoothChildren
  intro child _
  exact (wholeChildSum_continuous
    chi eta hchi heta c J s orders child axes).norm

theorem wholeDerivativeChildrenMass_nonneg {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) :
    0 ≤ wholeDerivativeChildrenMass chi eta c J s orders axes u := by
  unfold wholeDerivativeChildrenMass
  exact Finset.sum_nonneg (fun child _ => norm_nonneg _)

/-- Full original 729-child derivative L1, using the genuine allocation
integrable majorant (not a new assumption on the desired integral).
The inherited estimate uses 2*K to pay all raised HB slot orders.
Constants precede every original group count, physical scale and label. -/
theorem wholeDerivativeChildren_integrable_polynomial
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
        Integrable (wholeDerivativeChildrenMass
          chi eta c J s orders axes) ∧
        (∫ u : Fin 6 → ℝ,
          wholeDerivativeChildrenMass chi eta c J s orders axes u) ≤
          (2 : ℝ)^k *
          (((2 : ℝ)^k * (((g : ℝ) + 1) * B)^k * Ceta) *
            ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6)) := by
  classical
  obtain ⟨B, Ceta, C, hB, hCeta, hC, halloc⟩ :=
    wholeAllocationChildren_integrable_polynomial
      chi eta hchi heta hsmall hlarge hpsi hetaSmall hetaLarge K
  refine ⟨B, Ceta, C, hB, hCeta, hC, ?_⟩
  intro g k c J hc s hs axes hk orders horders
  obtain ⟨hintAlloc, hboundAlloc⟩ :=
    halloc g k c J hc s hs axes hk orders horders
  have hcont := wholeDerivativeChildrenMass_continuous
    chi eta hchi heta c J s orders axes
  have hpoint (u : Fin 6 → ℝ) :
      wholeDerivativeChildrenMass chi eta c J s orders axes u ≤
        wholeAllocationChildrenMass chi eta c J s orders axes u :=
    wholeDerivativeChildrenMass_le_allocation
      chi eta hchi heta c J s orders axes u
  have hnonneg (u : Fin 6 → ℝ) :
      0 ≤ wholeDerivativeChildrenMass chi eta c J s orders axes u :=
    wholeDerivativeChildrenMass_nonneg chi eta c J s orders axes u
  have hint : Integrable
      (wholeDerivativeChildrenMass chi eta c J s orders axes) := by
    apply Integrable.mono' hintAlloc hcont.aestronglyMeasurable
    exact Filter.Eventually.of_forall (by
      intro u
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg u)]
        using hpoint u)
  exact ⟨hint, (integral_mono hint hintAlloc hpoint).trans hboundAlloc⟩

end
end ImbalancedChen.P3HBOriginalWholeDerivativeL1
