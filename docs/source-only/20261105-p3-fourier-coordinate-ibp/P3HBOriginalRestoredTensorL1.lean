import ImbalancedChen.P3HBOriginalWholeDerivativeL1
import ImbalancedChen.P3HBSmoothLogTensorRestoration
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
P3.6 — restore the ORIGINAL unsplit six-position smooth HB tensor after
ALL ordered geometry/tensor Leibniz allocations, *before* taking norms.
The 3^6 labelled smooth children are summed, not identified or discarded.
The final integrable bound is inherited from the actual 729-labelled
whole-child derivative mass; it is not a new Fourier/PP assumption.

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 original HB dyadic factors, §4 (F) mixed physical L1.

The genuine original group product, the one complete-product trim,
every ordered derivative occurrence and original six-slot tensor remain.
This does not identify every frozen original W_T/U5/hat source, prove
uniform growing-m(T) Fourier bounds, or pay same-integer-rho arithmetic.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalRestoredTensorL1
noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBOriginalWholeChildAllOrder
open ImbalancedChen.P3HBOriginalWholeChildAllocationL1
open ImbalancedChen.P3HBOriginalWholeDerivativeL1

/-- Exact SIGNED sum over the original 729 differentiated smooth children.
It is not the positive mass sum: all complex cancellations are retained. -/
def originalRestoredWholeDerivative {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) : ℂ :=
  ∑ child ∈ smoothChildren,
    originalOrderedAxisDeriv (List.ofFn axes)
      (fun v => originalGroupPhysicalTrim chi eta c J s v *
        logTensorMixed chi orders child v) u

/-- First use the genuine all-order Leibniz result, then interchange TWO
literal finite labelled sums, and restore each positional HB tensor.
The right side keeps each binary owner, repeated axis and original group
occurrence; no 729-factor is inserted into this exact SIGNED identity. -/
theorem originalRestoredWholeDerivative_eq_owner {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) :
    originalRestoredWholeDerivative chi eta c J s orders axes u =
      ∑ owner : Fin k → Fin 2,
        originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupPhysicalTrim chi eta c J s) u *
        (∏ i : Fin 6,
          iteratedDeriv
            (childOrdersAfter orders (axesAssigned axes owner 1) i)
            (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v))
            (u i)) := by
  classical
  unfold originalRestoredWholeDerivative
  calc
    (∑ child ∈ smoothChildren,
      originalOrderedAxisDeriv (List.ofFn axes)
        (fun v => originalGroupPhysicalTrim chi eta c J s v *
          logTensorMixed chi orders child v) u) =
      ∑ child ∈ smoothChildren,
        wholeChildSum chi eta c J s orders child axes u := by
          apply Finset.sum_congr rfl
          intro child _
          exact originalWholeChild_ordered_eq_allocation
            chi eta hchi heta c J s orders child k axes u
    _ = ∑ owner : Fin k → Fin 2,
          originalOrderedAxisDeriv (axesAssigned axes owner 0)
            (originalGroupPhysicalTrim chi eta c J s) u *
          (∏ i : Fin 6,
            iteratedDeriv
              (childOrdersAfter orders (axesAssigned axes owner 1) i)
              (fun v : ℝ => chi (Real.exp v) - chi (2 * Real.exp v))
              (u i)) := by
      simp only [wholeChildSum, wholeChildTerm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro owner _
      calc
        (∑ child ∈ smoothChildren,
          originalOrderedAxisDeriv (axesAssigned axes owner 0)
            (originalGroupPhysicalTrim chi eta c J s) u *
          logTensorMixed chi
            (childOrdersAfter orders (axesAssigned axes owner 1))
            child u) =
          originalOrderedAxisDeriv (axesAssigned axes owner 0)
            (originalGroupPhysicalTrim chi eta c J s) u *
          (∑ child ∈ smoothChildren,
            logTensorMixed chi
              (childOrdersAfter orders (axesAssigned axes owner 1))
              child u) := by rw [Finset.mul_sum]
        _ = _ := by
          rw [logTensorMixed_children_sum chi hchi
            (childOrdersAfter orders (axesAssigned axes owner 1)) u]

/-- The SIGNED restored derivative is continuous because it is a finite
sum of genuine, continuous Leibniz derivatives. No measurability field. -/
theorem originalRestoredWholeDerivative_continuous {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6) :
    Continuous (originalRestoredWholeDerivative
      chi eta c J s orders axes) := by
  classical
  unfold originalRestoredWholeDerivative
  apply continuous_finsetSum smoothChildren
  intro child _
  have heq :
      (fun u : Fin 6 → ℝ =>
        originalOrderedAxisDeriv (List.ofFn axes)
          (fun v => originalGroupPhysicalTrim chi eta c J s v *
            logTensorMixed chi orders child v) u) =
      wholeChildSum chi eta c J s orders child axes := by
    funext u
    exact originalWholeChild_ordered_eq_allocation
      chi eta hchi heta c J s orders child k axes u
  rw [heq]
  exact wholeChildSum_continuous
    chi eta hchi heta c J s orders child axes

/-- Pointwise absolute control retains ALL original labels on the right.
This is a triangle inequality, not a fibre-relative PP estimate. -/
theorem originalRestoredWholeDerivative_norm_le_mass {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (axes : Fin k → Fin 6)
    (u : Fin 6 → ℝ) :
    ‖originalRestoredWholeDerivative chi eta c J s orders axes u‖ ≤
      wholeDerivativeChildrenMass chi eta c J s orders axes u := by
  unfold originalRestoredWholeDerivative wholeDerivativeChildrenMass
  exact norm_sum_le _ _

/-- Actual unsplit original six-slot HB derivative has an L1 majorant,
via the previously integrated whole 729-child derivative mass.
No requested L1 bound is hypothesized, and constants still precede g,
all original positive scales, ordered axes, slots and the integration
variable. K is fixed; growth of m(T) remains a separate internal duty. -/
theorem originalRestoredWholeDerivative_integrable_polynomial
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
        Integrable (fun u : Fin 6 → ℝ =>
          ‖originalRestoredWholeDerivative
            chi eta c J s orders axes u‖) ∧
        (∫ u : Fin 6 → ℝ,
          ‖originalRestoredWholeDerivative
            chi eta c J s orders axes u‖) ≤
          (2 : ℝ)^k *
          (((2 : ℝ)^k * (((g : ℝ) + 1) * B)^k * Ceta) *
            ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6)) := by
  classical
  obtain ⟨B, Ceta, C, hB, hCeta, hC, hwhole⟩ :=
    wholeDerivativeChildren_integrable_polynomial
      chi eta hchi heta hsmall hlarge hpsi hetaSmall hetaLarge K
  refine ⟨B, Ceta, C, hB, hCeta, hC, ?_⟩
  intro g k c J hc s hs axes hk orders horders
  obtain ⟨hmass, hmassBound⟩ :=
    hwhole g k c J hc s hs axes hk orders horders
  have hpoint (u : Fin 6 → ℝ) :
      ‖originalRestoredWholeDerivative chi eta c J s orders axes u‖ ≤
        wholeDerivativeChildrenMass chi eta c J s orders axes u :=
    originalRestoredWholeDerivative_norm_le_mass
      chi eta c J s orders axes u
  have hnonneg (u : Fin 6 → ℝ) :
      0 ≤ wholeDerivativeChildrenMass chi eta c J s orders axes u :=
    wholeDerivativeChildrenMass_nonneg chi eta c J s orders axes u
  have hcont := originalRestoredWholeDerivative_continuous
    chi eta hchi heta c J s orders axes
  have hint : Integrable (fun u : Fin 6 → ℝ =>
      ‖originalRestoredWholeDerivative
        chi eta c J s orders axes u‖) := by
    apply Integrable.mono' hmass hcont.norm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (by
      intro u
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (hnonneg u)] using hpoint u)
  exact ⟨hint, (integral_mono hint hmass hpoint).trans hmassBound⟩

end
end ImbalancedChen.P3HBOriginalRestoredTensorL1
