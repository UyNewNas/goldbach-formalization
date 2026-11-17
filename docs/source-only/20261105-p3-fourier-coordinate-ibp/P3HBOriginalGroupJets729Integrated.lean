import ImbalancedChen.P3HBOriginalGroupTrimPolynomialAllOrder
import ImbalancedChen.P3HBExplicitSmoothCutoffs
import ImbalancedChen.P3HBWeightedOriginalChildrenL1
import ImbalancedChen.P3HBLogDerivativeGlobalSupport
import Mathlib.Tactic

/-!
P3.6: genuine finite-order GEOMETRY-JET TIMES ALL 729 original HB
labelled children, integrated over the true six-dimensional log chart.

Frozen paper: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
section 2 and section 4 (F).

The actual ordered jet is taken from the complete original occurrence
group product times ONE complete-physical-product trim. It is not a
supplied jet field. The second factor is the literal original 3^6
smooth log-child tensor, with original positional labels and multiplicity.
This pays a genuine integrated contribution for EVERY fixed finite
ordered geometry derivative, including repeats and zero derivatives.

One ordinary MEASURABILITY premise on the genuine higher geometry jet
remains explicit. The exact high-order Leibniz identity for the product
of geometry with HB tensor, actual U5 and other hats, uniformity in
growing length, all Fourier/PP and same-rho arithmetic are NOT inferred.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Lean v4.33.0-rc1, pinned Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalGroupJets729Integrated
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBOriginalGroupTrimPolynomialAllOrder
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBLogDerivativeGlobalSupport
open ImbalancedChen.P3HBWeightedOriginalChildrenL1
open ImbalancedChen.P3HBExplicitSmoothCutoffs

/-- The literal absolute mass of one true ordered geometric jet
multiplied by EVERY original positional three-way HB child.
It is NOT defined to be the derivative of the whole product. -/
def originalGroupJetChildrenMass {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (orders : Fin 6 → ℕ)
    (u : Fin 6 → ℝ) : ℝ :=
  ∑ child ∈ smoothChildren,
    ‖originalOrderedAxisDeriv (List.ofFn axes)
      (originalGroupPhysicalTrim chi eta c J s) u *
       logTensorMixed chi orders child u‖

/-- Pointwise exact factoring is justified by the literal product,
before any L1 estimate. Every one of the 729 children is retained. -/
theorem originalGroupJetChildrenMass_eq {g k : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (orders : Fin 6 → ℕ)
    (u : Fin 6 → ℝ) :
    originalGroupJetChildrenMass chi eta c J s axes orders u =
      ‖originalOrderedAxisDeriv (List.ofFn axes)
        (originalGroupPhysicalTrim chi eta c J s) u‖ *
      (∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖) := by
  unfold originalGroupJetChildrenMass
  simp_rw [norm_mul]
  rw [Finset.mul_sum]

/-- A genuine integrated fixed-order geometric Leibniz contribution:
B, Ceta and C are selected before g, all positive physical scales,
ordered axes and the 729 HB labels. The only as-yet-undischarged premise
is measurable(norm of the LITERAL geometric ordered derivative), a
plain smoothness obligation, not the target integral/Fourier/PP estimate.

This proves the integral of each geometry-jet times HB-tensor term,
NOT the integral of the derivative of their PRODUCT. -/
theorem originalGroupJetChildren_integrable_polynomial
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
        Measurable (fun u : Fin 6 → ℝ =>
          ‖originalOrderedAxisDeriv (List.ofFn axes)
            (originalGroupPhysicalTrim chi eta c J s) u‖) →
        Integrable (originalGroupJetChildrenMass
          chi eta c J s axes orders) ∧
        (∫ u : Fin 6 → ℝ,
          originalGroupJetChildrenMass chi eta c J s axes orders u) ≤
          ((2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta) *
          ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6) := by
  classical
  obtain ⟨B, Ceta, hB, hCeta, hgeom⟩ :=
    originalGroupPhysicalTrim_ordered_polynomial
      chi eta hchi heta hsmall hlarge hpsi hetaSmall hetaLarge K
  obtain ⟨C, hCnonneg, hchild⟩ :=
    logChild_uniform_global_finite_order
      chi hchi hsmall hlarge K
  refine ⟨B, Ceta, C, hB, hCeta, hCnonneg, ?_⟩
  intro g k c J hc s hs axes hk orders horders hmeas
  let W : (Fin 6 → ℝ) → ℝ := fun u =>
    ‖originalOrderedAxisDeriv (List.ofFn axes)
      (originalGroupPhysicalTrim chi eta c J s) u‖
  let M : ℝ := (2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hWmeas : Measurable W := hmeas
  have hWbound (u : Fin 6 → ℝ) : |W u| ≤ M := by
    simpa only [W, abs_of_nonneg (norm_nonneg _), M] using
      (hgeom g k c J hc s hs axes hk u)
  have hident :
      originalGroupJetChildrenMass chi eta c J s axes orders =
        (fun u : Fin 6 → ℝ =>
          |W u| * (∑ child ∈ smoothChildren,
            ‖logTensorMixed chi orders child u‖)) := by
    funext u
    rw [originalGroupJetChildrenMass_eq]
    simp only [W, abs_of_nonneg (norm_nonneg _)]
  have hInt :
      Integrable (fun u : Fin 6 → ℝ =>
        |W u| * (∑ child ∈ smoothChildren,
          ‖logTensorMixed chi orders child u‖)) :=
    weighted_children_norm_integrable
      chi hchi hsmall hlarge orders W hWmeas M hWbound
  have hL1 :
      (∫ u : Fin 6 → ℝ,
        |W u| * (∑ child ∈ smoothChildren,
          ‖logTensorMixed chi orders child u‖)) ≤
        M * ((smoothChildren.card : ℝ) *
          ((2 * Real.log 2) * C) ^ 6) :=
    weighted_children_L1_le
      chi hchi hsmall hlarge K C hchild
        orders horders W hWmeas M hM hWbound
  constructor
  · rw [hident]
    exact hInt
  · rw [hident]
    exact hL1

/-- Apply the new six-dimensional all-729 integrated estimate to the
specific admissible Mathlib C-infinity smoothTransition chi/eta choice.
This fixes the cutoff-selection interface, but not other physical W_T
factors or higher-jet measurability. -/
theorem chosenGroupJetChildren_integrable_polynomial (K : ℕ) :
    ∃ B Ceta C : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧ 0 ≤ C ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (orders : Fin 6 → ℕ), (∀ i, orders i ≤ K) →
        Measurable (fun u : Fin 6 → ℝ =>
          ‖originalOrderedAxisDeriv (List.ofFn axes)
            (originalGroupPhysicalTrim chosenChi chosenEta c J s) u‖) →
        Integrable (originalGroupJetChildrenMass
          chosenChi chosenEta c J s axes orders) ∧
        (∫ u : Fin 6 → ℝ,
          originalGroupJetChildrenMass
            chosenChi chosenEta c J s axes orders u) ≤
          ((2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta) *
          ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6) := by
  exact originalGroupJetChildren_integrable_polynomial
    chosenChi chosenEta chosenChi_smooth chosenEta_smooth
    chosenChi_left chosenChi_right chosenChi_dyadic_contraction
    chosenEta_left chosenEta_right K

end
end ImbalancedChen.P3HBOriginalGroupJets729Integrated
