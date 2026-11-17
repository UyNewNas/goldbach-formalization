import ImbalancedChen.P3HBOriginalGroupPhysicalChildrenFirst
import ImbalancedChen.P3HBSmoothTensorQuantitativeL1
import ImbalancedChen.P3HBWeightedOriginalChildrenL1
import ImbalancedChen.P3HBCoupledTwoAxisAutomaticMeas
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
P3.6 — actual six-dimensional L1 of the FIRST derivative of ALL 729
original HB children multiplied by the same original occurrence-indexed
physical dyadic group product and the ONE complete-product smooth trim.

Manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 and §4(F). Pinned Lean v4.33.0-rc1, Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Unlike an ordinary pointwise derivative ceiling, the inequality below
integrates the true finite labelled absolute sum over the ORIGINAL
Lebesgue product volume on (Fin 6 → ℝ). The only geometric premises are
ordinary measurability and zeroth/first actual derivative bounds; these
are not Fourier/PP/discrepancy estimates. The old group × trim source
supplies pointwise bounds but its global jet measurability and faithful
half-line eta extension still require source-only Lean checking.

No uniform g=m(T) conclusion, full U5, other HB source, 2S, H-box,
modulus discrepancy, special product=T or PP closure is claimed.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBLogDerivativeGlobalSupport
open ImbalancedChen.P3HBSmoothTensorL1
open ImbalancedChen.P3HBSmoothTensorQuantitativeL1
open ImbalancedChen.P3HBWeightedOriginalChildrenL1
open ImbalancedChen.P3HBCoupledTwoAxisAutomaticMeas
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBWeightedAxisLeibniz
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBOriginalGroupPhysicalChildrenFirst

/-- This is the genuine summed absolute first derivative of the 729
physical children, not the derivative of their already-summed weight. -/
def physicalChildrenFirstMass {g : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (i : Fin 6)
    (u : Fin 6 → ℝ) : ℝ :=
  ∑ child ∈ smoothChildren,
    ‖actualAxisDeriv
      (physicalOriginalChild chi eta c J s orders child) i u‖

/-- Measurability is derived from the ACTUAL Leibniz identity and the
usual measurability of the two genuine geometric jets. In particular we
DO NOT assume the target integrated mass is measurable or integrable. -/
theorem physicalChildrenFirstMass_measurable {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (i : Fin 6)
    (hWmeas : Measurable (originalGroupPhysicalTrim chi eta c J s))
    (hDWmeas : Measurable
      (actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i)) :
    Measurable (physicalChildrenFirstMass chi eta c J s orders i) := by
  have ht (child : Fin 6 → Fin 3) : Measurable (fun u : Fin 6 → ℝ =>
      ‖actualAxisDeriv
        (physicalOriginalChild chi eta c J s orders child) i u‖) := by
    have h0 := (logTensorMixed_continuous chi hchi orders child).measurable
    have h1 := (logTensorMixed_continuous chi hchi
      (raiseOrder orders i) child).measurable
    have heq : (fun u : Fin 6 → ℝ =>
        ‖actualAxisDeriv
          (physicalOriginalChild chi eta c J s orders child) i u‖) =
        (fun u => ‖actualAxisDeriv
            (originalGroupPhysicalTrim chi eta c J s) i u *
              logTensorMixed chi orders child u +
            originalGroupPhysicalTrim chi eta c J s u *
              logTensorMixed chi (raiseOrder orders i) child u‖) := by
      funext u
      rw [physicalOriginalChild_axisDeriv chi eta hchi heta
        c J s orders child u i]
    rw [heq]
    exact ((hDWmeas.mul h0).add (hWmeas.mul h1)).norm
  unfold physicalChildrenFirstMass
  apply Finset.measurable_sum
  intro child _
  exact ht child

/-- The original FULL 729-child first-axis absolute mass has genuine
Lebesgue L1 and a quantitative bound on the same six-coordinate chart.

M0 and M1 are ordinary, separately specified 0/1-jet size bounds for
the ACTUAL physical group product × single trim. Neither is an L1,
Fourier-tail, arithmetic-discrepancy, or PP hypothesis. In particular
this theorem does not assert their uniformity as the group count grows. -/
theorem physicalChildrenFirstMass_integrable_and_L1_le {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (i : Fin 6)
    (hk : ∀ j : Fin 6, orders j + 1 ≤ K)
    (hWmeas : Measurable (originalGroupPhysicalTrim chi eta c J s))
    (hDWmeas : Measurable
      (actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i))
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hW0 : ∀ u, ‖originalGroupPhysicalTrim chi eta c J s u‖ ≤ M0)
    (hW1 : ∀ u,
      ‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖ ≤ M1) :
    Integrable (physicalChildrenFirstMass chi eta c J s orders i) ∧
    (∫ u : Fin 6 → ℝ,
        physicalChildrenFirstMass chi eta c J s orders i u) ≤
      (M1 + M0) *
        ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6) := by
  let W : (Fin 6 → ℝ) → ℂ := originalGroupPhysicalTrim chi eta c J s
  let DW : (Fin 6 → ℝ) → ℂ := actualAxisDeriv W i
  let E : ℝ := (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C)^6
  let m0 : (Fin 6 → ℝ) → ℝ := fun u =>
    ∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖
  let m1 : (Fin 6 → ℝ) → ℝ := fun u =>
    ∑ child ∈ smoothChildren,
      ‖logTensorMixed chi (raiseOrder orders i) child u‖
  have hki (j : Fin 6) : (raiseOrder orders i) j ≤ K := by
    by_cases hj : j = i
    · subst j
      simpa [raiseOrder] using hk i
    · have hle : orders j ≤ K := by omega
      simpa [raiseOrder, Function.update_noteq hj] using hle
  have hk0 (j : Fin 6) : orders j ≤ K := by omega
  have hmeas0 : Measurable (fun u : Fin 6 → ℝ => ‖W u‖) := hWmeas.norm
  have hmeas1 : Measurable (fun u : Fin 6 → ℝ => ‖DW u‖) := hDWmeas.norm
  have hbound0 (u : Fin 6 → ℝ) : |‖W u‖| ≤ M0 := by
    simpa using hW0 u
  have hbound1 (u : Fin 6 → ℝ) : |‖DW u‖| ≤ M1 := by
    simpa using hW1 u
  have hInt0 : Integrable (fun u : Fin 6 → ℝ => ‖W u‖ * m1 u) :=
    by
      simpa only [m1, abs_of_nonneg (norm_nonneg _)] using
        (weighted_children_norm_integrable chi hchi hsmall hlarge
          (raiseOrder orders i) (fun u => ‖W u‖) hmeas0 M0 hbound0)
  have hInt1 : Integrable (fun u : Fin 6 → ℝ => ‖DW u‖ * m0 u) :=
    by
      simpa only [m0, abs_of_nonneg (norm_nonneg _)] using
        (weighted_children_norm_integrable chi hchi hsmall hlarge
          orders (fun u => ‖DW u‖) hmeas1 M1 hbound1)
  have hmajor : Integrable (fun u : Fin 6 → ℝ =>
      ‖DW u‖ * m0 u + ‖W u‖ * m1 u) := hInt1.add hInt0
  have hmassMeas : AEStronglyMeasurable
      (physicalChildrenFirstMass chi eta c J s orders i) :=
    (physicalChildrenFirstMass_measurable chi eta hchi heta
      c J s orders i hWmeas hDWmeas).aestronglyMeasurable
  have hnonneg (u : Fin 6 → ℝ) :
      0 ≤ physicalChildrenFirstMass chi eta c J s orders i u := by
    unfold physicalChildrenFirstMass
    exact Finset.sum_nonneg (fun child _ => norm_nonneg _)
  have hpoint (u : Fin 6 → ℝ) :
      physicalChildrenFirstMass chi eta c J s orders i u ≤
        ‖DW u‖ * m0 u + ‖W u‖ * m1 u :=
    physicalOriginalChildren_axisDeriv_mass_le
      chi eta hchi heta c J s orders u i
  have hactual : Integrable (physicalChildrenFirstMass chi eta c J s orders i) :=
    Integrable.mono_nonneg hmajor hmassMeas
      (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hpoint)
  have hb1 : (∫ u : Fin 6 → ℝ, ‖DW u‖ * m0 u) ≤ M1 * E := by
    simpa only [m0, E, abs_of_nonneg (norm_nonneg _)] using
      (weighted_children_L1_le chi hchi hsmall hlarge K C hC
        orders hk0 (fun u => ‖DW u‖) hmeas1 M1 hM1 hbound1)
  have hb0 : (∫ u : Fin 6 → ℝ, ‖W u‖ * m1 u) ≤ M0 * E := by
    simpa only [m1, E, abs_of_nonneg (norm_nonneg _)] using
      (weighted_children_L1_le chi hchi hsmall hlarge K C hC
        (raiseOrder orders i) hki (fun u => ‖W u‖) hmeas0 M0 hM0 hbound0)
  refine ⟨hactual, ?_⟩
  calc
    (∫ u : Fin 6 → ℝ,
      physicalChildrenFirstMass chi eta c J s orders i u) ≤
        ∫ u : Fin 6 → ℝ, (‖DW u‖ * m0 u + ‖W u‖ * m1 u) :=
      integral_mono hactual hmajor hpoint
    _ = (∫ u : Fin 6 → ℝ, ‖DW u‖ * m0 u) +
        (∫ u : Fin 6 → ℝ, ‖W u‖ * m1 u) :=
      integral_add hInt1 hInt0
    _ ≤ M1 * E + M0 * E := add_le_add hb1 hb0
    _ = (M1 + M0) * E := by ring

end
end ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1
