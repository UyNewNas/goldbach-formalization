import ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1Instantiated
import ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
import ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
import ImbalancedChen.P3HBOriginalGroupCoordinateMixed
import ImbalancedChen.P3HBActualCompleteProductTrim
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-!
P3.6 frozen paper 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2,4(F). Discharge BOTH ordinary measurability
premises of the actual original 729-child first-coordinate Lebesgue L1
result, using the literal occurrence-indexed dyadic group factors and
ONE complete-product smooth trim. The physical scales are not conflated.

The proof derives continuity of each actual coordinate derivative from
its scalar iterated derivative, the true group membership test, and the
finite-product rule. No derivative-valued oracle, L1/Fourier/PP premise,
or new arithmetic axiom is introduced. As before, all-real ContDiff of
eta is a stated internal hypothesis; matching the manuscript's original
half-line eta remains an internal step.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalPhysicalChildrenFirstMeasurable
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBActualCompleteProductTrim
open ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1
open ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1Instantiated
open ImbalancedChen.P3HBSmoothLogTensorRestoration

/-- The ORIGINAL group sum on the entire positional six-coordinate chart
is a finite sum of genuine coordinate projections. -/
theorem originalGroupSum_continuous (J : Finset (Fin 6)) :
    Continuous (originalGroupSum J) := by
  change Continuous (fun u : Fin 6 → ℝ => ∑ j ∈ J, u j)
  exact continuous_finsetSum J (by
    intro j hj
    exact continuous_apply j)

/-- No positive-scale assumption is needed for ordinary smoothness. -/
theorem groupDyadicLogProfile_contDiff (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (c : ℝ) :
    ContDiff ℝ ⊤ (groupDyadicLogProfile chi c) := by
  have he1 : ContDiff ℝ ⊤ (fun t : ℝ => c * Real.exp t) := by fun_prop
  have he2 : ContDiff ℝ ⊤ (fun t : ℝ => 2 * (c * Real.exp t)) := by fun_prop
  change ContDiff ℝ ⊤ (fun t : ℝ =>
    chi (c * Real.exp t) - chi (2 * (c * Real.exp t)))
  exact (hchi.comp he1).sub (hchi.comp he2)

/-- Genuine group factor itself is continuous, including an empty J. -/
theorem originalGroupDyadicFactor_continuous (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (c : ℝ) (J : Finset (Fin 6)) :
    Continuous (originalGroupDyadicFactor chi c J) := by
  change Continuous (fun u : Fin 6 → ℝ =>
    groupDyadicLogProfile chi c (originalGroupSum J u))
  exact (groupDyadicLogProfile_contDiff chi hchi c).continuous.comp
    (originalGroupSum_continuous J)

/-- Continuity of the LITERAL first coordinate derivative, obtained from
the scalar order-1 derivative. Coordinates absent from J give zero. -/
theorem originalGroupDyadicFactor_axisDeriv_continuous
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : ℝ) (J : Finset (Fin 6)) (i : Fin 6) :
    Continuous (fun u : Fin 6 → ℝ =>
      actualAxisDeriv (originalGroupDyadicFactor chi c J) i u) := by
  classical
  have heq (u : Fin 6 → ℝ) :
      actualAxisDeriv (originalGroupDyadicFactor chi c J) i u =
        if i ∈ J then
          iteratedDeriv 1 (groupDyadicLogProfile chi c) (originalGroupSum J u)
        else 0 := by
    have h := originalGroupOrderedDeriv_exact chi c J [i] u
    simpa [originalOrderedAxisDeriv, axesWithinGroup] using h
  have hfun : (fun u : Fin 6 → ℝ =>
        actualAxisDeriv (originalGroupDyadicFactor chi c J) i u) =
      (fun u => if i ∈ J then
        iteratedDeriv 1 (groupDyadicLogProfile chi c) (originalGroupSum J u)
        else 0) := by
    funext u
    exact heq u
  rw [hfun]
  by_cases hi : i ∈ J
  · simpa only [if_pos hi] using
      (((groupDyadicLogProfile_contDiff chi hchi c).continuous_iteratedDeriv
        1 le_top).comp (originalGroupSum_continuous J))
  · simpa only [if_neg hi] using (continuous_const :
      Continuous (fun _ : Fin 6 → ℝ => (0 : ℂ)))

/-- Actual original group OCCURRENCES are never quotiented by identical
subsets or identical positive scales. -/
theorem originalGroupProduct_continuous {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) :
    Continuous (originalGroupProduct chi c J) := by
  change Continuous (fun u : Fin 6 → ℝ =>
    ∏ j : Fin g, originalGroupDyadicFactor chi (c j) (J j) u)
  exact continuous_finsetProd Finset.univ (by
    intro j hj
    exact originalGroupDyadicFactor_continuous chi hchi (c j) (J j))

/-- The true first derivative of the full finite occurrence product is
continuous; we use the source's ACTUAL Leibniz identity, not a new jet. -/
theorem originalGroupProduct_axisDeriv_continuous {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (i : Fin 6) :
    Continuous (fun u : Fin 6 → ℝ =>
      actualAxisDeriv (originalGroupProduct chi c J) i u) := by
  have hformula : (fun u : Fin 6 → ℝ =>
      actualAxisDeriv (originalGroupProduct chi c J) i u) =
      (fun u => ∑ j : Fin g,
        (∏ l ∈ (Finset.univ.erase j),
          originalGroupDyadicFactor chi (c l) (J l) u) *
        actualAxisDeriv (originalGroupDyadicFactor chi (c j) (J j)) i u) := by
    funext u
    exact originalGroupProduct_axisDeriv chi hchi c J u i
  rw [hformula]
  apply continuous_finsetSum Finset.univ
  intro j hj
  apply Continuous.mul
  · exact continuous_finsetProd (Finset.univ.erase j) (by
      intro l hl
      exact originalGroupDyadicFactor_continuous chi hchi (c l) (J l))
  · exact originalGroupDyadicFactor_axisDeriv_continuous
      chi hchi (c j) (J j) i

/-- The SINGLE true trim is continuous, including its upper plateau 1. -/
theorem physicalTrim_continuous (eta : ℝ → ℂ)
    (heta : ContDiff ℝ ⊤ eta) (s : ℝ) :
    Continuous (physicalTrim eta s) := by
  change Continuous (fun u : Fin 6 → ℝ =>
    eta (s * Real.exp (originalGroupSum Finset.univ u)))
  exact heta.continuous.comp
    ((Real.continuous_exp.comp (originalGroupSum_continuous Finset.univ)).const_mul s)

/-- Smoothness of the actual scaled trim's one-dimensional log profile. -/
theorem trimLogProfile_contDiff (eta : ℝ → ℂ)
    (heta : ContDiff ℝ ⊤ eta) (s : ℝ) :
    ContDiff ℝ ⊤ (trimLogProfile eta s) := by
  have he : ContDiff ℝ ⊤ (fun t : ℝ => s * Real.exp t) := by fun_prop
  change ContDiff ℝ ⊤ (fun t : ℝ => eta (s * Real.exp t))
  exact heta.comp he

/-- The actual order-one derivative is continuous on the ENTIRE original
chart, not merely within the narrow trim transition strip. -/
theorem physicalTrim_axisDeriv_continuous (eta : ℝ → ℂ)
    (heta : ContDiff ℝ ⊤ eta) (s : ℝ) (i : Fin 6) :
    Continuous (fun u : Fin 6 → ℝ =>
      actualAxisDeriv (physicalTrim eta s) i u) := by
  have hfun : (fun u : Fin 6 → ℝ =>
        actualAxisDeriv (physicalTrim eta s) i u) =
      (fun u => iteratedDeriv 1 (trimLogProfile eta s)
        (originalGroupSum Finset.univ u)) := by
    funext u
    have h := physicalTrim_orderedDeriv_exact eta s [i] u
    simpa [originalOrderedAxisDeriv] using h
  rw [hfun]
  exact ((trimLogProfile_contDiff eta heta s).continuous_iteratedDeriv
    1 le_top).comp (originalGroupSum_continuous Finset.univ)

/-- Genuine group × ONE full-product trim has the ordinary regularity
needed for the previous Lebesgue L1 theorem. No positivity, Fourier or
arithmetic premise is required merely for measurability. -/
theorem originalGroupPhysicalTrim_continuous {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    Continuous (originalGroupPhysicalTrim chi eta c J s) := by
  change Continuous (fun u : Fin 6 → ℝ =>
    originalGroupProduct chi c J u * physicalTrim eta s u)
  exact (originalGroupProduct_continuous chi hchi c J).mul
    (physicalTrim_continuous eta heta s)

/-- Measurability of the ACTUAL first derivative is a consequence of
continuous literal geometry jets and the old product rule. -/
theorem originalGroupPhysicalTrim_axisDeriv_continuous {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (i : Fin 6) :
    Continuous (fun u : Fin 6 → ℝ =>
      actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u) := by
  have hformula : (fun u : Fin 6 → ℝ =>
      actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u) =
      (fun u =>
        actualAxisDeriv (originalGroupProduct chi c J) i u * physicalTrim eta s u +
        originalGroupProduct chi c J u * actualAxisDeriv (physicalTrim eta s) i u) := by
    funext u
    exact originalGroupPhysicalTrim_axisDeriv chi hchi eta heta c J s u i
  rw [hformula]
  exact ((originalGroupProduct_axisDeriv_continuous chi hchi c J i).mul
    (physicalTrim_continuous eta heta s)).add
    ((originalGroupProduct_continuous chi hchi c J).mul
      (physicalTrim_axisDeriv_continuous eta heta s i))

/-- Integrated literal 729-child first-axis derivative bound, now WITHOUT
the earlier undischarged measurable(W) or measurable(D_i W) hypotheses.
All geometric bounds come from the old actual physical group × trim jets.
This is still only first order on one original six-slot chart, and the
exponential dependence on g remains explicit. -/
theorem physicalChildrenFirstMass_integrable_actual_no_meas
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hchiSmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hchiLarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C) :
    ∃ Cchi Ceta : ℝ, 0 ≤ Cchi ∧ 1 ≤ Ceta ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)),
        (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (orders : Fin 6 → ℕ) (i : Fin 6),
          (∀ j, orders j + 1 ≤ K) →
          Integrable (physicalChildrenFirstMass chi eta c J s orders i) ∧
          (∫ u : Fin 6 → ℝ,
            physicalChildrenFirstMass chi eta c J s orders i u) ≤
            ((2 * ((g : ℝ) + 1) + 1) *
              ((3 * Cchi) ^ g * Ceta)) *
              ((smoothChildren.card : ℝ) *
                ((2 * Real.log 2) * C) ^ 6) := by
  obtain ⟨Cchi, Ceta, hCchi, hCeta, hprior⟩ :=
    physicalChildrenFirstMass_integrable_actual_bounds
      chi eta hchi heta hchiSmall hchiLarge hetaSmall hetaLarge K C hC
  refine ⟨Cchi, Ceta, hCchi, hCeta, ?_⟩
  intro g c J hc s hs orders i hk
  exact hprior g c J hc s hs orders i hk
    (originalGroupPhysicalTrim_continuous chi eta hchi heta c J s).measurable
    (originalGroupPhysicalTrim_axisDeriv_continuous
      chi eta hchi heta c J s i).measurable

end
end ImbalancedChen.P3HBOriginalPhysicalChildrenFirstMeasurable
