import ImbalancedChen.P3HBOriginalPhysicalChildrenFirstMeasurable
import ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
import ImbalancedChen.P3HBActualCompleteProductTrimUniform
import Mathlib.Tactic

/-!
P3.6: first-axis original 729-child L1 with POLYNOMIAL instead of
exponential dependence on the number of literal original dyadic groups.

Frozen source: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 (nonnegative smooth dyadic partition) and §4(F).

The manuscript's chosen nonnegative partition has 0 <= psi <= 1.
In this conditional source theorem the *exact* required profile bound is
kept explicit: for all t, norm(chi t - chi (2*t)) <= 1.
The two chi plateau assumptions ALONE do not imply this bound for an
arbitrary complex-valued cutoff. Admitting the actual partition profile
and its bound remains an INTERNAL, not external, proof obligation.

The original 6 positions, all g group OCCURRENCES (including duplicates),
independent positive c_j, ONE physical complete-product trim s, and all
729 ordered HB child labels are preserved. We use actual coordinate
derivatives and actual 6D Lebesgue integrals, not freely prescribed jets.
The resulting factor is linear in g at first order, not (3*Cchi)^g.
It does NOT establish high-order 2S, uniform full W_T, Fourier tail, or PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalPhysicalChildrenFirstPolynomial
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBActualCompleteProductTrimUniform
open ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1
open ImbalancedChen.P3HBOriginalPhysicalChildrenFirstMeasurable
open ImbalancedChen.P3HBSmoothLogTensorRestoration

/-- The actual original group factor is contractive if and only if
the chosen dyadic partition profile satisfies the stated bound at its
true physical argument. No group scale is dropped. -/
theorem originalGroupFactor_norm_le_one
    (chi : ℝ → ℂ)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (c : ℝ) (J : Finset (Fin 6)) (u : Fin 6 → ℝ) :
    ‖originalGroupDyadicFactor chi c J u‖ ≤ 1 := by
  change ‖chi (c * Real.exp (originalGroupSum J u)) -
      chi (2 * (c * Real.exp (originalGroupSum J u)))‖ ≤ 1
  exact hpsi _

/-- The whole original occurrence-indexed group product has norm <= 1.
Repeated occurrences are retained; the empty product has norm exactly 1. -/
theorem originalGroupProduct_norm_le_one {g : ℕ}
    (chi : ℝ → ℂ)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) :
    ‖originalGroupProduct chi c J u‖ ≤ 1 := by
  classical
  unfold originalGroupProduct
  rw [norm_prod]
  calc
    (∏ j : Fin g, ‖originalGroupDyadicFactor chi (c j) (J j) u‖)
        ≤ ∏ _j : Fin g, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro j hj
            exact norm_nonneg _
          · intro j hj
            exact originalGroupFactor_norm_le_one chi hpsi (c j) (J j) u
    _ = 1 := by simp

/-- Under the actual nonnegative-partition amplitude bound,
a single group derivative costs one constant and the remaining
(g-1) undifferentiated factors cost at most one, not a power of g.
The conclusion is for the TRUE coordinate derivative of the full product. -/
theorem originalGroupProduct_axisDeriv_linear {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (Cchi : ℝ) (hCchi : 0 ≤ Cchi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6)
    (hjet : ∀ j : Fin g,
      ‖actualAxisDeriv
        (originalGroupDyadicFactor chi (c j) (J j)) i u‖ ≤ Cchi) :
    ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ ≤
      (g : ℝ) * Cchi := by
  classical
  have hterm (j : Fin g) :
      (∏ l ∈ (Finset.univ.erase j),
        ‖originalGroupDyadicFactor chi (c l) (J l) u‖) *
        ‖actualAxisDeriv
          (originalGroupDyadicFactor chi (c j) (J j)) i u‖ ≤ Cchi := by
    have hp :
        (∏ l ∈ (Finset.univ.erase j),
          ‖originalGroupDyadicFactor chi (c l) (J l) u‖) ≤ 1 := by
      calc
        (∏ l ∈ (Finset.univ.erase j),
          ‖originalGroupDyadicFactor chi (c l) (J l) u‖)
          ≤ ∏ _l ∈ (Finset.univ.erase j), (1 : ℝ) := by
            apply Finset.prod_le_prod
            · intro l hl
              exact norm_nonneg _
            · intro l hl
              exact originalGroupFactor_norm_le_one chi hpsi (c l) (J l) u
        _ = 1 := by simp
    calc
      (∏ l ∈ (Finset.univ.erase j),
        ‖originalGroupDyadicFactor chi (c l) (J l) u‖) *
          ‖actualAxisDeriv
            (originalGroupDyadicFactor chi (c j) (J j)) i u‖
        ≤ 1 * Cchi := mul_le_mul hp (hjet j) (norm_nonneg _) (by norm_num)
      _ = Cchi := one_mul _
  calc
    ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖
      ≤ originalGroupAxisMass chi c J u i :=
        originalGroupProduct_axisDeriv_norm_le chi hchi c J u i
    _ ≤ ∑ _j : Fin g, Cchi := by
      unfold originalGroupAxisMass
      apply Finset.sum_le_sum
      intro j hj
      exact hterm j
    _ = (g : ℝ) * Cchi := by simp [nsmul_eq_mul]

/-- The exact 729-child FIRST-axis mass has an L1 bound linear in the
number g of original dyadic group occurrences, provided the chosen
partition profile really is norm-bounded by one.

The fixed chi,eta and K,C occur BEFORE g, the physical scales, all
729 labels, the derivative orders and the evaluation point.
The remaining eta whole-real smooth extension and actual hpsi discharge
are manuscript-INTERNAL obligations. -/
theorem physicalChildrenFirstMass_integrable_polynomial
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hchiSmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hchiLarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
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
            (((g : ℝ) * (3 * Cchi) + 2) * Ceta) *
              ((smoothChildren.card : ℝ) *
                ((2 * Real.log 2) * C) ^ 6) := by
  obtain ⟨Cchi, hCchi, hgroup⟩ :=
    originalGroupOrderedDeriv_uniform_scale chi hchi hchiSmall hchiLarge 1
  obtain ⟨Ceta, hCeta, htrim⟩ :=
    physicalTrim_uniform_ordered_jets eta heta hetaSmall hetaLarge 1
  refine ⟨Cchi, Ceta, hCchi, hCeta, ?_⟩
  intro g c J hc s hs orders i hk
  have hG0 (u : Fin 6 → ℝ) :
      ‖originalGroupProduct chi c J u‖ ≤ 1 :=
    originalGroupProduct_norm_le_one chi hpsi c J u
  have hG1 (u : Fin 6 → ℝ) :
      ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ ≤
        (g : ℝ) * (3 * Cchi) := by
    apply originalGroupProduct_axisDeriv_linear chi hchi hpsi
      (3 * Cchi) (mul_nonneg (by norm_num) hCchi) c J u i
    intro j
    have h := hgroup (c j) (hc j) (J j) [i] (by simp) u
    simpa only [originalOrderedAxisDeriv] using h
  have hT0 (u : Fin 6 → ℝ) :
      ‖physicalTrim eta s u‖ ≤ Ceta := by
    simpa only [originalOrderedAxisDeriv] using
      (htrim s hs ([] : List (Fin 6)) (by simp) u)
  have hT1 (u : Fin 6 → ℝ) :
      ‖actualAxisDeriv (physicalTrim eta s) i u‖ ≤ Ceta := by
    simpa only [originalOrderedAxisDeriv] using
      (htrim s hs [i] (by simp) u)
  have hM0 : 0 ≤ Ceta := (by norm_num : (0 : ℝ) ≤ 1).trans hCeta
  have hM1 : 0 ≤ ((g : ℝ) * (3 * Cchi) + 1) * Ceta := by positivity
  have hW0 (u : Fin 6 → ℝ) :
      ‖originalGroupPhysicalTrim chi eta c J s u‖ ≤ Ceta := by
    change ‖originalGroupProduct chi c J u * physicalTrim eta s u‖ ≤ Ceta
    rw [norm_mul]
    calc
      ‖originalGroupProduct chi c J u‖ * ‖physicalTrim eta s u‖
        ≤ 1 * Ceta :=
          mul_le_mul (hG0 u) (hT0 u) (norm_nonneg _) (by norm_num)
      _ = Ceta := one_mul _
  have hW1 (u : Fin 6 → ℝ) :
      ‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖ ≤
        ((g : ℝ) * (3 * Cchi) + 1) * Ceta := by
    calc
      ‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖
        ≤ ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ *
            ‖physicalTrim eta s u‖ +
          ‖originalGroupProduct chi c J u‖ *
            ‖actualAxisDeriv (physicalTrim eta s) i u‖ :=
          originalGroupPhysicalTrim_axisDeriv_norm_le
            chi hchi eta heta c J s u i
      _ ≤ ((g : ℝ) * (3 * Cchi)) * Ceta + 1 * Ceta := by
        apply add_le_add
        · exact mul_le_mul (hG1 u) (hT0 u)
            (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hG0 u) (hT1 u)
            (norm_nonneg _) (by norm_num)
      _ = ((g : ℝ) * (3 * Cchi) + 1) * Ceta := by ring
  obtain ⟨hint, hL1⟩ :=
    physicalChildrenFirstMass_integrable_and_L1_le
      chi eta hchi heta hchiSmall hchiLarge K C hC
      c J s orders i hk
      (originalGroupPhysicalTrim_continuous chi eta hchi heta c J s).measurable
      (originalGroupPhysicalTrim_axisDeriv_continuous
        chi eta hchi heta c J s i).measurable
      Ceta (((g : ℝ) * (3 * Cchi) + 1) * Ceta)
      hM0 hM1 hW0 hW1
  refine ⟨hint, ?_⟩
  calc
    (∫ u : Fin 6 → ℝ,
      physicalChildrenFirstMass chi eta c J s orders i u) ≤
        ((((g : ℝ) * (3 * Cchi) + 1) * Ceta) + Ceta) *
          ((smoothChildren.card : ℝ) *
            ((2 * Real.log 2) * C) ^ 6) := hL1
    _ = (((g : ℝ) * (3 * Cchi) + 2) * Ceta) *
          ((smoothChildren.card : ℝ) *
            ((2 * Real.log 2) * C) ^ 6) := by ring

end
end ImbalancedChen.P3HBOriginalPhysicalChildrenFirstPolynomial
