import ImbalancedChen.P3HBOriginalGroupTrimAllOrder
import ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
import ImbalancedChen.P3HBActualCompleteProductTrimUniform
import Mathlib.Tactic

/-!
P3.6, original occurrence-indexed grouped dyadic product times ONE literal
physical complete-product trim: a finite-order quantitative pointwise budget.

Paper pin: UyNewNas/chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
sections 2 and 4(F).

This is not a new geometry or distribution assumption. It composes true
ordered-derivative candidate identities with the original group-allocation
mass and the actual complete-product trim derivative budget. Physical group
scales and the complete-product scale remain independent and positive;
repeated axes and repeated group occurrences are not identified.

The factor 2^k (g+1)^k (3*Cchi)^g Ceta is explicit. It does NOT prove the
T,m(T)-uniform integrated derivative budget, the U5/HB-hat assembly, Fourier
truncation or same-integer-rho PP. It also does not establish that the
real-complex smooth eta extension matches the manuscript's half-line eta.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalGroupTrimPointwiseBudget
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupFinCons
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupTrimAllOrder
open ImbalancedChen.P3HBActualCompleteProductTrim
open ImbalancedChen.P3HBActualCompleteProductTrimUniform
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst

/-- Fixed-order bound on the TRUE binary allocation mass of the original
group-occurrence product and the single physical trim. Every derivative
occurrence is assigned to exactly one of these two factors. Neither
physical scale is absorbed into the bound; g-dependence stays explicit.

In particular g=0 is retained, and the term (g+1)^k is used instead of
implicitly assuming g^0 or a positive number of original groups. -/
theorem binaryMass_uniform_finite_order
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hchiSmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hchiLarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ Cchi Ceta : ℝ, 0 ≤ Cchi ∧ 1 ≤ Ceta ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (u : Fin 6 → ℝ),
          binaryMass chi eta c J s axes u ≤
            (2 : ℝ) ^ k * ((g : ℝ) + 1) ^ k *
              (3 * Cchi) ^ g * Ceta := by
  classical
  obtain ⟨Cchi, hCchi, hmass⟩ :=
    allocationMass_le_fixed_order chi hchi hchiSmall hchiLarge K
  obtain ⟨Ceta, hCeta, htrim⟩ :=
    physicalTrim_uniform_ordered_jets eta heta hetaSmall hetaLarge K
  refine ⟨Cchi, Ceta, hCchi, hCeta, ?_⟩
  intro g k c J hc s hs axes hk u
  have hpow : 0 ≤ (3 * Cchi) ^ g := by
    positivity
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
  have hgplus : 1 ≤ (g : ℝ) + 1 := by linarith
  have hcoef : 0 ≤ ((g : ℝ) + 1) ^ k * (3 * Cchi) ^ g := by
    positivity
  have hterm (owner : Fin k → Fin 2) :
      ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupProduct chi c J) u‖ *
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 1)
          (physicalTrim eta s) u‖ ≤
          (((g : ℝ) + 1) ^ k * (3 * Cchi) ^ g) * Ceta := by
    let groupAxes : Fin (axesAssigned axes owner 0).length → Fin 6 :=
      fun r => (axesAssigned axes owner 0).get r
    have hlist : List.ofFn groupAxes = axesAssigned axes owner 0 := by
      simp [groupAxes]
    have hlen : (axesAssigned axes owner 0).length ≤ k :=
      axesAssigned_length_le axes owner 0
    have hgroupBase :
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
            (originalGroupProduct chi c J) u‖ ≤
          (g : ℝ) ^ (axesAssigned axes owner 0).length *
            (3 * Cchi) ^ g := by
      have hactual :=
        originalGroupProduct_ordered_norm_le_mass
          chi hchi c J groupAxes u
      have hallocated :=
        hmass g (axesAssigned axes owner 0).length c J hc
          groupAxes (hlen.trans hk) u
      simpa only [hlist] using hactual.trans hallocated
    have hpower :
        (g : ℝ) ^ (axesAssigned axes owner 0).length ≤
          ((g : ℝ) + 1) ^ k := by
      calc
        (g : ℝ) ^ (axesAssigned axes owner 0).length ≤
            ((g : ℝ) + 1) ^ (axesAssigned axes owner 0).length := by
          gcongr
          <;> linarith
        _ ≤ ((g : ℝ) + 1) ^ k :=
          pow_le_pow_right₀ hgplus hlen
    have hgroup :
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
            (originalGroupProduct chi c J) u‖ ≤
          ((g : ℝ) + 1) ^ k * (3 * Cchi) ^ g :=
      hgroupBase.trans (mul_le_mul_of_nonneg_right hpower hpow)
    have htrimJet :
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 1)
            (physicalTrim eta s) u‖ ≤ Ceta :=
      htrim s hs (axesAssigned axes owner 1)
        ((axesAssigned_length_le axes owner 1).trans hk) u
    exact mul_le_mul hgroup htrimJet (norm_nonneg _) hcoef
  have hcount : (Fintype.card (Fin k → Fin 2) : ℝ) = (2 : ℝ) ^ k := by
    exact_mod_cast allocation_card 2 k
  unfold binaryMass
  calc
    (∑ owner : Fin k → Fin 2,
      ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupProduct chi c J) u‖ *
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 1)
          (physicalTrim eta s) u‖)
        ≤ ∑ _owner : Fin k → Fin 2,
            (((g : ℝ) + 1) ^ k * (3 * Cchi) ^ g) * Ceta := by
          apply Finset.sum_le_sum
          intro owner ho
          exact hterm owner
    _ = (2 : ℝ) ^ k *
          ((((g : ℝ) + 1) ^ k * (3 * Cchi) ^ g) * Ceta) := by
        simp [Finset.sum_const, nsmul_eq_mul, hcount]
    _ = (2 : ℝ) ^ k * ((g : ℝ) + 1) ^ k *
          (3 * Cchi) ^ g * Ceta := by ring

/-- The genuine repeated ordered coordinate derivative of the literal
group-occurrence product times the ONE complete-product trim inherits the
pointwise quantitative ceiling. This corollary depends on the previously
constructed actual all-order binary Leibniz identity, not a derivative
oracle or a distribution theorem. -/
theorem originalGroupPhysicalTrim_ordered_uniform_finite_order
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hchiSmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hchiLarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ Cchi Ceta : ℝ, 0 ≤ Cchi ∧ 1 ≤ Ceta ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (u : Fin 6 → ℝ),
          ‖originalOrderedAxisDeriv (List.ofFn axes)
              (originalGroupPhysicalTrim chi eta c J s) u‖ ≤
            (2 : ℝ) ^ k * ((g : ℝ) + 1) ^ k *
              (3 * Cchi) ^ g * Ceta := by
  obtain ⟨Cchi, Ceta, hCchi, hCeta, hbound⟩ :=
    binaryMass_uniform_finite_order chi eta hchi heta
      hchiSmall hchiLarge hetaSmall hetaLarge K
  refine ⟨Cchi, Ceta, hCchi, hCeta, ?_⟩
  intro g k c J hc s hs axes hk u
  exact (originalGroupPhysicalTrim_ordered_norm_le_binaryMass
    chi eta hchi heta c J s axes u).trans
    (hbound g k c J hc s hs axes hk u)

end
end ImbalancedChen.P3HBOriginalGroupTrimPointwiseBudget
