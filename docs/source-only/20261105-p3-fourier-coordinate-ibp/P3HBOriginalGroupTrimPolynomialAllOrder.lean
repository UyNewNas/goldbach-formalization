import ImbalancedChen.P3HBOriginalGroupPolynomialAllOrder
import ImbalancedChen.P3HBOriginalGroupTrimAllOrder
import ImbalancedChen.P3HBActualCompleteProductTrimUniform
import Mathlib.Tactic

/-!
P3.6: polynomial-in-g fixed-order bound for the ACTUAL original dyadic
occurrence-group product times ONE literal complete-physical-product trim.

Frozen manuscript UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 (smooth dyadic geometry) and §4 (F).

The crucial hypothesis hpsi is the genuine original nonnegative
partition's contraction bound; it is not inferred from arbitrary complex
cutoff plateau values. For g original group occurrences the earlier
all-order group jet bound is g^l B^l, not (3C)^g. We distribute EVERY
coordinate derivative occurrence (including repetitions) between that
full group product and the ONE complete-product trim. Each partial word
has length <= k. The group jet is bounded by ((g+1)B)^k and the trim jet
by Ceta. Summing all 2^k binary allocations gives a polynomial bound
at fixed k, with Ceta and B chosen BEFORE g, physical scales, labels,
axis words and evaluation points.

This is NOT complete W_T with U5 and HB hats, an integrated mixed L1
budget, uniformity in growing derivative order, Fourier/PP or the same-rho
arithmetic discrepancy. All statements are SOURCE_ONLY, uncompiled and
kernel-unverified. Locked Lean v4.33.0-rc1; Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalGroupTrimPolynomialAllOrder
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupFinCons
open ImbalancedChen.P3HBOriginalGroupPolynomialAllOrder
open ImbalancedChen.P3HBOriginalGroupTrimAllOrder
open ImbalancedChen.P3HBActualCompleteProductTrim
open ImbalancedChen.P3HBActualCompleteProductTrimUniform
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst

/-- TRUE binary-allocation mass: the original g-fold group product has
polynomial fixed-order jets under the actual dyadic contraction hpsi;
there is one independently scaled full-product trim. The constants are
chosen uniformly in g and all physical scales. -/
theorem binaryMass_polynomial_finite_order
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ B Ceta : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (u : Fin 6 → ℝ),
          binaryMass chi eta c J s axes u ≤
            (2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta := by
  classical
  obtain ⟨B, hB, hgroup⟩ :=
    originalGroupProduct_ordered_polynomial
      chi hchi hsmall hlarge hpsi K
  obtain ⟨Ceta, hCeta, htrim⟩ :=
    physicalTrim_uniform_ordered_jets
      eta heta hetaSmall hetaLarge K
  refine ⟨B, Ceta, hB, hCeta, ?_⟩
  intro g k c J hc s hs axes hk u
  let A : ℝ := ((g : ℝ) + 1) * B
  have hAone : 1 ≤ A := by
    dsimp [A]
    have hg : (1 : ℝ) ≤ (g : ℝ) + 1 := by
      have hg0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
      linarith
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((g : ℝ) + 1) * B :=
        mul_le_mul hg hB (by norm_num) (by positivity)
  have hgb_le : (g : ℝ) * B ≤ A := by
    dsimp [A]
    apply mul_le_mul_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ B)
    linarith
  have hterm (owner : Fin k → Fin 2) :
      ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupProduct chi c J) u‖ *
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 1)
          (physicalTrim eta s) u‖ ≤ A ^ k * Ceta := by
    let subAxes : Fin (axesAssigned axes owner 0).length → Fin 6 :=
      fun r => (axesAssigned axes owner 0).get r
    have hlist : List.ofFn subAxes = axesAssigned axes owner 0 := by
      simp [subAxes]
    have hlen : (axesAssigned axes owner 0).length ≤ k :=
      axesAssigned_length_le axes owner 0
    have hgroupJet :
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
            (originalGroupProduct chi c J) u‖ ≤
          (g : ℝ) ^ (axesAssigned axes owner 0).length *
            B ^ (axesAssigned axes owner 0).length := by
      simpa only [hlist] using
        (hgroup g (axesAssigned axes owner 0).length c J hc
          subAxes (hlen.trans hk) u)
    have hgroupA :
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
            (originalGroupProduct chi c J) u‖ ≤ A ^ k := by
      calc
        _ ≤ (g : ℝ) ^ (axesAssigned axes owner 0).length *
            B ^ (axesAssigned axes owner 0).length := hgroupJet
        _ = ((g : ℝ) * B) ^ (axesAssigned axes owner 0).length :=
          (mul_pow _ _ _).symm
        _ ≤ A ^ (axesAssigned axes owner 0).length := by
          gcongr <;> exact hgb_le
        _ ≤ A ^ k := pow_le_pow_right₀ hAone hlen
    have htrimJet :
        ‖originalOrderedAxisDeriv (axesAssigned axes owner 1)
            (physicalTrim eta s) u‖ ≤ Ceta :=
      htrim s hs (axesAssigned axes owner 1)
        ((axesAssigned_length_le axes owner 1).trans hk) u
    exact mul_le_mul hgroupA htrimJet (norm_nonneg _) (by positivity)
  have hcard : (Fintype.card (Fin k → Fin 2) : ℝ) = (2 : ℝ) ^ k := by
    exact_mod_cast allocation_card 2 k
  unfold binaryMass
  calc
    (∑ owner : Fin k → Fin 2,
      ‖originalOrderedAxisDeriv (axesAssigned axes owner 0)
        (originalGroupProduct chi c J) u‖ *
      ‖originalOrderedAxisDeriv (axesAssigned axes owner 1)
        (physicalTrim eta s) u‖) ≤
        ∑ _owner : Fin k → Fin 2, A ^ k * Ceta := by
          apply Finset.sum_le_sum
          intro owner ho
          exact hterm owner
    _ = (2 : ℝ) ^ k * (A ^ k * Ceta) := by
          simp [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = (2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta := by
          dsimp [A]
          ring

/-- The ACTUAL iterated coordinate derivative of grouped physical trim,
not an arbitrary jet field, inherits the polynomial bound via the
already stated exact two-owner Leibniz identity. -/
theorem originalGroupPhysicalTrim_ordered_polynomial
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ B Ceta : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (u : Fin 6 → ℝ),
          ‖originalOrderedAxisDeriv (List.ofFn axes)
              (originalGroupPhysicalTrim chi eta c J s) u‖ ≤
            (2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta := by
  obtain ⟨B, Ceta, hB, hCeta, hmass⟩ :=
    binaryMass_polynomial_finite_order chi eta hchi heta
      hsmall hlarge hpsi hetaSmall hetaLarge K
  refine ⟨B, Ceta, hB, hCeta, ?_⟩
  intro g k c J hc s hs axes hk u
  exact (originalGroupPhysicalTrim_ordered_norm_le_binaryMass
    chi eta hchi heta c J s axes u).trans
    (hmass g k c J hc s hs axes hk u)

end
end ImbalancedChen.P3HBOriginalGroupTrimPolynomialAllOrder
