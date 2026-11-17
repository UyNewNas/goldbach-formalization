import ImbalancedChen.P3HBOriginalGroupAllOrderShiftedSupport
import ImbalancedChen.P3HBActualCompleteProductTrimUniform
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
P3.6 — ACTUAL first coordinate derivative and quantitative scale-uniform
budget of the product of ALL original occurrence-indexed dyadic groups and
the SINGLE full physical product trim.

Frozen manuscript UyNewNas/chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 (complete-product eta) and §4 (F) (original grouped psi).

This is an actual product, not a new freely specified jet family. All
group occurrences, positive independent chart scales and the complete
product trim scale are preserved. The zero-th order trim may equal ONE
on its upper plateau. The constants below are independent of all positive
scales, but the factor g*(3*Cchi)^g is NOT uniform in an arbitrarily
growing number of groups. No U5, HB hats, full 2S, Fourier tail or same-rho
physical modulus discrepancy is settled by this first-order result.

Pinned Lean v4.33.0-rc1, Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalGroupFinCons
open ImbalancedChen.P3HBOriginalGroupAllOrderShiftedSupport
open ImbalancedChen.P3HBActualCompleteProductTrim
open ImbalancedChen.P3HBActualCompleteProductTrimUniform

/-- The literal combination after the manuscript's smooth full-product
trim. Group j is an occurrence, not a distinct set of coordinates. -/
def originalGroupPhysicalTrim {g : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (u : Fin 6 → ℝ) : ℂ :=
  originalGroupProduct chi c J u * physicalTrim eta s u

/-- Genuine coordinate differentiability of the whole group product.
This is proved from the actual finite product and smooth factors. -/
theorem originalGroupProduct_slice_differentiable {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ
      (fun t : ℝ => originalGroupProduct chi c J (Function.update u i t))
      (u i) := by
  classical
  change DifferentiableAt ℝ
    (fun t : ℝ => ∏ j : Fin g,
      originalGroupDyadicFactor chi (c j) (J j) (Function.update u i t)) (u i)
  exact DifferentiableAt.fun_finsetProd
    (u := (Finset.univ : Finset (Fin g)))
    (f := fun j t => originalGroupDyadicFactor chi (c j) (J j)
      (Function.update u i t))
    (x := u i) (by
      intro j hj
      exact originalGroupFactor_slice_differentiable
        chi hchi (c j) (J j) u i)

/-- Genuine coordinate differentiability of the single COMPLETE-product
trim, from the same fixed C-infinity eta and the sum of all six slots. -/
theorem physicalTrim_slice_differentiable
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (s : ℝ) (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ
      (fun t : ℝ => physicalTrim eta s (Function.update u i t)) (u i) := by
  have hsum : Differentiable ℝ
      (fun t : ℝ =>
        originalGroupSum Finset.univ (Function.update u i t)) :=
    groupSum_slice_differentiable Finset.univ u i
  have hexp : Differentiable ℝ
      (fun t : ℝ =>
        s * Real.exp
          (originalGroupSum Finset.univ (Function.update u i t))) :=
    (Real.differentiable_exp.comp hsum).const_mul s
  change DifferentiableAt ℝ
    (fun t : ℝ => eta
      (s * Real.exp
        (originalGroupSum Finset.univ (Function.update u i t)))) (u i)
  exact ((heta.differentiable (by norm_num)).comp hexp).differentiableAt

/-- Actual Leibniz derivative, not a separately supplied derivative or
allocation field. In particular the SECOND term survives when eta is
on its upper plateau; it is not dropped by a false compact-support
claim about the zero-th trim. -/
theorem originalGroupPhysicalTrim_axisDeriv {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u =
      actualAxisDeriv (originalGroupProduct chi c J) i u *
        physicalTrim eta s u +
      originalGroupProduct chi c J u *
        actualAxisDeriv (physicalTrim eta s) i u := by
  have hG :=
    originalGroupProduct_slice_differentiable chi hchi c J u i
  have hT := physicalTrim_slice_differentiable eta heta s u i
  have hu : Function.update u i (u i) = u := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_noteq hj]
  change deriv
    (fun t : ℝ =>
      originalGroupProduct chi c J (Function.update u i t) *
      physicalTrim eta s (Function.update u i t)) (u i) = _
  simpa only [actualAxisDeriv, hu] using
    (hG.hasDerivAt.mul hT.hasDerivAt).deriv

/-- The genuine derivative has the exact nonnegative two-factor
majorant, with no independence assumption on the overlapping six
physical coordinates. -/
theorem originalGroupPhysicalTrim_axisDeriv_norm_le {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) (i : Fin 6) :
    ‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖ ≤
      ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ *
        ‖physicalTrim eta s u‖ +
      ‖originalGroupProduct chi c J u‖ *
        ‖actualAxisDeriv (physicalTrim eta s) i u‖ := by
  rw [originalGroupPhysicalTrim_axisDeriv chi hchi eta heta c J s u i]
  simpa only [norm_mul] using
    (norm_add_le
      (actualAxisDeriv (originalGroupProduct chi c J) i u *
        physicalTrim eta s u)
      (originalGroupProduct chi c J u *
        actualAxisDeriv (physicalTrim eta s) i u))

/-- ONE common pair of fixed-smoothing constants simultaneously bounds
the actual first coordinate derivative for all physical group and trim
scales. Its g dependence is exposed and is not misreported as a fixed
power of log T when g is allowed to grow. -/
theorem originalGroupPhysicalTrim_axisDeriv_uniform
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hchiSmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hchiLarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1) :
    ∃ Cchi Ceta : ℝ, 0 ≤ Cchi ∧ 1 ≤ Ceta ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
          ∀ (u : Fin 6 → ℝ) (i : Fin 6),
            ‖actualAxisDeriv
                (originalGroupPhysicalTrim chi eta c J s) i u‖ ≤
              ((g : ℝ) + 1) * (3 * Cchi) ^ g * Ceta := by
  obtain ⟨Cchi, hCchi, hmass⟩ :=
    allocationMass_le_fixed_order chi hchi hchiSmall hchiLarge 1
  obtain ⟨Ceta, hCeta, htrim⟩ :=
    physicalTrim_uniform_ordered_jets eta heta hetaSmall hetaLarge 1
  refine ⟨Cchi, Ceta, hCchi, hCeta, ?_⟩
  intro g c J hc s hs u i
  have hG0 : ‖originalGroupProduct chi c J u‖ ≤ (3 * Cchi) ^ g := by
    let a : Fin 0 → Fin 6 := fun r => Fin.elim0 r
    have h1 := originalGroupProduct_ordered_norm_le_mass chi hchi c J a u
    have h2 := hmass g 0 c J hc a (by omega) u
    simpa [a, originalOrderedAxisDeriv] using (h1.trans h2)
  have hG1 :
      ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ ≤
        (g : ℝ) * (3 * Cchi) ^ g := by
    let a : Fin 1 → Fin 6 := fun _ => i
    have h1 := originalGroupProduct_ordered_norm_le_mass chi hchi c J a u
    have h2 := hmass g 1 c J hc a (by omega) u
    simpa [a, originalOrderedAxisDeriv] using (h1.trans h2)
  have hT0 : ‖physicalTrim eta s u‖ ≤ Ceta := by
    simpa only [originalOrderedAxisDeriv] using
      (htrim s hs ([] : List (Fin 6)) (by simp) u)
  have hT1 :
      ‖actualAxisDeriv (physicalTrim eta s) i u‖ ≤ Ceta := by
    simpa only [originalOrderedAxisDeriv] using
      (htrim s hs [i] (by simp) u)
  have hpow : 0 ≤ (3 * Cchi) ^ g :=
    pow_nonneg (mul_nonneg (by norm_num) hCchi) _
  have hfirst : 0 ≤ (g : ℝ) * (3 * Cchi) ^ g :=
    mul_nonneg (Nat.cast_nonneg _) hpow
  calc
    ‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖
        ≤ ‖actualAxisDeriv (originalGroupProduct chi c J) i u‖ *
            ‖physicalTrim eta s u‖ +
          ‖originalGroupProduct chi c J u‖ *
            ‖actualAxisDeriv (physicalTrim eta s) i u‖ :=
      originalGroupPhysicalTrim_axisDeriv_norm_le
        chi hchi eta heta c J s u i
    _ ≤ ((g : ℝ) * (3 * Cchi) ^ g) * Ceta +
          (3 * Cchi) ^ g * Ceta := by
      apply add_le_add
      · exact mul_le_mul hG1 hT0 (norm_nonneg _) hfirst
      · exact mul_le_mul hG0 hT1 (norm_nonneg _) hpow
    _ = ((g : ℝ) + 1) * (3 * Cchi) ^ g * Ceta := by ring

/-- Multiplication by the FULL physical trim does not enlarge an original
group's shifted-strip support for the true FIRST coordinate derivative.
This uses both the order-0 and order-1 full-group derivative vanishing;
no claim that eta itself vanishes on the upper plateau. -/
theorem originalGroupPhysicalTrim_axisDeriv_zero_outside_group {g : ℕ}
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hchiSmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hchiLarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (hc : ∀ j, 0 < c j)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (u : Fin 6 → ℝ) (i : Fin 6) (j : Fin g)
    (hout : originalGroupSum (J j) u + Real.log (c j) ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u = 0 := by
  have hz0 :
      originalGroupProduct chi c J u = 0 := by
    have hz := originalGroupProduct_ordered_zero_outside_any_group
      chi hchi hchiSmall hchiLarge c hc J
      (fun r : Fin 0 => Fin.elim0 r) u j hout
    simpa [originalOrderedAxisDeriv] using hz
  have hz1 :
      actualAxisDeriv (originalGroupProduct chi c J) i u = 0 := by
    have hz := originalGroupProduct_ordered_zero_outside_any_group
      chi hchi hchiSmall hchiLarge c hc J
      (fun _ : Fin 1 => i) u j hout
    simpa [originalOrderedAxisDeriv] using hz
  rw [originalGroupPhysicalTrim_axisDeriv chi hchi eta heta c J s u i,
    hz0, hz1]
  simp

end
end ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
