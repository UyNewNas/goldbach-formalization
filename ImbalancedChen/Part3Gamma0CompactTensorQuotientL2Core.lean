import ImbalancedChen.Part3Gamma0CompactTensorPoincareC2Core
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual Gamma0-invariant C2 tensor Poincare function descends to the
actual orbit quotient. Its global bound is proved, not supplied: a
nonzero Poincare value gives a nonzero translated seed, placing a true
Gamma0 translate of the point in the explicit compact seed container.
Invariance transfers the value there, and continuity bounds it on that
compact set. The genuine quotient sigma algebra makes the lift measurable.
Finite canonical quotient mass then gives MemLp2 and an actual quotient
L2 vector for every literal finite CompactTensor seed.

No quotient operator, closure, self-adjointness or spectral normalization
is asserted. The whole-plane tensor operator is not relabeled automorphic.
-/

namespace ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a

noncomputable section

open Set MeasureTheory Filter
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a

/-- A nonzero value of the actual Poincare sum has a nonzero literal
translated seed term. No summability supplier is required for this implication. -/
theorem nonzeroPoincare_has_nonzero_seed (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane)
    (hz : finiteCompactTensorPoincare N s T z ≠ 0) :
    ∃ q : effectiveGamma0 N,
      finiteCoreFunction s T (effectiveMatrixAction N q z) ≠ 0 := by
  classical
  by_contra hnot
  have hall : ∀ q : effectiveGamma0 N,
      finiteCoreFunction s T (effectiveMatrixAction N q z) = 0 := by
    intro q
    by_contra hq
    exact hnot ⟨q, hq⟩
  exact hz (by simp [finiteCompactTensorPoincare, hall])

/-- The literal compact seed container meets every orbit on which the
Poincare function is nonzero, and preserves the actual function value. -/
theorem nonzeroPoincare_compact_representative (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane)
    (hz : finiteCompactTensorPoincare N s T z ≠ 0) :
    ∃ k ∈ finiteCompactTensorSupportK s T,
      finiteCompactTensorPoincare N s T k = finiteCompactTensorPoincare N s T z := by
  obtain ⟨q, hq⟩ := nonzeroPoincare_has_nonzero_seed N s T z hz
  refine ⟨effectiveMatrixAction N q z, finiteCoreFunction_support_subset s T hq, ?_⟩
  exact finiteCompactTensorPoincare_gamma0_invariant N s T (effectiveRepresentative N q) z

/-- A global bound proved from actual compact support, continuity and
Gamma0 invariance. Empty seed support is handled by the zero-value case. -/
theorem finiteCompactTensorPoincare_global_bound (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane,
      ‖finiteCompactTensorPoincare N s T z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (finiteCompactTensorSupportK_isCompact s T).bddAbove_image
    (finiteCompactTensorPoincare_continuous N s T).norm.continuousOn
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro z
  by_cases hz : finiteCompactTensorPoincare N s T z = 0
  · simpa [hz] using le_max_right C 0
  · obtain ⟨k, hk, hPk⟩ := nonzeroPoincare_compact_representative N s T z hz
    calc
      ‖finiteCompactTensorPoincare N s T z‖ =
          ‖finiteCompactTensorPoincare N s T k‖ := congrArg norm hPk.symm
      _ ≤ C := hC ⟨k, hk, rfl⟩
      _ ≤ max C 0 := le_max_left C 0

/-- The actual quotient function, obtained by the proved genuine Gamma0
invariance of the new Poincare object on every orbit. -/
def quotientTensorPoincare (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) : Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (finiteCompactTensorPoincare N s T) (by
    intro z w hzw
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp hzw
    rw [← hγ]
    exact finiteCompactTensorPoincare_gamma0_invariant N s T γ w)

@[simp] theorem quotientTensorPoincare_projection (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane) :
    quotientTensorPoincare N s T (orbitProjection N z) =
      finiteCompactTensorPoincare N s T z := rfl

/-- Quotient measurability follows directly from its true sigma algebra,
with no measurable-section or Hausdorff quotient supplier. -/
theorem quotientTensorPoincare_measurable (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    Measurable (quotientTensorPoincare N s T) := by
  apply measurable_from_quotient.mpr
  change Measurable (finiteCompactTensorPoincare N s T)
  exact (finiteCompactTensorPoincare_continuous N s T).measurable

theorem quotientTensorPoincare_global_bound (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Gamma0OrbitSpace N,
      ‖quotientTensorPoincare N s T q‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := finiteCompactTensorPoincare_global_bound N s T
  refine ⟨C, hC, ?_⟩
  intro q
  exact Quotient.inductionOn q (fun z => hbound z)

/-- Membership in L2 for the actual finite canonical quotient measure,
proved from the derived bound rather than assumed as a normalization. -/
theorem quotientTensorPoincare_memLp_two (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    MemLp (quotientTensorPoincare N s T) 2 (carrierPushforward N) := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  obtain ⟨C, _hC, hbound⟩ := quotientTensorPoincare_global_bound N s T
  exact MemLp.of_bound (quotientTensorPoincare_measurable N s T).aestronglyMeasurable C
    (Filter.Eventually.of_forall hbound)

/-- An actual quotient L2 vector from the actual invariant C2 Poincare
family. This is a core family, with no density or operator claim. -/
def quotientTensorPoincareL2 (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) : Lp ℂ 2 (carrierPushforward N) :=
  (quotientTensorPoincare_memLp_two N s T).toLp (quotientTensorPoincare N s T)

/-- The quotient function's actual pullback retains the proved C2 chart
representative, linking this quotient L2 family to the geometric seed core. -/
theorem quotientTensorPoincare_pullback_C2 (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    ContDiffOn ℝ 2
      (extendUpper (fun z => quotientTensorPoincare N s T (orbitProjection N z)))
      positiveChart := by
  simpa only [quotientTensorPoincare_projection] using
    finiteCompactTensorPoincare_contDiffOn_chart N s T

end
end ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
