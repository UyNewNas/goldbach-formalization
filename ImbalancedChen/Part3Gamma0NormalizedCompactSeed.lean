import ImbalancedChen.Part3Gamma0CompactSeedQuotientL2Budget
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A compact-seed reconstruction bridge for the actual effective Gamma0 action.
The denominator is a genuine locally finite Poincare series of a nonnegative
compactly supported real bump. Positivity is derived from an actual orbit
meeting a compact carrier on which that bump is positive. The normalized
compact seed reconstructs the original invariant function exactly.

This does not assume or prove membership of an arbitrary smooth compact
quotient function in the finite smooth-tensor core. Choosing the bump and
proving finite-jet approximation remain separate constructive inputs.
-/

namespace ImbalancedChen.Part3.Gamma0NormalizedCompactSeed20261025a

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open Gamma0EffectiveActionKernel20261024z
open Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0CompactSeedQuotientL2Budget20261025a

/-- Actual effective-group periodization, with central signs counted once. -/
def bumpTrace (N : ℕ) (b : UpperHalfPlane → ℝ) (z : UpperHalfPlane) : ℝ :=
  ∑' q : effectiveGamma0 N, b (effectiveMatrixAction N q z)

/-- Proper-action compact hits supply summability before any tsum algebra. -/
theorem bumpTrace_summable (N : ℕ) (b : UpperHalfPlane → ℝ)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hbK : Function.support b ⊆ K) (z : UpperHalfPlane) :
    Summable (fun q : effectiveGamma0 N => b (effectiveMatrixAction N q z)) := by
  have hcast : Function.support (fun w => (b w : ℂ)) ⊆ K := by
    intro w hw
    apply hbK
    intro hzero
    exact hw (by simp [hzero])
  obtain ⟨U, hU, S, hS⟩ := compact_seed_locally_finite N
    (fun w => (b w : ℂ)) hK hcast z
  apply summable_of_ne_finset_zero (s := S)
  intro q hq
  exact Complex.ofReal_eq_zero.mp (hS z (mem_of_mem_nhds hU) q hq)

/-- Right multiplication is a true permutation of the effective group. -/
theorem bumpTrace_action (N : ℕ) (b : UpperHalfPlane → ℝ)
    (r : effectiveGamma0 N) (z : UpperHalfPlane) :
    bumpTrace N b (effectiveMatrixAction N r z) = bumpTrace N b z := by
  unfold bumpTrace
  calc
    (∑' q : effectiveGamma0 N, b (effectiveMatrixAction N q (effectiveMatrixAction N r z))) =
        ∑' q : effectiveGamma0 N, b (effectiveMatrixAction N (q * r) z) := by
      apply tsum_congr
      intro q
      rw [effectiveMatrixAction_mul]
    _ = _ := (Equiv.mulRight r).tsum_eq (fun q => b (effectiveMatrixAction N q z))

theorem bumpTrace_nonneg (N : ℕ) (b : UpperHalfPlane → ℝ)
    (hb : ∀ w, 0 ≤ b w) (z : UpperHalfPlane) : 0 ≤ bumpTrace N b z :=
  tsum_nonneg (fun q => hb _)

/-- Orbit coverage plus bump positivity, rather than a presumed nonzero
normalizing denominator, gives strict positivity at the target point. -/
theorem bumpTrace_pos_of_orbit_meets (N : ℕ) (b : UpperHalfPlane → ℝ)
    {K C : Set UpperHalfPlane} (hK : IsCompact K)
    (hbK : Function.support b ⊆ K) (hb : ∀ w, 0 ≤ b w)
    (hbC : ∀ w ∈ C, 0 < b w) (z : UpperHalfPlane)
    (hcover : ∃ q : effectiveGamma0 N, effectiveMatrixAction N q z ∈ C) :
    0 < bumpTrace N b z := by
  obtain ⟨q, hq⟩ := hcover
  exact (bumpTrace_summable N b hK hbK z).tsum_pos
    (fun r => hb _) q (hbC _ hq)

/-- A literal compactly supported seed; no tensor-span membership is hidden. -/
def normalizedSeed (N : ℕ) (b : UpperHalfPlane → ℝ)
    (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  (b z : ℂ) * F z / (bumpTrace N b z : ℂ)

theorem normalizedSeed_support_subset (N : ℕ) (b : UpperHalfPlane → ℝ)
    (F : UpperHalfPlane → ℂ) :
    Function.support (normalizedSeed N b F) ⊆ Function.support b := by
  intro z hz hzero
  exact hz (by simp [normalizedSeed, hzero])

theorem normalizedSeed_hasCompactSupport (N : ℕ) (b : UpperHalfPlane → ℝ)
    (F : UpperHalfPlane → ℂ) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (hbK : Function.support b ⊆ K) :
    HasCompactSupport (normalizedSeed N b F) := by
  apply hK.of_isClosed_subset isClosed_tsupport
  exact closure_minimal ((normalizedSeed_support_subset N b F).trans hbK) hK.isClosed

/-- The real denominator agrees exactly with the existing complex trace. -/
theorem complex_trace_bump (N : ℕ) (b : UpperHalfPlane → ℝ) (z : UpperHalfPlane) :
    complexSeedTrace N (fun w => (b w : ℂ)) z = (bumpTrace N b z : ℂ) := by
  simp only [complexSeedTrace, translatedSeed, bumpTrace, Complex.ofReal_tsum]

private theorem invariant_effective (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z, F (g • z) = F z)
    (q : effectiveGamma0 N) (z : UpperHalfPlane) :
    F (effectiveMatrixAction N q z) = F z := hF (effectiveRepresentative N q) z

/-- Exact actual effective-Poincare reconstruction. The coverage premise is
only the geometric orbit/compact-carrier relation, and the denominator
positivity needed for division is proved from the nonnegative compact bump. -/
theorem normalizedSeed_trace_eq (N : ℕ) (b : UpperHalfPlane → ℝ)
    (F : UpperHalfPlane → ℂ) {K C : Set UpperHalfPlane}
    (hK : IsCompact K) (hbK : Function.support b ⊆ K)
    (hb : ∀ w, 0 ≤ b w) (hbC : ∀ w ∈ C, 0 < b w)
    (hF : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z, F (g • z) = F z)
    (hcover : ∀ z, F z ≠ 0 →
      ∃ q : effectiveGamma0 N, effectiveMatrixAction N q z ∈ C)
    (z : UpperHalfPlane) : complexSeedTrace N (normalizedSeed N b F) z = F z := by
  by_cases hz : F z = 0
  · unfold complexSeedTrace translatedSeed
    have hall : ∀ q : effectiveGamma0 N,
        normalizedSeed N b F (effectiveMatrixAction N q z) = 0 := by
      intro q
      simp [normalizedSeed, invariant_effective N F hF q z, hz]
    simp only [hall, tsum_zero, hz]
  · have hdpos := bumpTrace_pos_of_orbit_meets N b hK hbK hb hbC z (hcover z hz)
    have hd : (bumpTrace N b z : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hdpos
    calc
      complexSeedTrace N (normalizedSeed N b F) z =
          ∑' q : effectiveGamma0 N,
            (b (effectiveMatrixAction N q z) : ℂ) * F z / (bumpTrace N b z : ℂ) := by
        unfold complexSeedTrace translatedSeed
        apply tsum_congr
        intro q
        simp only [normalizedSeed, invariant_effective N F hF q z, bumpTrace_action]
      _ = (∑' q : effectiveGamma0 N, (b (effectiveMatrixAction N q z) : ℂ)) *
          F z / (bumpTrace N b z : ℂ) := by
        rw [tsum_div_const, tsum_mul_right]
      _ = (bumpTrace N b z : ℂ) * F z / (bumpTrace N b z : ℂ) := by
        rw [← Complex.ofReal_tsum]
        rfl
      _ = F z := by field_simp

end
end ImbalancedChen.Part3.Gamma0NormalizedCompactSeed20261025a
