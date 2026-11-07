import ImbalancedChen.Part3ActualHeckeEffectiveRightTransversal
import ImbalancedChen.Part3Gamma0CompactTensorPoincareLocalFinite
import ImbalancedChen.Part3Gamma0ComplexL1PoincareUnfolding
import ImbalancedChen.Part3ActualPrimeHeckeQuotientDescent
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The original compact-seed effective Poincare trace has an exact physical
Hecke identity, with transformed seed p^-1/2 sum_j f(B_j^-1 z).
The CORRECT inverse-branch right transversal and full +/-I effective
index equivalence are used. Original compact_seed_locally_finite supplies
actual finite double-index support before any series interchange; no
summability, seed L1, Poincare-Hecke identity or right-representative
premise is supplied. This is pointwise on the full upper half-plane.
-/

namespace ImbalancedChen.Part3.ActualCompactSeedHeckeReindex20261026b
noncomputable section
open Set MeasureTheory Filter Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators Topology
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRealBranch20261026b
open ActualPrimeHeckeQuotientDescent20261026b ActualHeckeEffectiveRightTransversal20261026b
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0ComplexL1PoincareUnfolding20261025a

variable (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)

def dualHeckeSeed (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  (Real.sqrt (p : ℝ) : ℂ)⁻¹ • ∑ j : Branch p, f ((branchSL p hp.pos j)⁻¹ • z)

/-- Original compact local finiteness gives a concrete finite support for
ALL left Hecke terms simultaneously, with the branch index retained. -/
theorem compact_left_pairs_summable (f : ℍ → ℂ) {K : Set ℍ} (hK : IsCompact K)
    (hs : Function.support f ⊆ K) (z : ℍ) :
    Summable (fun q : effectiveGamma0 N × Branch p =>
      f (effectiveMatrixAction N q.1 (branchSL p hp.pos q.2 • z))) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hlocal (j : Branch p) := compact_seed_locally_finite N f hK hs (branchSL p hp.pos j • z)
  choose U hU S hS using hlocal
  let T : Finset (effectiveGamma0 N × Branch p) :=
    Finset.univ.biUnion (fun j : Branch p => (S j).image (fun q => (q,j)))
  apply summable_of_ne_finset_zero (s := T)
  intro q hq
  have hout : q.1 ∉ S q.2 := by
    intro hmem
    apply hq
    exact Finset.mem_biUnion.mpr ⟨q.2,Finset.mem_univ _,Finset.mem_image.mpr ⟨q.1,hmem,rfl⟩⟩
  exact hS q.2 (branchSL p hp.pos q.2 • z) (mem_of_mem_nhds (hU q.2)) q.1 hout

/-- Right double-series summability is DERIVED from original compact
local finiteness and the paid effective transversal action identity. -/
theorem compact_right_pairs_summable (f : ℍ → ℂ) {K : Set ℍ} (hK : IsCompact K)
    (hs : Function.support f ⊆ K) (z : ℍ) :
    Summable (fun q : Branch p × effectiveGamma0 N =>
      f ((branchSL p hp.pos q.1)⁻¹ • effectiveMatrixAction N q.2 z)) := by
  let E := effectiveDualRightTransversal N p hp hpN
  apply E.summable_iff.mp
  simpa only [E,Function.comp_def,effectiveDualRightTransversal_action] using
    (compact_left_pairs_summable N p hp f hK hs z)

/-- Exact sum reindexing, with every infinite sum already summable by
original compact support and with the central signs counted only once. -/
theorem compact_seed_trace_Hecke (f : ℍ → ℂ) {K : Set ℍ} (hK : IsCompact K)
    (hs : Function.support f ⊆ K) (z : ℍ) :
    nativeHecke p hp.pos (complexSeedTrace N f) z = complexSeedTrace N (dualHeckeSeed p hp f) z := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let FL : effectiveGamma0 N × Branch p → ℂ := fun q =>
    f (effectiveMatrixAction N q.1 (branchSL p hp.pos q.2 • z))
  let FR : Branch p × effectiveGamma0 N → ℂ := fun q =>
    f ((branchSL p hp.pos q.1)⁻¹ • effectiveMatrixAction N q.2 z)
  have hFL : Summable FL := compact_left_pairs_summable N p hp f hK hs z
  have hFR : Summable FR := compact_right_pairs_summable N p hp hpN f hK hs z
  have hleft : (∑ j : Branch p, complexSeedTrace N f (branchSL p hp.pos j • z)) = ∑' q,FL q := by
    calc
      _ = ∑' j : Branch p, ∑' q : effectiveGamma0 N, FL (q,j) := by
        rw [tsum_fintype]
        rfl
      _ = ∑' q : effectiveGamma0 N, ∑' j : Branch p, FL (q,j) := hFL.tsum_comm
      _ = _ := hFL.tsum_prod.symm
  have hreindex : (∑' q,FL q) = ∑' q,FR q := by
    have he := (effectiveDualRightTransversal N p hp hpN).tsum_eq FR
    simpa only [FR,FL,effectiveDualRightTransversal_action] using he
  have hright : (∑' q,FR q) = ∑' q : effectiveGamma0 N, ∑ j : Branch p, FR (j,q) := by
    calc
      _ = ∑' j : Branch p, ∑' q : effectiveGamma0 N, FR (j,q) := hFR.tsum_prod
      _ = ∑' q : effectiveGamma0 N, ∑' j : Branch p, FR (j,q) := hFR.tsum_comm.symm
      _ = _ := by simp only [tsum_fintype]
  have hsum : Summable (fun q : effectiveGamma0 N => ∑ j : Branch p, FR (j,q)) := by
    have h := hFR.prod_symm.prod
    simpa only [tsum_fintype] using h
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹ •
    (∑ j : Branch p, complexSeedTrace N f (branchSL p hp.pos j • z)) = _
  calc
    _ = (Real.sqrt (p : ℝ) : ℂ)⁻¹ •
        (∑' q : effectiveGamma0 N, ∑ j : Branch p, FR (j,q)) := by
      rw [hleft,hreindex,hright]
    _ = ∑' q : effectiveGamma0 N,
        (Real.sqrt (p : ℝ) : ℂ)⁻¹ • ∑ j : Branch p, FR (j,q) :=
      (Summable.tsum_const_smul _ hsum).symm
    _ = _ := rfl

/-- The transformed actual seed trace is genuinely summable at every
point; this is not merely an identity of default-zero divergent sums. -/
theorem dualHeckeSeed_trace_summable (f : ℍ → ℂ) {K : Set ℍ} (hK : IsCompact K)
    (hs : Function.support f ⊆ K) (z : ℍ) :
    Summable (fun q : effectiveGamma0 N => dualHeckeSeed p hp f (effectiveMatrixAction N q z)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := (compact_right_pairs_summable N p hp hpN f hK hs z).prod_symm.prod
  have hsum : Summable (fun q : effectiveGamma0 N => ∑ j : Branch p,
      f ((branchSL p hp.pos j)⁻¹ • effectiveMatrixAction N q z)) := by
    simpa only [tsum_fintype] using h
  exact Summable.const_smul _ hsum

end
end ImbalancedChen.Part3.ActualCompactSeedHeckeReindex20261026b

