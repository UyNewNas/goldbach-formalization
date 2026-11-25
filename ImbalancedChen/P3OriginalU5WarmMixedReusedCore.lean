import ImbalancedChen.P2RoundedFibreCore
import ImbalancedChen.P2OriginalPairRootRoughProducer
import ImbalancedChen.FirstExitValidSelection
import Mathlib

/-! Fixed-Git reuse only. No new first-disagreement or affine crossing proof.
SOURCE ONLY / UNCOMPILED. Namespace names are preserved. The sole qualified
universe identifier receives the known reserved-word quoting adaptation. -/

namespace ImbalancedChen.P2ActualPairPlanRawSupport
noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2LowerCanonicalRetainedTrace

theorem pair_raw_iff_canonical_warm {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (N enum : ℕ)
    (p : ℕ × ℕ) (z0 z : ℝ) (r : ℕ) :
    r ∈ P2LowerFiniteCellRounding.rawSupport (pairPolicy P a b seed N p)
      N enum z0 z ↔ r ∈ P2LowerFiniteCellRounding.«universe» N enum z0 z ∧
      pairPolicy P a b seed N p r.primeFactorsList = true := by
  constructor
  · intro hr
    have hU := P2LowerFiniteCellRounding.rawSupport_subset_universe
      (pairPolicy P a b seed N p) N enum z0 z hr
    obtain ⟨chosen, hsub, haccept, hprod⟩ :=
      (pair_policy_support_iff P a b seed N enum p z0 z r).mp hr
    have hc := actual_chosen_eq_canonical N enum z0 z chosen hsub hprod
    refine ⟨hU, ?_⟩
    simpa only [pairPolicy, warmRetain, warmTrace, physicalWord, hc] using haccept
  · rintro ⟨hU, haccept⟩
    obtain ⟨hsub, hprod⟩ := canonical_subword_of_universe N enum z0 z hU
    apply (pair_policy_support_iff P a b seed N enum p z0 z r).mpr
    refine ⟨r.primeFactorsList.reverse, hsub, ?_, hprod⟩
    simpa only [pairPolicy, warmRetain, warmTrace, physicalWord] using haccept

/-- The actual pair-root ALL/ANY loss sees canonical WARM traces. The pair
seed and external coordinates are fixed while two same-label rough words
are compared; the ordinary cold trace is not substituted. -/
theorem mixed_pair_iff_canonical_warm {depth mesh : ℕ}
    (P : CapPlan depth mesh) (a b seed : ℝ) (N enum : ℕ)
    (p : ℕ × ℕ) (z0 z tau : ℝ) (d : ℕ) :
    P2RoundedCausalFibreLossAndLevel.mixed (pairPolicy P a b seed N p)
      N enum z0 z tau d ↔
      ∃ r ∈ P2LowerFiniteCellRounding.cell N enum z0 z tau d,
      ∃ s ∈ P2LowerFiniteCellRounding.cell N enum z0 z tau d,
        pairPolicy P a b seed N p r.primeFactorsList = true ∧
        pairPolicy P a b seed N p s.primeFactorsList ≠ true := by
  constructor
  · rintro ⟨⟨r, hr, hrraw⟩, s, hs, hsraw⟩
    refine ⟨r, hr, s, hs, ?_, ?_⟩
    · exact ((pair_raw_iff_canonical_warm P a b seed N enum p z0 z r).mp hrraw).2
    · intro ht
      exact hsraw ((pair_raw_iff_canonical_warm P a b seed N enum p z0 z s).mpr
        ⟨(Finset.mem_filter.mp hs).1, ht⟩)
  · rintro ⟨r, hr, s, hs, htr, hts⟩
    refine ⟨⟨r, hr, ?_⟩, ⟨s, hs, ?_⟩⟩
    · exact (pair_raw_iff_canonical_warm P a b seed N enum p z0 z r).mpr
        ⟨(Finset.mem_filter.mp hr).1, htr⟩
    · intro hraw
      exact hts ((pair_raw_iff_canonical_warm P a b seed N enum p z0 z s).mp hraw).2



end
end ImbalancedChen.P2ActualPairPlanRawSupport

namespace ImbalancedChen.P4AUpperTaggedFirstPrefixDisagreement
noncomputable section
open scoped Classical

/-- The actual tree polarity after k selected primes. -/
def polarityAfter (positive : Bool) : ℕ → Bool
  | 0 => positive
  | k + 1 => polarityAfter (!positive) k

/-- Actual sequential decision, with the tree's newest-first history.
The out-of-range convention is unused in every theorem below. -/
def decisionAt {α : Type*} (P : Bool → List α → Bool)
    (pre : List α) (positive : Bool) : List α → ℕ → Bool
  | [], _ => true
  | p :: _, 0 => P (!positive) (p :: pre)
  | p :: ps, k + 1 => decisionAt P (p :: pre) (!positive) ps k

theorem decisionAt_eq_prefix {α : Type*} (P : Bool → List α → Bool)
    (pre : List α) (positive : Bool) (xs : List α) (k : ℕ)
    (hk : k < xs.length) :
    decisionAt P pre positive xs k =
      P (polarityAfter positive (k + 1)) ((xs.take (k + 1)).reverse ++ pre) := by
  induction xs generalizing pre positive k with
  | nil => simp at hk
  | cons p ps ih =>
      cases k with
      | zero => simp [decisionAt, polarityAfter]
      | succ k =>
          have hk' : k < ps.length := by simpa using hk
          simpa only [decisionAt, polarityAfter, List.take_succ_cons,
            List.reverse_cons, List.append_assoc, List.singleton_append] using
            ih (p :: pre) (!positive) k hk'

/-- A disagreement of complete valid selections produces an actual first
different decision. Earlier decisions are equal, even when one of them is
false. No retained representative replaces the charged word. -/
theorem validSelection_disagreement_first_decision {α : Type*}
    (P : Bool → List α → Bool) (xs ys : List α)
    (hlen : xs.length = ys.length) :
    ∀ (preX preY : List α) (positive : Bool),
      ¬(FirstExitValidSelection P preX positive xs ↔
        FirstExitValidSelection P preY positive ys) →
      ∃ k : ℕ, k < xs.length ∧
        decisionAt P preX positive xs k ≠ decisionAt P preY positive ys k ∧
        ∀ i : ℕ, i < k →
          decisionAt P preX positive xs i = decisionAt P preY positive ys i := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      intro preX preY positive hneq
      exact (hneq (by simp only [FirstExitValidSelection])).elim
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          intro preX preY positive hneq
          by_cases hhead : P (!positive) (x :: preX) = P (!positive) (y :: preY)
          · have htail :
                ¬(FirstExitValidSelection P (x :: preX) (!positive) xs ↔
                  FirstExitValidSelection P (y :: preY) (!positive) ys) := by
              intro hh
              apply hneq
              change (_ ∧ _) ↔ (_ ∧ _)
              rw [hhead, hh]
            obtain ⟨k, hk, hdiff, hbefore⟩ := ih ys (by simpa using hlen)
              (x :: preX) (y :: preY) (!positive) htail
            refine ⟨k + 1, by simpa using Nat.succ_lt_succ hk, hdiff, ?_⟩
            intro i hi
            cases i with
            | zero => exact hhead
            | succ i => exact hbefore i (by omega)
          · exact ⟨0, by simp, hhead, fun i hi => (Nat.not_lt_zero i hi).elim⟩


end
end ImbalancedChen.P4AUpperTaggedFirstPrefixDisagreement

namespace ImbalancedChen.P4AUpperTaggedFrozenAdmissionCatalogue
noncomputable section
open scoped Classical

/-- Truth disagreement derives properness. In particular zero affine
rows, whether true or false, have no wall and cannot be charged. -/
theorem strict_row_disagreement_proper_wall {r : ℕ}
    (L : (Fin r → ℝ) →L[ℝ] ℝ) (c tau : ℝ) (x y : Fin r → ℝ)
    (hclose : ‖x - y‖ ≤ tau) (hdiff : ¬(L x < c ↔ L y < c)) :
    L ≠ 0 ∧ |L x - c| ≤ ‖L‖ * tau := by
  have hproper : L ≠ 0 := by
    intro hz
    exact hdiff (by simp only [hz, ContinuousLinearMap.zero_apply])
  have hosc := L.le_opNorm (x - y)
  rw [map_sub, Real.norm_eq_abs] at hosc
  have hos := hosc.trans (mul_le_mul_of_nonneg_left hclose (norm_nonneg L))
  obtain ⟨hlo, hhi⟩ := abs_le.mp hos
  refine ⟨hproper, abs_le.mpr ?_⟩
  by_cases hx : L x < c
  · have hy : c ≤ L y := le_of_not_gt (fun hy => hdiff (iff_of_true hx hy))
    constructor <;> linarith
  · have hy : L y < c := by
      by_contra hy
      exact hdiff (iff_of_false hx hy)
    have hx' := le_of_not_gt hx
    constructor <;> linarith


end
end ImbalancedChen.P4AUpperTaggedFrozenAdmissionCatalogue

namespace ImbalancedChen.P5Z.PresievedRoughSlotAffineGates
noncomputable section
open scoped Classical BigOperators

def prefix {r : ℕ} (v : Fin r → ℝ) (i : Fin r) : ℝ := ∑ j : Fin r with j.val < i.val, v j

def cube {r : ℕ} (v : Fin r → ℝ) (i : Fin r) : ℝ := prefix v i + 3 * v i

def totalRow (r : ℕ) : (Fin r → ℝ) →L[ℝ] ℝ := ∑ i : Fin r, ContinuousLinearMap.proj i

def cubeRow {r : ℕ} (i : Fin r) : (Fin r → ℝ) →L[ℝ] ℝ :=
  (∑ j : Fin r with j.val < i.val, ContinuousLinearMap.proj j) + (3 : ℝ) • ContinuousLinearMap.proj i

theorem cubeRow_apply {r : ℕ} (i : Fin r) (v : Fin r → ℝ) : cubeRow i v = cube v i := by
  simp [cubeRow, cube, prefix, ContinuousLinearMap.sum_apply, smul_eq_mul]

end
end ImbalancedChen.P5Z.PresievedRoughSlotAffineGates
