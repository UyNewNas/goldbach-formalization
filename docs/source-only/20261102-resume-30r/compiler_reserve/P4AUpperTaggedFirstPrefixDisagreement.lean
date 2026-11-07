import ImbalancedChen.P4AUpperTaggedMixedWallPayment

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The O compiler compares complete valid selections, not independent gates.
This file extracts the FIRST actual differing selected-prefix decision from
its real opposite witness. All earlier decisions agree, the witness stays
in the same historical tag and fine cell, and an upper even decision cannot
be the differing decision. No mixed-cover, support/rank or small-error
hypothesis is introduced.

This is the missing tree-to-prefix conversion. Identifying every resulting
actual policy decision with a frozen finite affine circuit is a separate
source obligation, not a field of a new policy record.
-/

namespace ImbalancedChen.P4AUpperTaggedFirstPrefixDisagreement

noncomputable section
open scoped Classical
open P4AUpperTaggedParityCompiler

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

/-- Complete actual tagged crossing coverage by first differing odd policy
prefixes. This conclusion retains the actual charged d, its opposite e,
the original rank, all earlier equal decisions, and the frozen tag.
It is a tree classification, not yet a proper-affine-wall classification. -/
theorem crossing_first_actual_odd_prefix
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap w z)
    (hc : crossing keep tag N cap w z tau d) :
    ∃ e ∈ cell tag N cap w z tau d, tag e = tag d ∧
      primeWordLabel N tau e = primeWordLabel N tau d ∧
      ∃ k : ℕ, k < d.primeFactorsList.length ∧
        polarityAfter true (k + 1) = false ∧
        keep ((d.primeFactorsList.reverse.take (k + 1)).reverse) ≠
          keep ((e.primeFactorsList.reverse.take (k + 1)).reverse) ∧
        ∀ i : ℕ, i < k →
          decisionAt (oddFirstExitPolicy keep) [] true d.primeFactorsList.reverse i =
            decisionAt (oddFirstExitPolicy keep) [] true e.primeFactorsList.reverse i := by
  obtain ⟨e, he, htag, hlabels, hvalid⟩ :=
    P4AUpperTaggedMixedWallPayment.crossing_at_point_has_opposite_canonical_selection
      keep tag N cap w z tau hd hc
  have hlen : d.primeFactorsList.reverse.length = e.primeFactorsList.reverse.length := by
    simpa only [List.length_reverse] using (cell_rank_preserved tag N cap w z tau he).symm
  obtain ⟨k, hk, hdiff, hbefore⟩ := validSelection_disagreement_first_decision
    (oddFirstExitPolicy keep) d.primeFactorsList.reverse e.primeFactorsList.reverse
    hlen [] [] true hvalid
  have hke : k < e.primeFactorsList.reverse.length := by omega
  rw [decisionAt_eq_prefix _ [] true _ k hk,
    decisionAt_eq_prefix _ [] true _ k hke] at hdiff
  simp only [List.append_nil] at hdiff
  have hodd : polarityAfter true (k + 1) = false := by
    cases hpol : polarityAfter true (k + 1) with
    | false => rfl
    | true =>
        exact (hdiff (by simp only [hpol, oddFirstExitPolicy, Bool.true_or])).elim
  have hkeep : keep ((d.primeFactorsList.reverse.take (k + 1)).reverse) ≠
      keep ((e.primeFactorsList.reverse.take (k + 1)).reverse) := by
    simpa only [hodd, oddFirstExitPolicy, Bool.false_or] using hdiff
  exact ⟨e, he, htag, hlabels, k, by simpa only [List.length_reverse] using hk,
    hodd, hkeep, hbefore⟩

/-- Literal one-unit coefficient changes inherit the complete prefix
classification; it is not restricted to a preselected wall subfamily. -/
theorem changed_first_actual_odd_prefix
    (keep : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap w z)
    (hc : changed keep tag N cap w z tau d) :
    ∃ e ∈ cell tag N cap w z tau d, tag e = tag d ∧
      primeWordLabel N tau e = primeWordLabel N tau d ∧
      ∃ k : ℕ, k < d.primeFactorsList.length ∧
        polarityAfter true (k + 1) = false ∧
        keep ((d.primeFactorsList.reverse.take (k + 1)).reverse) ≠
          keep ((e.primeFactorsList.reverse.take (k + 1)).reverse) ∧
        ∀ i : ℕ, i < k →
          decisionAt (oddFirstExitPolicy keep) [] true d.primeFactorsList.reverse i =
            decisionAt (oddFirstExitPolicy keep) [] true e.primeFactorsList.reverse i :=
  crossing_first_actual_odd_prefix keep tag N cap w z tau hd
    (changed_implies_crossing keep tag N cap w z tau hd hc)

/-- Same OriginalData and same historical tag as O's compiledRho.
No full87 identity of the held constructor is asserted. -/
theorem held_changed_first_actual_odd_prefix
    (data : P5OriginalCommonRefinedConstructor.OriginalData)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap w z)
    (hc : changed (P4ACommonPolicyTaggedCompiler.heldRetain data N)
      (P4ACommonPolicyTaggedCompiler.historicalTag data N) N cap w z tau d) :
    ∃ e ∈ cell (P4ACommonPolicyTaggedCompiler.historicalTag data N) N cap w z tau d,
      P4ACommonPolicyTaggedCompiler.historicalTag data N e =
        P4ACommonPolicyTaggedCompiler.historicalTag data N d ∧
      primeWordLabel N tau e = primeWordLabel N tau d ∧
      ∃ k : ℕ, k < d.primeFactorsList.length ∧
        polarityAfter true (k + 1) = false ∧
        P4ACommonPolicyTaggedCompiler.heldRetain data N
            ((d.primeFactorsList.reverse.take (k + 1)).reverse) ≠
          P4ACommonPolicyTaggedCompiler.heldRetain data N
            ((e.primeFactorsList.reverse.take (k + 1)).reverse) ∧
        ∀ i : ℕ, i < k →
          decisionAt (oddFirstExitPolicy (P4ACommonPolicyTaggedCompiler.heldRetain data N))
              [] true d.primeFactorsList.reverse i =
            decisionAt (oddFirstExitPolicy (P4ACommonPolicyTaggedCompiler.heldRetain data N))
              [] true e.primeFactorsList.reverse i :=
  changed_first_actual_odd_prefix (P4ACommonPolicyTaggedCompiler.heldRetain data N)
    (P4ACommonPolicyTaggedCompiler.historicalTag data N) N cap w z tau hd hc

end
end ImbalancedChen.P4AUpperTaggedFirstPrefixDisagreement
