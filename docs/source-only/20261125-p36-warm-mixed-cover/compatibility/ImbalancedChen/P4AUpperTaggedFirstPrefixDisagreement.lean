import ImbalancedChen.P3OriginalU5WarmMixedReusedCore
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
