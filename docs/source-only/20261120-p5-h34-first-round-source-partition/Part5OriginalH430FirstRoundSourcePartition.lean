import ImbalancedChen.Part5OriginalH430Q80InitialSupport

/-!
P5.6 / h34: EXACT original Q80 first-round source partition.

At the real first update, an overflow above a common integer ceiling
that already bounds the genuine seed must come from exactly one of:
* a targeted ORIGINAL upper 106-bank candidate, or
* a lower Buchstab suffix with physical index 50 <= i < 109.
The upper Buchstab branch reads the zero initial lower table, and
retention cannot first overflow a seed-safe ceiling. The lower suffix
outside 50..108 reads only zero upper seed. The last theorem proves the
corresponding sufficient one-round ceiling condition using only these
actual positive-source checks. It does NOT assert their numerical
payment, the F seed, or full CLOSED-CELL.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FirstRoundSourcePartition
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (q rows)
open Part5OriginalH430Q80InitialSupport
open Part5OriginalH430LiteralRoundActionStep

private theorem upper_seed_nonnegative (i : Fin 200) :
    (0 : ℤ) ≤ seed true i := by
  by_cases hi : i.val < 60
  · norm_num [seed, q, hi]
  · simp [seed, hi]

private theorem ceiling_upper_nonnegative
    (ceiling : Table)
    (hseed : ∀ upper i, iterate 0 upper i ≤ ceiling upper i)
    (i : Fin 200) : (0 : ℤ) ≤ ceiling true i := by
  have hs : seed true i ≤ ceiling true i := by
    simpa [iterate] using hseed true i
  exact (upper_seed_nonnegative i).trans hs

/-- Any first-round UPPER strict excess over a seed-safe integer
ceiling is caused by one of the ACTUALLY targeted original 106 bank
offers, not by retention or a phantom upper Buchstab term. -/
theorem upper_first_round_excess_is_targeted_bank
    (ceiling : Table)
    (hseed : ∀ upper i, iterate 0 upper i ≤ ceiling upper i)
    (i : Fin 200)
    (hbad : ceiling true i < iterate 1 true i) :
    ∃ k : Fin 106, i.val ∈ (rows k).targets ∧
      ceiling true i < candidate seed (rows k) := by
  have hbad' :
      ceiling true i <
        iterate ((⟨0, by decide⟩ : Fin 430).val + 1) true i := by
    simpa using hbad
  rcases actual_iteration_overflow_has_action_witness
      (⟨0, by decide⟩ : Fin 430) true i (ceiling true i) hbad'
      with hret | hbuch | hbank
  · exact False.elim ((not_lt_of_ge (hseed true i)) hret)
  · obtain ⟨_, hsource⟩ := hbuch
    have hzero :
        suffix (iterate 0) false (max 50 (i.val - 49)) = 0 := by
      simpa [iterate] using
        initial_upper_buchstab_suffix_zero (max 50 (i.val - 49))
    have hnegative : ceiling true i < 0 := by
      simpa [hzero] using hsource
    exact False.elim
      ((not_lt_of_ge (ceiling_upper_nonnegative ceiling hseed i))
        hnegative)
  · simpa [iterate] using hbank.2

/-- Any first-round LOWER strict excess over a seed-safe ceiling is
caused by the real opposite-table suffix in the only eligible physical
window 50..108, not by a bank offer or by retention. -/
theorem lower_first_round_excess_is_limited_buchstab
    (ceiling : Table)
    (hseed : ∀ upper i, iterate 0 upper i ≤ ceiling upper i)
    (i : Fin 200)
    (hbad : ceiling false i < iterate 1 false i) :
    50 ≤ i.val ∧ i.val < 109 ∧
      ceiling false i < suffix seed true (i.val - 49) := by
  have hzero : iterate 0 false i = 0 := by
    simp [iterate, seed]
  have hceiling : (0 : ℤ) ≤ ceiling false i := by
    calc
      (0 : ℤ) = iterate 0 false i := hzero.symm
      _ ≤ ceiling false i := hseed false i
  have hnonzero : iterate 1 false i ≠ 0 := by
    intro heq
    have hnegative : ceiling false i < 0 := by
      simpa [heq] using hbad
    exact (not_lt_of_ge hceiling) hnegative
  obtain ⟨h50, h109⟩ :=
    first_lower_nonzero_only_in_fifty_to_108 i hnonzero
  have hbad' :
      ceiling false i <
        iterate ((⟨0, by decide⟩ : Fin 430).val + 1) false i := by
    simpa using hbad
  rcases actual_iteration_overflow_has_action_witness
      (⟨0, by decide⟩ : Fin 430) false i (ceiling false i) hbad'
      with hret | hbuch | hbank
  · exact False.elim ((not_lt_of_ge (hseed false i)) hret)
  · obtain ⟨_, hsource⟩ := hbuch
    exact ⟨h50, h109, by simpa [iterate] using hsource⟩
  · exact False.elim (Bool.false_ne_true hbank.1)

/-- Exact first update dichotomy over BOTH 200-cell tables.
The original source indices and bank targets remain intact; no
selected-count family or alternative action is invented. -/
theorem first_round_excess_has_restricted_positive_source
    (ceiling : Table)
    (hseed : ∀ upper i, iterate 0 upper i ≤ ceiling upper i)
    (hbad : ∃ upper i, ceiling upper i < iterate 1 upper i) :
    (∃ i : Fin 200, ∃ k : Fin 106,
      i.val ∈ (rows k).targets ∧
        ceiling true i < candidate seed (rows k)) ∨
    (∃ i : Fin 200, 50 ≤ i.val ∧ i.val < 109 ∧
      ceiling false i < suffix seed true (i.val - 49)) := by
  obtain ⟨upper, i, hcross⟩ := hbad
  cases upper with
  | false =>
      exact Or.inr ⟨i,
        lower_first_round_excess_is_limited_buchstab
          ceiling hseed i hcross⟩
  | true =>
      obtain ⟨k, htarget, hcandidate⟩ :=
        upper_first_round_excess_is_targeted_bank
          ceiling hseed i hcross
      exact Or.inl ⟨i, k, htarget, hcandidate⟩

/-- The first ACTUAL Q80 round needs only the genuine 106 targeted
upper-bank inequalities and the 59 possible lower suffix indices.
The source bounds are still manuscript-internal, UNPAID obligations;
no uniform 430-generation or F envelope hypothesis is smuggled in. -/
theorem first_round_safe_of_paid_actual_sources
    (ceiling : Table)
    (hseed : ∀ upper i, iterate 0 upper i ≤ ceiling upper i)
    (hbank : ∀ (i : Fin 200) (k : Fin 106),
      i.val ∈ (rows k).targets →
        candidate seed (rows k) ≤ ceiling true i)
    (hlower : ∀ i : Fin 200,
      50 ≤ i.val → i.val < 109 →
        suffix seed true (i.val - 49) ≤ ceiling false i) :
    ∀ upper i, iterate 1 upper i ≤ ceiling upper i := by
  intro upper i
  by_contra hn
  have hbad : ceiling upper i < iterate 1 upper i :=
    lt_of_not_ge hn
  rcases first_round_excess_has_restricted_positive_source
      ceiling hseed ⟨upper, i, hbad⟩ with
    ⟨j, k, htarget, hcross⟩ |
    ⟨j, h50, h109, hcross⟩
  · exact (not_lt_of_ge (hbank j k htarget)) hcross
  · exact (not_lt_of_ge (hlower j h50 h109)) hcross

end
end ImbalancedChen.Part5OriginalH430FirstRoundSourcePartition
