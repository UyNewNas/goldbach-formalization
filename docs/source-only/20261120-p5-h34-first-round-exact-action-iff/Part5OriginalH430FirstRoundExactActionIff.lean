import ImbalancedChen.Part5OriginalH430FirstRoundActiveSupport

/-!
P5.6 / h34: a two-way, exact FIRST-ROUND Q80 source test.

Earlier source established that the authentic first update is safe if the
real seed and every targeted 106-bank candidate / eligible lower suffix
obey an integer ceiling. This file proves the MISSING converse: each
targeted bank offer and each enabled lower suffix is bounded by the
ACTUAL first-round result, irrespective of which offer finally wins.
Thus those 106-row / 59-physical-index checks are necessary AND
sufficient for one complete first Q80 generation, conditional only on
the separately unpaid genuine seed bound.

This is not a bound on the candidates, nor a 430-round CLOSED-CELL or
original U3/U4 count proof. No source, Q80 divisor, row target,
first-round result, or frozen analytic envelope is replaced.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FirstRoundExactActionIff
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430Q80InitialSupport
open Part5OriginalH430FirstRoundSourcePartition

/-- The genuine max-with-provenance offer never lowers the current
integer numerator. -/
private theorem offer_retains_numerator
    (d : Decision) (v : ℤ) (c : Choice) :
    d.numerator ≤ (offer d v c).numerator := by
  rw [offer_numerator]
  exact le_max_left _ _

/-- It also never falls below the candidate it is actually offered. -/
private theorem offer_contains_candidate
    (d : Decision) (v : ℤ) (c : Choice) :
    v ≤ (offer d v c).numerator := by
  rw [offer_numerator]
  exact le_max_right _ _

private theorem offerRow_retains_numerator
    (old : Table) (i : Fin 200) (d : Decision) (k : Fin 106) :
    d.numerator ≤ (offerRow old i d k).numerator := by
  by_cases ht : i.val ∈ (rows k).targets
  · simpa only [offerRow, if_pos ht] using
      (offer_retains_numerator d (candidate old (rows k)) (.bank k))
  · simpa only [offerRow, if_neg ht] using (le_refl d.numerator)

/-- Genuine left-to-right 106-bank scanning never decreases its
accumulated integer numerator. -/
private theorem scan_retains_numerator
    (old : Table) (i : Fin 200) :
    ∀ (ks : List (Fin 106)) (d : Decision),
      d.numerator ≤ (scan old i ks d).numerator := by
  intro ks
  induction ks with
  | nil =>
      intro d
      exact le_refl _
  | cons k ks ih =>
      intro d
      change d.numerator ≤
        (scan old i ks (offerRow old i d k)).numerator
      exact (offerRow_retains_numerator old i d k).trans
        (ih (offerRow old i d k))

/-- Every genuinely targeted row is dominated by the FINAL scan
numerator. This includes a row that subsequently loses to another row:
the scan uses max, not a sum over 106 phantom winners. -/
private theorem targeted_candidate_le_scan
    (old : Table) (i : Fin 200)
    (ks : List (Fin 106)) (d : Decision)
    (k : Fin 106)
    (htarget : i.val ∈ (rows k).targets)
    (hk : k ∈ ks) :
    candidate old (rows k) ≤ (scan old i ks d).numerator := by
  induction ks generalizing d with
  | nil =>
      cases hk
  | cons j js ih =>
      have hmem : k = j ∨ k ∈ js := List.mem_cons.mp hk
      rcases hmem with h | h
      · subst j
        have hrow : candidate old (rows k) ≤
            (offerRow old i d k).numerator := by
          simpa only [offerRow, if_pos htarget] using
            (offer_contains_candidate d (candidate old (rows k))
              (.bank k))
        exact hrow.trans
          (scan_retains_numerator old i js (offerRow old i d k))
      · change candidate old (rows k) ≤
          (scan old i js (offerRow old i d j)).numerator
        exact ih (offerRow old i d j) h

/-- A real row is bounded by the ACTUAL first upper output, including
its original 106-row target and Q80 floor, even if it did not win. -/
theorem first_upper_target_candidate_le_actual
    (i : Fin 200) (k : Fin 106)
    (htarget : i.val ∈ (rows k).targets) :
    candidate seed (rows k) ≤ iterate 1 true i := by
  calc
    candidate seed (rows k) ≤
        (scan seed i (List.finRange 106)
          ⟨seed true i, Choice.retained⟩).numerator := by
        exact targeted_candidate_le_scan seed i
          (List.finRange 106)
          ⟨seed true i, Choice.retained⟩ k htarget
          (by simp)
    _ = iterate 1 true i :=
      (first_upper_round_is_exact_bank_scan i).symm

/-- The real first lower output dominates every enabled Buchstab
suffix. At first generation the old lower seed is zero, but this lower
candidate still reads the ORIGINAL positive upper seed, with offset49. -/
theorem first_lower_suffix_le_actual
    (i : Fin 200) (h50 : 50 ≤ i.val) :
    suffix seed true (i.val - 49) ≤ iterate 1 false i := by
  change suffix seed true (i.val - 49) ≤
    (ordinaryDecision seed false i).numerator
  rw [ordinaryDecision_numerator]
  simpa [h50] using
    (le_max_right (seed false i) (suffix seed true (i.val - 49)))

/-- EXACT one-generation equivalence at all 400 physical Boolean-table
cells. Assuming ONLY the legitimate actual initial seed inequality,
the first full Q80 update is ceiling-safe precisely when all targeted
original 106-bank candidates and the 59 eligible lower suffix indices
are ceiling-safe. No candidate payment is asserted by this equivalence.
The reverse direction uses the prior actual first-round source partition;
the forward direction uses max retention of EACH literal candidate. -/
theorem first_round_safe_iff_all_actual_positive_sources
    (ceiling : Table)
    (hseed : ∀ upper i, iterate 0 upper i ≤ ceiling upper i) :
    (∀ upper i, iterate 1 upper i ≤ ceiling upper i) ↔
      ( (∀ (i : Fin 200) (k : Fin 106),
           i.val ∈ (rows k).targets →
             candidate seed (rows k) ≤ ceiling true i) ∧
        (∀ i : Fin 200, 50 ≤ i.val → i.val < 109 →
           suffix seed true (i.val - 49) ≤ ceiling false i)) := by
  constructor
  · intro hsafe
    constructor
    · intro i k ht
      exact (first_upper_target_candidate_le_actual i k ht).trans
        (hsafe true i)
    · intro i h50 _
      exact (first_lower_suffix_le_actual i h50).trans (hsafe false i)
  · rintro ⟨hbank, hlower⟩
    exact first_round_safe_of_paid_actual_sources
      ceiling hseed hbank hlower

end
end ImbalancedChen.Part5OriginalH430FirstRoundExactActionIff
