import ImbalancedChen.Part5OriginalH430FutureQuantitativePhysicalFloor
import ImbalancedChen.Part5OriginalH430FirstRoundPhysicalMassMoment

/-!
P5.6 / h34: literal Q80 physical INCREMENT accounting across the original
430-round producer. This is a telescope, not another parallel positive
source and NOT the selected U3/U4 count identity.

A physical cell which was already positive in an earlier generation is
not charged again merely because retention carries it into later rounds.
Only its exact integer increase is counted at that later generation.
All increments are nonnegative from the ORIGINAL retention rule.
The lower table's first 50 structurally inactive cells have zero
increments for every generation.

The exact sum of all 430 increments is final physical Q80 mass minus
the actual initial seed mass. Combining the already-recorded original
second/third/fourth-round receipts gives a *necessary* net growth floor.
This is NOT an analytic F upper payment, a Theta or seven-integral bound,
a root-weighted q/tag selected-count, or a full CLOSED-CELL induction.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralIncrementTelescope
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430FutureQuantitativePhysicalFloor
open Part5OriginalH430FirstRoundPhysicalMassMoment
open Part5OriginalH430Q80InitialSupport

/-- One and only one original physical Q80 numerator change at
generation g. No winning action is counted twice by this definition. -/
def literalIncrement (g : ℕ) (upper : Bool) (i : Fin 200) : ℤ :=
  iterate (g + 1) upper i - iterate g upper i

/-- Nonnegative payment is derived from ORIGINAL retention and the
same old/new integer producer, not supplied as an extra hypothesis. -/
theorem literal_increment_nonneg (g : ℕ) (upper : Bool)
    (i : Fin 200) : 0 ≤ literalIncrement g upper i := by
  unfold literalIncrement
  exact sub_nonneg.mpr
    (original_iterate_le_of_le g (g + 1) (by omega) upper i)

/-- Across ANY literal prefix, retention is counted only once:
the sum of REAL integer additions telescopes exactly to the actual
Q80 endpoint minus the actual seed at the same physical cell. -/
theorem literal_increment_telescope (n : ℕ) (upper : Bool)
    (i : Fin 200) :
    (∑ g in Finset.range n, literalIncrement g upper i) =
      iterate n upper i - iterate 0 upper i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold literalIncrement
      ring

/-- No positive increment can vanish from a later causal prefix.
This compares actual producer values; it adds no extra mass source. -/
theorem literal_increment_prefix_le_430 (n : ℕ) (hn : n ≤ 430)
    (upper : Bool) (i : Fin 200) :
    (∑ g in Finset.range n, literalIncrement g upper i) ≤
      (∑ g in Finset.range 430, literalIncrement g upper i) := by
  rw [literal_increment_telescope, literal_increment_telescope]
  exact sub_le_sub_right
    (original_iterate_le_of_le n 430 hn upper i) _

/-- These 50 lower physical cells are structurally inactive,
not hidden rejected sources; their true generation increments are zero. -/
theorem lower_first_fifty_increment_zero (g : ℕ)
    (i : Fin 200) (hi : i.val < 50) :
    literalIncrement g false i = 0 := by
  simp [literalIncrement, lower_first_fifty_zero g i hi,
    lower_first_fifty_zero (g + 1) i hi]

/-- The exact original 430-round UPPER physical Q80 increment account.
The bank and Buchstab winners are already reflected in iterate;
none of the 106 rejected bank offers is artificially added here. -/
theorem upper_430_increment_account :
    (∑ i : Fin 200,
      ∑ g in Finset.range 430, literalIncrement g true i) =
    (∑ i : Fin 200, iterate 430 true i) -
      (∑ i : Fin 200, iterate 0 true i) := by
  simp_rw [literal_increment_telescope]
  rw [Finset.sum_sub_distrib]

/-- The matching original LOWER account has exactly zero bank offers
and includes the true offset-49 Buchstab decisions, not a scalar proxy. -/
theorem lower_430_increment_account :
    (∑ i : Fin 200,
      ∑ g in Finset.range 430, literalIncrement g false i) =
    (∑ i : Fin 200, iterate 430 false i) -
      (∑ i : Fin 200, iterate 0 false i) := by
  simp_rw [literal_increment_telescope]
  rw [Finset.sum_sub_distrib]

/-- Exact two-table raw physical mass conservation with ACTUAL seed.
This is a counting identity over 200+200 *physical sites*, not the
U3/U4 q/tag selected source and not 430 repeated initial masses. -/
theorem full_430_physical_increment_account :
    (∑ i : Fin 200,
      ∑ g in Finset.range 430, literalIncrement g true i) +
    (∑ i : Fin 200,
      ∑ g in Finset.range 430, literalIncrement g false i) =
    ((∑ i : Fin 200, iterate 430 true i) +
      (∑ i : Fin 200, iterate 430 false i)) -
    ((∑ i : Fin 200, iterate 0 true i) +
      (∑ i : Fin 200, iterate 0 false i)) := by
  rw [upper_430_increment_account, lower_430_increment_account]
  ring

/-- Necessary amount of genuinely ADDED raw physical Q80 numerator
across all 430 rounds. The value uses the earlier exact 4-round
physical floor and the exact original 60-cell upper seed, without
mistaking surviving support for repeated payments.
Neither the floor proofs nor this arithmetic has been Lean-compiled. -/
theorem full_430_increment_necessary_floor :
    (1731100593645017731014086 : ℤ) ≤
      (∑ i : Fin 200,
        ∑ g in Finset.range 430, literalIncrement g true i) +
      (∑ i : Fin 200,
        ∑ g in Finset.range 430, literalIncrement g false i) := by
  have hfloor := generation_430_physical_numerator_total_lower
  rw [full_430_physical_increment_account,
      original_seed_upper_physical_mass_exact,
      original_seed_lower_physical_mass_zero]
  omega

end
end ImbalancedChen.Part5OriginalH430LiteralIncrementTelescope
