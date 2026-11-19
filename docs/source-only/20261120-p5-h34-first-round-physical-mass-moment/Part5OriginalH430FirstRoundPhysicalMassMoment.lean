import ImbalancedChen.Part5OriginalH430FirstRoundExact400

/-!
P5.6 / h34: ORIGINAL first-generation Q80 physical aggregate receipts.

This packet does not replace the literal producer by a probability model.
The integer tables are the previously recorded exact 400 physical receipts.
The mass is the sum of Q80 numerators over the original 200 physical cells
PER TABLE; the first moment uses physical index i (not an integral variable).
In particular these totals are NOT an original U3/U4 arithmetic count owner,
a Theta count, an analytic F payment or a 430-round invariant.

The difference between generation one and the original seed is recorded
exactly, not described as a conserved mass. The source stays entirely
manuscript-internal and makes no new analytic assumptions.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FirstRoundPhysicalMassMoment
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430FirstRoundExact400

/-- A raw Q80 NUMERATOR total; no normalization by Q80 or owner multiplicity. -/
def firstRoundPhysicalMass (upper : Bool) : ℤ :=
  ∑ i : Fin 200, firstRoundExactReceipts upper i

/-- Physical-index first moment, retaining the original cell index. -/
def firstRoundPhysicalMoment (upper : Bool) : ℤ :=
  ∑ i : Fin 200, (i.val : ℤ) * firstRoundExactReceipts upper i

/-- The aggregate reads the ACTUAL original first-generation producer. -/
theorem first_round_physical_mass_actual (upper : Bool) :
    (∑ i : Fin 200, iterate 1 upper i) =
      firstRoundPhysicalMass upper := by
  unfold firstRoundPhysicalMass
  apply Finset.sum_congr rfl
  intro i _
  exact first_round_all_400_exact upper i

/-- Index weighting is performed after reading EACH physical original cell. -/
theorem first_round_physical_moment_actual (upper : Bool) :
    (∑ i : Fin 200, (i.val : ℤ) * iterate 1 upper i) =
      firstRoundPhysicalMoment upper := by
  unfold firstRoundPhysicalMoment
  apply Finset.sum_congr rfl
  intro i _
  rw [first_round_all_400_exact]

/-- Exact finite certificate: 95 potentially positive upper physical cells. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem first_round_upper_physical_mass_exact :
    firstRoundPhysicalMass true = 2246161734616850095238755 := by
  decide

/-- Exact finite certificate: the original lower physical indices 50..108. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem first_round_lower_physical_mass_exact :
    firstRoundPhysicalMass false = 567805031667360936980540 := by
  decide

/-- Exact physical-index moment of the original first upper table. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem first_round_upper_physical_moment_exact :
    firstRoundPhysicalMoment true = 86931177967141457720214218 := by
  decide

/-- Exact physical-index moment of the original first lower table. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem first_round_lower_physical_moment_exact :
    firstRoundPhysicalMoment false = 38666108370717453725152205 := by
  decide

/-- The original upper seed is supported on exactly its first 60 cells. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem original_seed_upper_physical_mass_exact :
    (∑ i : Fin 200, iterate 0 true i) =
      1687902229345945253724720 := by
  decide

/-- The original lower seed is identically zero, not a second root seed. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem original_seed_lower_physical_mass_zero :
    (∑ i : Fin 200, iterate 0 false i) = 0 := by
  decide

/-- Aggregate first-generation Q80 physical numerator MASS.
This is not the selected-count source, which has root/owner weights. -/
theorem first_round_total_physical_mass_actual :
    (∑ i : Fin 200, iterate 1 true i) +
        (∑ i : Fin 200, iterate 1 false i) =
      2813966766284211032219295 := by
  rw [first_round_physical_mass_actual, first_round_physical_mass_actual,
      first_round_upper_physical_mass_exact, first_round_lower_physical_mass_exact]
  norm_num

/-- The initial-to-first-round raw numerator increase is strictly positive.
It is not an extra analytical fee, an error budget, or a count licence. -/
theorem first_round_physical_mass_growth_exact :
    ((∑ i : Fin 200, iterate 1 true i) +
      (∑ i : Fin 200, iterate 1 false i)) -
    ((∑ i : Fin 200, iterate 0 true i) +
      (∑ i : Fin 200, iterate 0 false i)) =
      1126064536938265778494575 := by
  rw [first_round_total_physical_mass_actual,
      original_seed_upper_physical_mass_exact,
      original_seed_lower_physical_mass_zero]
  norm_num

/-- The two real physical-index moments together, WITHOUT identifying
physical-index weights with integration coordinates or Theta factors. -/
theorem first_round_total_physical_moment_actual :
    (∑ i : Fin 200, (i.val : ℤ) * iterate 1 true i) +
        (∑ i : Fin 200, (i.val : ℤ) * iterate 1 false i) =
      125597286337858911445366423 := by
  rw [first_round_physical_moment_actual, first_round_physical_moment_actual,
      first_round_upper_physical_moment_exact,
      first_round_lower_physical_moment_exact]
  norm_num

end
end ImbalancedChen.Part5OriginalH430FirstRoundPhysicalMassMoment
