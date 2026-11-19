import ImbalancedChen.Part5OriginalH430FirstFailureNonretained

/-!
P5.6 / h34: an unconditional support theorem for the ORIGINAL Q80
producer, not an arbitrary table recurrence.

The initial lower table is zero. Its first 50 cells have ONLY the
retention transition at every generation, since Buchstab is disabled
there and the 106-bank scan is upper-only. They consequently remain
zero for ALL original generations. In round one the lower table can
be nonzero only at literal indices 50..108: every later suffix starts
past the first-60 upper seed. The first upper ordinary decision is
retained, not Buchstab, so its only possible new round-one actions
are the original targeted 106 bank candidates.

These are exact integer Q80 facts. No positive bank/suffix estimate,
analytic F base, U3/U4 count identity, PP input or h34 conclusion is
asserted. SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430Q80InitialSupport
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (q logWeights)
open Part5OriginalUpsilon5CausalDictionary (floorValue)

/-- The ORIGINAL literal lower seed is zero at every physical cell. -/
theorem initial_lower_read_zero (j : ℕ) :
    read seed false j = 0 := by
  by_cases hj : j < 200
  · simp [read, hj, seed]
  · simp [read, hj]

/-- At the first update, an upper Buchstab offer reads only the old
lower table, which is literally zero, including integer quotient. -/
theorem initial_upper_buchstab_suffix_zero (k : ℕ) :
    suffix seed false k = 0 := by
  simp [suffix, initial_lower_read_zero]

private theorem initial_upper_numerator_nonneg (i : Fin 200) :
    0 ≤ seed true i := by
  by_cases hi : i.val < 60
  · norm_num [seed, q, hi]
  · simp [seed, hi]

/-- The literal upper ordinary decision in round one has RETAINED
provenance: its candidate Buchstab value is exactly zero. This is
stronger than just a bound on its numerator. -/
theorem first_upper_ordinary_is_retained (i : Fin 200) :
    ordinaryDecision seed true i =
      ⟨seed true i, Choice.retained⟩ := by
  by_cases hi : 50 ≤ i.val
  · simp [ordinaryDecision, hi, initial_upper_buchstab_suffix_zero,
      offer, not_lt_of_ge (initial_upper_numerator_nonneg i)]
  · simp [ordinaryDecision, hi]

/-- Original first upper update: precisely the existing targeted
106-bank scan starting from the retained seed. No phantom first
Buchstab payment is included. -/
theorem first_upper_round_is_exact_bank_scan (i : Fin 200) :
    iterate 1 true i =
      (scan seed i (List.finRange 106)
        ⟨seed true i, Choice.retained⟩).numerator := by
  change (scan seed i (List.finRange 106)
    (ordinaryDecision seed true i)).numerator = _
  rw [first_upper_ordinary_is_retained]

/-- All lower-table cells below literal index 50 are identically ZERO
at EVERY generation, including 430. This uses the authentic upper-only
bank and the literal 50 cutoff, not an induction hypothesis asserting
CLOSED-CELL. -/
theorem lower_first_fifty_zero (g : ℕ) (i : Fin 200)
    (hi : i.val < 50) : iterate g false i = 0 := by
  induction g with
  | zero =>
      simp [iterate, seed]
  | succ g ih =>
      change (ordinaryDecision (iterate g) false i).numerator = 0
      rw [ordinaryDecision_numerator]
      have hnot : ¬ 50 ≤ i.val := by omega
      simpa only [if_neg hnot] using ih

theorem lower_first_fifty_floor_zero (g : ℕ) (i : Fin 200)
    (hi : i.val < 50) :
    floorValue (iterate g false) i = 0 := by
  simp [floorValue, lower_first_fifty_zero g i hi]

/-- The first upper seed has no nonzero read from index 60 onward;
this checks the real 200-cell read with out-of-range zero semantics. -/
theorem initial_upper_read_zero_from_sixty (j : ℕ)
    (hj : 60 ≤ j) : read seed true j = 0 := by
  by_cases hj200 : j < 200
  · have hnot : ¬ j < 60 := by omega
    simp [read, hj200, seed, hnot]
  · simp [read, hj200]

/-- Every original upper-seed suffix starting at 60 or later is zero,
using the full literal logWeights vector and the SAME q. -/
theorem initial_lower_buchstab_suffix_zero_from_sixty (k : ℕ)
    (hk : 60 ≤ k) : suffix seed true k = 0 := by
  unfold suffix
  have hs : (∑ r ∈ Finset.range (200 - k),
      read seed true (k + r) *
        (if hj : k + r < 200 then
          logWeights ⟨k + r, hj⟩ else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [initial_upper_read_zero_from_sixty (k + r) (by omega)]
    simp
  rw [hs]
  simp

/-- The ORIGINAL lower table has no round-one support at indices
109..199. Its Buchstab read starts at i-49 >=60, outside the seed. -/
theorem first_lower_tail_zero (i : Fin 200)
    (hi : 109 ≤ i.val) : iterate 1 false i = 0 := by
  change (ordinaryDecision seed false i).numerator = 0
  rw [ordinaryDecision_numerator]
  have h50 : 50 ≤ i.val := by omega
  have hk : 60 ≤ i.val - 49 := by omega
  simp [h50, seed,
    initial_lower_buchstab_suffix_zero_from_sixty (i.val - 49) hk]

/-- Exact structural first-generation lower support, with no invented
additional kernel or source family. Nothing is claimed about whether
an individual index 50..108 is actually positive. -/
theorem first_lower_nonzero_only_in_fifty_to_108 (i : Fin 200)
    (hnonzero : iterate 1 false i ≠ 0) :
    50 ≤ i.val ∧ i.val < 109 := by
  constructor
  · by_contra h
    exact hnonzero (lower_first_fifty_zero 1 i (by omega))
  · by_contra h
    exact hnonzero (first_lower_tail_zero i (by omega))

/-- The lower first-50 CLOSED-CELL obligation at EVERY round follows
from ONLY the actual generation-zero F bound. It is an unconditional
producer invariant, not the still-unpaid remaining 350-cell induction. -/
theorem lower_first_fifty_closed_cell_from_seed
    (F : Bool → ℝ → ℝ)
    (hseed : ∀ (i : Fin 200) (s : ℝ),
      i.val < 50 → s ∈ queryCell i →
        floorValue (iterate 0 false) i ≤ F false s) :
    ∀ (g : ℕ) (i : Fin 200) (s : ℝ),
      i.val < 50 → s ∈ queryCell i →
        floorValue (iterate g false) i ≤ F false s := by
  intro g i s hi hs
  have hF : (0 : ℝ) ≤ F false s := by
    have h := hseed i s hi hs
    rw [lower_first_fifty_floor_zero 0 i hi] at h
    exact h
  rw [lower_first_fifty_floor_zero g i hi]
  exact hF

end
end ImbalancedChen.Part5OriginalH430Q80InitialSupport
