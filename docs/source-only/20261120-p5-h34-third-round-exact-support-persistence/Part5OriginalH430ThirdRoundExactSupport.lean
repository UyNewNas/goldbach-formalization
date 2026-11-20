import ImbalancedChen.Part5OriginalH430ThirdRoundExterior91

/-!
P5.6/h34: exact ORIGINAL third-generation support and persistence.
The previous 91 exterior receipts plus the genuine 400-cell second-round
receipts now establish POSITIVITY at all 343 possible third-round sites.
Retention in the literal original Q80 producer propagates those 343
positive numerator sites through each later generation (in particular 430).
This is a physical-support statement only; it is NOT U3/U4 selected count,
F-envelope payment, PP/same-rho or the original h34 theorem.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ThirdRoundExactSupport
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430ThirdRoundExterior91
open Part5OriginalH430SecondRoundComplete400
open Part5OriginalH430SecondRoundExteriorSources

/-- Every authentic bank offer keeps at least its preceding decision
numerator; the 106-row scan is NOT a sum of mutually exclusive actions. -/
private theorem actual_offerRow_ge (old : Table) (i : Fin 200)
    (d : Decision) (k : Fin 106) :
    d.numerator ≤ (offerRow old i d k).numerator := by
  by_cases ht : i.val ∈ (P2Selected430LiteralActionData.rows k).targets
  · simpa [offerRow, ht, offer_numerator] using
      (le_max_left d.numerator
        (candidate old (P2Selected430LiteralActionData.rows k)))
  · simp [offerRow, ht]

private theorem actual_scan_ge (old : Table) (i : Fin 200)
    (ks : List (Fin 106)) (d : Decision) :
    d.numerator ≤ (scan old i ks d).numerator := by
  induction ks generalizing d with
  | nil =>
      rfl
  | cons k ks ih =>
      change d.numerator ≤
        (scan old i ks (offerRow old i d k)).numerator
      exact (actual_offerRow_ge old i d k).trans (ih _)

/-- Retention is an actual option in both original tables. Upper-bank
strict tie choices do not change this numerical order. -/
theorem original_round_retains (old : Table) (upper : Bool)
    (i : Fin 200) :
    old upper i ≤ roundTable old upper i := by
  have hordinary :
      old upper i ≤ (ordinaryDecision old upper i).numerator := by
    rw [ordinaryDecision_numerator]
    by_cases h50 : 50 ≤ i.val
    · simp only [if_pos h50]
      exact le_max_left _ _
    · simpa only [if_neg h50] using (le_refl (old upper i))
  cases upper with
  | false =>
      change old false i ≤ (ordinaryDecision old false i).numerator
      exact hordinary
  | true =>
      change old true i ≤
        (scan old i (List.finRange 106)
          (ordinaryDecision old true i)).numerator
      exact hordinary.trans
        (actual_scan_ge old i (List.finRange 106)
          (ordinaryDecision old true i))

/-- True per-cell retention through each original Q80 generation;
no altered update rule or substituted real-valued model. -/
theorem original_iterate_succ_ge (g : ℕ) (upper : Bool)
    (i : Fin 200) :
    iterate g upper i ≤ iterate (g + 1) upper i := by
  change iterate g upper i ≤ roundTable (iterate g) upper i
  exact original_round_retains (iterate g) upper i

theorem original_iterate_le_of_le (m n : ℕ) (hmn : m ≤ n)
    (upper : Bool) (i : Fin 200) :
    iterate m upper i ≤ iterate n upper i := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
      exact ih.trans (original_iterate_succ_ge n upper i)

/-- These 100 values are the previous exact generation-two UPPER
interior receipts (not 100 newly invented positive-source payments). -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem second_upper_interior_100_positive (j : Fin 100) :
    0 < secondUpperInterior100 j := by
  fin_cases j <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem second_lower_interior_59_positive (j : Fin 59) :
    0 < secondLowerInterior59 j := by
  fin_cases j <;> decide

/-- All 158 genuine second-round upper active sites have positive
literal Q80 numerators. -/
theorem second_upper_inside_158_positive (i : Fin 200)
    (hi : i.val < 158) : 0 < iterate 2 true i := by
  rw [second_round_all_400_exact]
  by_cases h100 : i.val < 100
  · have h := second_upper_interior_100_positive
        (⟨i.val, h100⟩ : Fin 100)
    simpa [secondRoundExactReceipts, h100] using h
  · have hj : i.val - 100 < 58 := by omega
    have h := upper_new_58_positive
        (⟨i.val - 100, hj⟩ : Fin 58)
    simpa [secondRoundExactReceipts, h100, hi] using h

/-- All 94 genuine second-round lower sites 50..143 are positive. -/
theorem second_lower_inside_50_144_positive (i : Fin 200)
    (h50 : 50 ≤ i.val) (h144 : i.val < 144) :
    0 < iterate 2 false i := by
  rw [second_round_all_400_exact]
  by_cases h109 : i.val < 109
  · have hj : i.val - 50 < 59 := by omega
    have h := second_lower_interior_59_positive
        (⟨i.val - 50, hj⟩ : Fin 59)
    simpa [secondRoundExactReceipts, h50, h109] using h
  · have hj : i.val - 109 < 35 := by omega
    have h := lower_new_35_positive
        (⟨i.val - 109, hj⟩ : Fin 35)
    simpa [secondRoundExactReceipts, h50, h109, h144] using h

/-- Every upper site below 193 is genuinely positive in generation
three: the old 158 survive retention, and the new 35 use real suffixes. -/
theorem third_upper_inside_193_positive (i : Fin 200)
    (hi : i.val < 193) : 0 < iterate 3 true i := by
  by_cases h158 : i.val < 158
  · exact (second_upper_inside_158_positive i h158).trans_le
      (original_iterate_succ_ge 2 true i)
  · have hj : i.val - 158 < 35 := by omega
    have h := third_upper_new_35_genuinely_active
      (⟨i.val - 158, hj⟩ : Fin 35)
    have heq :
        (⟨158 + (i.val - 158), by omega⟩ : Fin 200) = i := by
      apply Fin.ext
      dsimp
      omega
    simpa only [heq] using h

/-- Every lower physical site from 50 onward is genuinely positive
at generation three: 94 retained and 56 new authentic suffixes. -/
theorem third_lower_from_50_positive (i : Fin 200)
    (h50 : 50 ≤ i.val) : 0 < iterate 3 false i := by
  by_cases h144 : i.val < 144
  · exact (second_lower_inside_50_144_positive i h50 h144).trans_le
      (original_iterate_succ_ge 2 false i)
  · have hj : i.val - 144 < 56 := by omega
    have h := third_lower_new_56_genuinely_active
      (⟨i.val - 144, hj⟩ : Fin 56)
    have heq :
        (⟨144 + (i.val - 144), by omega⟩ : Fin 200) = i := by
      apply Fin.ext
      dsimp
      omega
    simpa only [heq] using h

/-- This upgrades the previous upper-bound-only support theorem to a
FULL IFF for the actual 400-cell third-generation Q80 producer. -/
theorem third_round_nonzero_iff_physical (upper : Bool) (i : Fin 200) :
    iterate 3 upper i ≠ 0 ↔
      (upper = true ∧ i.val < 193) ∨
      (upper = false ∧ 50 ≤ i.val) := by
  constructor
  · exact third_round_nonzero_support upper i
  · intro h
    rcases h with ⟨hu, hi⟩ | ⟨hu, hi⟩
    · subst upper
      exact ne_of_gt (third_upper_inside_193_positive i hi)
    · subst upper
      exact ne_of_gt (third_lower_from_50_positive i hi)

private theorem third_upper_nonzero_iff (i : Fin 200) :
    iterate 3 true i ≠ 0 ↔ i.val < 193 := by
  constructor
  · intro h
    rcases (third_round_nonzero_iff_physical true i).mp h with
      ⟨_, hi⟩ | ⟨hfalse, _⟩
    · exact hi
    · cases hfalse
  · intro hi
    exact ne_of_gt (third_upper_inside_193_positive i hi)

private theorem third_lower_nonzero_iff (i : Fin 200) :
    iterate 3 false i ≠ 0 ↔ 50 ≤ i.val := by
  constructor
  · intro h
    rcases (third_round_nonzero_iff_physical false i).mp h with
      ⟨htrue, _⟩ | ⟨_, hi⟩
    · cases htrue
    · exact hi
  · intro hi
    exact ne_of_gt (third_lower_from_50_positive i hi)

/-- EXACTLY 193+150=343 physical cells carry a nonzero integer
numerator in the TRUE third Q80 generation. This is emphatically not
343 selected source occurrences, invoices, or arithmetic count weight. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem third_round_exactly_343_nonzero_physical_cells :
    (∑ i : Fin 200,
      if iterate 3 true i ≠ 0 then (1 : ℕ) else 0) +
    (∑ i : Fin 200,
      if iterate 3 false i ≠ 0 then (1 : ℕ) else 0) = 343 := by
  simp_rw [third_upper_nonzero_iff, third_lower_nonzero_iff]
  decide

/-- Authentic retention forces all 343 sites present at generation 3
to stay positive at every later generation, including the literal 430.
This is a LOWER support inclusion, not an analytic CLOSED-CELL bound. -/
theorem third_support_persists (g : ℕ) (hg : 3 ≤ g)
    (upper : Bool) (i : Fin 200)
    (hsite : (upper = true ∧ i.val < 193) ∨
             (upper = false ∧ 50 ≤ i.val)) :
    0 < iterate g upper i := by
  have h3 : 0 < iterate 3 upper i := by
    rcases hsite with ⟨hu, hi⟩ | ⟨hu, hi⟩
    · subst upper
      exact third_upper_inside_193_positive i hi
    · subst upper
      exact third_lower_from_50_positive i hi
  exact h3.trans_le (original_iterate_le_of_le 3 g hg upper i)

end
end ImbalancedChen.Part5OriginalH430ThirdRoundExactSupport
