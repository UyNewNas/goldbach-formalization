import ImbalancedChen.Part5OriginalH430StrictIncrementActualSources

/-!
P5.6 / h34: a genuine CHOSEN original Q80 physical winner, not an
arbitrary improving offer. The frozen producer uses strict (not weak)
updates: retention is the initial decision, the enabled Buchstab offer
is considered once, and only the UPPER table scans the original 106 bank
rows left-to-right, always against the same predecessor table.

This file propagates decision provenance through that actual scan and
proves a nonzero increment iff the FINAL selected choice is non-retained.
It identifies the exact winning Buchstab or bank integer numerator and
the actual positive DELTA. Unselected greater-than-old offers are not
summed and cannot become a second winner or a count payment.

This is a physical producer theorem, NOT original U3/U4 q/tag count
ownership or a complete CLOSED-CELL bound.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralUniqueStrictWinner
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430LiteralIncrementTelescope

/-- The actual numerator is never below the old cell. Every non-retained
choice remembers exactly ONE enabled original offer, which was strictly
greater than the old cell when selected. -/
def WinnerOrigin (old : Table) (upper : Bool)
    (i : Fin 200) (d : Decision) : Prop :=
  old upper i ≤ d.numerator ∧
  (d.choice = .retained → d.numerator = old upper i) ∧
  (d.choice = .buchstab →
    50 ≤ i.val ∧
    d.numerator =
      (if upper then suffix old false (max 50 (i.val - 49))
       else suffix old true (i.val - 49)) ∧
    old upper i < d.numerator) ∧
  (∀ k : Fin 106, d.choice = .bank k →
    upper = true ∧ i.val ∈ (rows k).targets ∧
    d.numerator = candidate old (rows k) ∧
    old upper i < d.numerator)

/-- The ORIGINAL ordinary decision either retains or strictly replaces
the old cell by the eligible opposite-table Buchstab suffix. -/
private theorem ordinary_origin (old : Table) (upper : Bool)
    (i : Fin 200) :
    WinnerOrigin old upper i (ordinaryDecision old upper i) := by
  by_cases h50 : 50 ≤ i.val
  · simp only [ordinaryDecision, if_pos h50]
    let v : ℤ :=
      if upper then suffix old false (max 50 (i.val - 49))
      else suffix old true (i.val - 49)
    change WinnerOrigin old upper i
      (offer ⟨old upper i, .retained⟩ v .buchstab)
    by_cases hv : old upper i < v
    · simp only [offer, if_pos hv]
      refine ⟨le_of_lt hv, ?_, ?_, ?_⟩
      · intro hr
        cases hr
      · intro hb
        exact ⟨h50, rfl, hv⟩
      · intro k hk
        cases hk
    · simp only [offer, if_neg hv]
      refine ⟨le_refl _, ?_, ?_, ?_⟩
      · intro _
        rfl
      · intro hb
        cases hb
      · intro k hk
        cases hk
  · simp only [ordinaryDecision, if_neg h50]
    change WinnerOrigin old upper i ⟨old upper i, .retained⟩
    refine ⟨le_refl _, ?_, ?_, ?_⟩
    · intro _
      rfl
    · intro hb
      cases hb
    · intro k hk
      cases hk

/-- A genuine targeted bank offer preserves the old decision unless its
integer numerator STRICTLY exceeds the current winning numerator. -/
private theorem bank_offer_origin (old : Table) (i : Fin 200)
    (d : Decision) (k : Fin 106)
    (hd : WinnerOrigin old true i d) :
    WinnerOrigin old true i (offerRow old i d k) := by
  by_cases ht : i.val ∈ (rows k).targets
  · by_cases hv : d.numerator < candidate old (rows k)
    · change WinnerOrigin old true i
        (offer d (candidate old (rows k)) (.bank k))
      simp only [offer, if_pos hv]
      refine ⟨hd.1.trans hv.le, ?_, ?_, ?_⟩
      · intro hr
        cases hr
      · intro hb
        cases hb
      · intro l hl
        have hkl : k = l := Choice.bank.inj hl
        subst l
        exact ⟨rfl, ht, rfl, lt_of_le_of_lt hd.1 hv⟩
    · simpa only [offerRow, if_pos ht, offer, if_neg hv] using hd
  · simpa only [offerRow, if_neg ht] using hd

/-- Provenance is preserved by the literal LEFT-TO-RIGHT 106-row scan;
no loser is added to the actual decision or to its numerator. -/
private theorem bank_scan_origin (old : Table) (i : Fin 200) :
    ∀ (ks : List (Fin 106)) (d : Decision),
      WinnerOrigin old true i d →
        WinnerOrigin old true i (scan old i ks d) := by
  intro ks
  induction ks with
  | nil =>
      intro d hd
      exact hd
  | cons k ks ih =>
      intro d hd
      change WinnerOrigin old true i
        (scan old i ks (offerRow old i d k))
      exact ih (offerRow old i d k)
        (bank_offer_origin old i d k hd)

/-- All three choices keep their ACTUAL data at a physical cell, including
the upper-only bank lane and the strict positive-delta condition. -/
theorem literal_round_winner_origin (old : Table)
    (upper : Bool) (i : Fin 200) :
    WinnerOrigin old upper i (roundDecision old upper i) := by
  cases upper with
  | false =>
      change WinnerOrigin old false i (ordinaryDecision old false i)
      exact ordinary_origin old false i
  | true =>
      change WinnerOrigin old true i
        (scan old i (List.finRange 106)
          (ordinaryDecision old true i))
      exact bank_scan_origin old i (List.finRange 106)
        (ordinaryDecision old true i)
        (ordinary_origin old true i)

/-- In the TRUE producer a cell changes strictly iff the FINAL chosen
action is not retention. Testing some unchosen offer is not payment. -/
theorem literal_round_strict_iff_chosen_nonretention
    (old : Table) (upper : Bool) (i : Fin 200) :
    old upper i < roundTable old upper i ↔
      (roundDecision old upper i).choice ≠ .retained := by
  have hs := literal_round_winner_origin old upper i
  constructor
  · intro hp hr
    have heq := hs.2.1 hr
    change old upper i < (roundDecision old upper i).numerator at hp
    omega
  · intro hn
    cases hc : (roundDecision old upper i).choice with
    | retained =>
        exact (hn hc).elim
    | buchstab =>
        exact (hs.2.2.1 hc).2.2
    | bank k =>
        exact (hs.2.2.2 k hc).2.2.2

/-- The final strict winner is either the SINGLE selected Buchstab
offer or the SINGLE selected, targeted upper bank row. Each winning
numerator equals the original corresponding candidate, not a sum. -/
theorem literal_round_strict_chosen_source (old : Table)
    (upper : Bool) (i : Fin 200)
    (hp : old upper i < roundTable old upper i) :
    ((roundDecision old upper i).choice = .buchstab ∧
      50 ≤ i.val ∧
      roundTable old upper i =
        (if upper then suffix old false (max 50 (i.val - 49))
         else suffix old true (i.val - 49))) ∨
    (upper = true ∧ ∃ k : Fin 106,
      (roundDecision old upper i).choice = .bank k ∧
      i.val ∈ (rows k).targets ∧
      roundTable old upper i = candidate old (rows k)) := by
  have hs := literal_round_winner_origin old upper i
  have hn := (literal_round_strict_iff_chosen_nonretention
    old upper i).1 hp
  cases hc : (roundDecision old upper i).choice with
  | retained =>
      exact (hn hc).elim
  | buchstab =>
      obtain ⟨hi, heq, _⟩ := hs.2.2.1 hc
      exact Or.inl ⟨hc, hi, heq⟩
  | bank k =>
      obtain ⟨hu, ht, heq, _⟩ := hs.2.2.2 k hc
      exact Or.inr ⟨hu, k, hc, ht, heq⟩

/-- One actual original generation has zero added numerator precisely
when its FINAL action is retention. A losing offer never creates a
positive increment in this ledger. -/
theorem actual_increment_zero_iff_retained (g : Fin 430)
    (upper : Bool) (i : Fin 200) :
    literalIncrement g.val upper i = 0 ↔
      (roundDecision (iterate g.val) upper i).choice = .retained := by
  have hnonneg := literal_increment_nonneg g.val upper i
  constructor
  · intro hz
    by_contra hn
    have hp := (literal_round_strict_iff_chosen_nonretention
      (iterate g.val) upper i).2 hn
    unfold literalIncrement at hz
    change iterate (g.val + 1) upper i - iterate g.val upper i = 0 at hz
    change iterate g.val upper i <
      iterate (g.val + 1) upper i at hp
    omega
  · intro hr
    have heq := (literal_round_winner_origin
      (iterate g.val) upper i).2.1 hr
    unfold literalIncrement
    change roundTable (iterate g.val) upper i -
      iterate g.val upper i = 0
    rw [heq]
    ring

/-- The exact, integer-valued Q80 increment is attributed ONLY to the
selected winning original offer. This identifies physical provenance,
not any U3/U4 arithmetic root, owner, weight or acceptance filter. -/
theorem actual_positive_increment_exact_chosen_delta
    (g : Fin 430) (upper : Bool) (i : Fin 200)
    (hpos : 0 < literalIncrement g.val upper i) :
    ((roundDecision (iterate g.val) upper i).choice = .buchstab ∧
      50 ≤ i.val ∧
      literalIncrement g.val upper i =
        (if upper then
           suffix (iterate g.val) false (max 50 (i.val - 49))
         else suffix (iterate g.val) true (i.val - 49)) -
          iterate g.val upper i) ∨
    (upper = true ∧ ∃ k : Fin 106,
      (roundDecision (iterate g.val) upper i).choice = .bank k ∧
      i.val ∈ (rows k).targets ∧
      literalIncrement g.val upper i =
        candidate (iterate g.val) (rows k) -
          iterate g.val upper i) := by
  have hp : iterate g.val upper i <
      roundTable (iterate g.val) upper i := by
    unfold literalIncrement at hpos
    change 0 < roundTable (iterate g.val) upper i -
      iterate g.val upper i at hpos
    omega
  rcases literal_round_strict_chosen_source
      (iterate g.val) upper i hp with
      ⟨hc, hi, heq⟩ | ⟨hu, k, hc, ht, heq⟩
  · left
    refine ⟨hc, hi, ?_⟩
    unfold literalIncrement
    change roundTable (iterate g.val) upper i -
      iterate g.val upper i = _
    rw [heq]
  · right
    refine ⟨hu, k, hc, ht, ?_⟩
    unfold literalIncrement
    change roundTable (iterate g.val) upper i -
      iterate g.val upper i = _
    rw [heq]

end
end ImbalancedChen.Part5OriginalH430LiteralUniqueStrictWinner
