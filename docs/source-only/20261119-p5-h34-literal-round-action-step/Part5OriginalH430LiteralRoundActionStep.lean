import ImbalancedChen.Part5OriginalH430PrefixClosedCellWinningBudget

/-!
P5.6 / h34: an ACTUAL Q80 numerator-level successor rule for the pinned
430-round producer. This is the missing literal predecessor-to-successor
decomposition, not the final CLOSED-CELL induction.

At each cell, the actual round chooses a maximum of retention, its actual
Buchstab suffix (when enabled), and targeted ORIGINAL 106-bank candidates
ONLY on the upper table. The proofs below expose the three precise
inequalities sufficient for a one-round ceiling, and a converse overflow
witness identifying which un-paid channel must exceed the ceiling.
No fabricated fourth action, scalar bank owner, arithmetic q/tag licence,
new threshold, proof escape, or analytic input is introduced.

A real closed-cell consequence is obtained only if a separate integer
ceiling and its real cellwise envelope are genuinely supplied. Their
existence/payment is NOT proved here. The original 430+11 h34 closure,
base/seed, Buchstab/bank positive budgets, U3/U4 source, PP/same-rho
and native-history remain open.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralRoundActionStep
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (rows)
open Part5OriginalUpsilon5CausalDictionary (floorValue)

/-- The original offer changes the numerator only by a maximum.
No symbolic action is added to the literal choice type. -/
private theorem offer_numerator_le_ceiling
    (d : Decision) (v bound : ℤ) (c : Choice)
    (hd : d.numerator ≤ bound) (hv : v ≤ bound) :
    (offer d v c).numerator ≤ bound := by
  rw [offer_numerator]
  exact max_le hd hv

/-- When a bank row is not actually targeted at the cell, its candidate
does not participate in the round. A targeted row uses the original
integer quotient and the actual 106-row table. -/
private theorem offerRow_numerator_le_ceiling
    (old : Table) (i : Fin 200) (d : Decision)
    (k : Fin 106) (bound : ℤ)
    (hd : d.numerator ≤ bound)
    (hk : i.val ∈ (rows k).targets →
      candidate old (rows k) ≤ bound) :
    (offerRow old i d k).numerator ≤ bound := by
  by_cases ht : i.val ∈ (rows k).targets
  · simpa only [offerRow, if_pos ht] using
      (offer_numerator_le_ceiling d (candidate old (rows k))
        bound (.bank k) hd (hk ht))
  · simpa only [offerRow, if_neg ht] using hd

/-- This induction is over the exact left-to-right bank scan, and
never sums unchosen candidates as if they had been paid. -/
private theorem scan_numerator_le_ceiling
    (old : Table) (i : Fin 200) (bound : ℤ) :
    ∀ (ks : List (Fin 106)) (d : Decision),
      d.numerator ≤ bound →
      (∀ k, k ∈ ks → i.val ∈ (rows k).targets →
        candidate old (rows k) ≤ bound) →
      (scan old i ks d).numerator ≤ bound := by
  intro ks
  induction ks with
  | nil =>
      intro d hd _
      simpa only [scan] using hd
  | cons k ks ih =>
      intro d hd hrows
      change (scan old i ks (offerRow old i d k)).numerator ≤ bound
      apply ih (offerRow old i d k)
      · exact offerRow_numerator_le_ceiling old i d k bound hd
          (hrows k (by simp))
      · intro j hj ht
        exact hrows j (by simp [hj]) ht

/-- The authentic retention/Buchstab decision, including the upper
max-50 cutoff and lower offset, is bounded without a changed suffix. -/
private theorem ordinary_numerator_le_ceiling
    (old : Table) (upper : Bool) (i : Fin 200) (bound : ℤ)
    (hret : old upper i ≤ bound)
    (hbuch : 50 ≤ i.val →
      (if upper then suffix old false (max 50 (i.val - 49))
       else suffix old true (i.val - 49)) ≤ bound) :
    (ordinaryDecision old upper i).numerator ≤ bound := by
  rw [ordinaryDecision_numerator]
  by_cases h50 : 50 ≤ i.val
  · simp only [if_pos h50]
    exact max_le hret (hbuch h50)
  · simpa only [if_neg h50] using hret

/-- EXACT producer-specific one-round CLOSED-CELL numerator step:
retention and the true Buchstab branch in BOTH tables, and all original
targeted 106-bank offers in the UPPER table. Bank candidate bounds are
checks, NOT additional mass charges for unselected alternatives. -/
theorem literal_round_le_of_three_action_bounds
    (old : Table) (upper : Bool) (i : Fin 200) (bound : ℤ)
    (hret : old upper i ≤ bound)
    (hbuch : 50 ≤ i.val →
      (if upper then suffix old false (max 50 (i.val - 49))
       else suffix old true (i.val - 49)) ≤ bound)
    (hbank : upper = true →
      ∀ k : Fin 106, i.val ∈ (rows k).targets →
        candidate old (rows k) ≤ bound) :
    roundTable old upper i ≤ bound := by
  cases upper with
  | false =>
      change (ordinaryDecision old false i).numerator ≤ bound
      exact ordinary_numerator_le_ceiling old false i bound hret hbuch
  | true =>
      change (scan old i (List.finRange 106)
        (ordinaryDecision old true i)).numerator ≤ bound
      apply scan_numerator_le_ceiling old i bound
        (List.finRange 106) (ordinaryDecision old true i)
      · exact ordinary_numerator_le_ceiling old true i bound hret hbuch
      · intro k _ ht
        exact hbank rfl k ht

/-- All candidate-branch inequalities are genuine manuscript-internal
tasks: this theorem supplies the actual g to g+1 Q80 step once they
are established at the SAME predecessor table. No hypothetical h34
counting theorem or all-430 closure hypothesis occurs. -/
theorem actual_iterate_succ_le_integer_ceiling
    (g : Fin 430) (ceiling : Table)
    (hret : ∀ upper i,
      iterate g.val upper i ≤ ceiling upper i)
    (hbuch : ∀ upper i, 50 ≤ i.val →
      (if upper then
         suffix (iterate g.val) false (max 50 (i.val - 49))
       else suffix (iterate g.val) true (i.val - 49)) ≤
        ceiling upper i)
    (hbank : ∀ i : Fin 200, ∀ k : Fin 106,
      i.val ∈ (rows k).targets →
        candidate (iterate g.val) (rows k) ≤ ceiling true i) :
    ∀ upper i, iterate (g.val + 1) upper i ≤ ceiling upper i := by
  intro upper i
  change roundTable (iterate g.val) upper i ≤ ceiling upper i
  apply literal_round_le_of_three_action_bounds
    (iterate g.val) upper i (ceiling upper i)
    (hret upper i) (hbuch upper i)
  intro hu k ht
  subst upper
  exact hbank i k ht

/-- A strict overflow at the next REAL Q80 iteration cannot appear out
of nowhere. It has a literal predecessor, Buchstab, or targeted upper
106-bank candidate witness. This is not an assertion that an overflow
actually occurs; it isolates exactly the unproved positive-source checks. -/
theorem literal_round_overflow_has_actual_action_witness
    (old : Table) (upper : Bool) (i : Fin 200) (bound : ℤ)
    (hexcess : bound < roundTable old upper i) :
    bound < old upper i ∨
    (50 ≤ i.val ∧ bound <
      (if upper then suffix old false (max 50 (i.val - 49))
       else suffix old true (i.val - 49))) ∨
    (upper = true ∧ ∃ k : Fin 106,
      i.val ∈ (rows k).targets ∧ bound < candidate old (rows k)) := by
  by_contra hnone
  have hret : old upper i ≤ bound :=
    le_of_not_gt (fun hgt => hnone (Or.inl hgt))
  have hbuch : 50 ≤ i.val →
      (if upper then suffix old false (max 50 (i.val - 49))
       else suffix old true (i.val - 49)) ≤ bound := by
    intro h50
    exact le_of_not_gt (fun hgt =>
      hnone (Or.inr (Or.inl ⟨h50, hgt⟩)))
  have hbank : upper = true →
      ∀ k : Fin 106, i.val ∈ (rows k).targets →
        candidate old (rows k) ≤ bound := by
    intro hu k ht
    exact le_of_not_gt (fun hgt =>
      hnone (Or.inr (Or.inr ⟨hu, k, ht, hgt⟩)))
  have hlimit :=
    literal_round_le_of_three_action_bounds old upper i bound
      hret hbuch hbank
  exact (not_lt_of_ge hlimit) hexcess

theorem actual_iteration_overflow_has_action_witness
    (g : Fin 430) (upper : Bool) (i : Fin 200) (bound : ℤ)
    (hexcess : bound < iterate (g.val + 1) upper i) :
    bound < iterate g.val upper i ∨
    (50 ≤ i.val ∧ bound <
      (if upper then
         suffix (iterate g.val) false (max 50 (i.val - 49))
       else suffix (iterate g.val) true (i.val - 49))) ∨
    (upper = true ∧ ∃ k : Fin 106,
      i.val ∈ (rows k).targets ∧
        bound < candidate (iterate g.val) (rows k)) := by
  change bound < roundTable (iterate g.val) upper i at hexcess
  exact literal_round_overflow_has_actual_action_witness
    (iterate g.val) upper i bound hexcess

/-- The Q80 scale is unchanged (2^80); no unit clipping or new
normalization is inserted in the integer-to-closed-cell transfer. -/
theorem floorValue_le_of_integer_ceiling
    (nums ceiling : Fin 200 → ℤ) (i : Fin 200)
    (h : nums i ≤ ceiling i) :
    floorValue nums i ≤ floorValue ceiling i := by
  change (nums i : ℝ) / (2 ^ 80 : ℝ) ≤
    (ceiling i : ℝ) / (2 ^ 80 : ℝ)
  have hc : (nums i : ℝ) ≤ (ceiling i : ℝ) := by
    exact_mod_cast h
  exact div_le_div_of_nonneg_right hc (by positivity)

/-- True one-round CLOSED-CELL consequence at the ORIGINAL query cells.
The explicit bank/suffix ceiling obligations and the physical real
envelope are still owed; they are not replaced by a postulated final
CLOSED-CELL or by an original U3/U4 count licence. -/
theorem actual_succ_closed_cell_of_literal_action_ceiling
    (g : Fin 430) (ceiling : Table)
    (F : Bool → ℝ → ℝ)
    (hret : ∀ upper i,
      iterate g.val upper i ≤ ceiling upper i)
    (hbuch : ∀ upper i, 50 ≤ i.val →
      (if upper then
         suffix (iterate g.val) false (max 50 (i.val - 49))
       else suffix (iterate g.val) true (i.val - 49)) ≤
        ceiling upper i)
    (hbank : ∀ i : Fin 200, ∀ k : Fin 106,
      i.val ∈ (rows k).targets →
        candidate (iterate g.val) (rows k) ≤ ceiling true i)
    (hcell : ∀ upper (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (ceiling upper) i ≤ F upper s) :
    ∀ upper (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate (g.val + 1) upper) i ≤ F upper s := by
  intro upper i s hs
  have hnext := actual_iterate_succ_le_integer_ceiling
    g ceiling hret hbuch hbank upper i
  exact (floorValue_le_of_integer_ceiling
    (iterate (g.val + 1) upper) (ceiling upper) i hnext).trans
      (hcell upper i s hs)

end
end ImbalancedChen.Part5OriginalH430LiteralRoundActionStep
