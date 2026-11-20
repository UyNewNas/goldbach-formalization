import ImbalancedChen.Part5OriginalH430LiteralUniqueStrictWinner

/-!
P5.6 / h34: one-payment partition of the ORIGINAL 430-round physical
Q80 numerator changes by the FINAL chosen action.

The same roundDecision, iterate, strict scan and 106 bank indices are
used; no offered-but-losing bank row receives mass. This is a
PHYSICAL CHOICE ledger, NOT original U3/U4 q/tag arithmetic owner,
root weight, full/selected/inherited gate, rejected lane, or CLOSED-CELL
count proof. The frozen manuscript's own count correspondence remains
unproved. SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ChosenPhysicalPaymentPartition
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430LiteralIncrementTelescope
open Part5OriginalH430LiteralUniqueStrictWinner

/-- The exact current-cell integer increment, charged only if the
original FINAL winning choice is Buchstab. -/
def buchstabPaid (g : ℕ) (upper : Bool) (i : Fin 200) : ℤ :=
  if (roundDecision (iterate g) upper i).choice = .buchstab
  then literalIncrement g upper i else 0

/-- A bank payment has an index in the original 106-row list. A row
that loses the strict final scan gets zero, even if it improved on the
old predecessor cell. Bank payments exist only on the upper table. -/
def bankPaid (g : ℕ) (i : Fin 200) (k : Fin 106) : ℤ :=
  if (roundDecision (iterate g) true i).choice = .bank k
  then literalIncrement g true i else 0

/-- Retention contains no increment, without assuming it as a new
source-licence. This holds for ANY generation of the original producer. -/
private theorem retained_increment_zero (g : ℕ)
    (upper : Bool) (i : Fin 200)
    (hr : (roundDecision (iterate g) upper i).choice = .retained) :
    literalIncrement g upper i = 0 := by
  have h := (literal_round_winner_origin (iterate g) upper i).2.1 hr
  unfold literalIncrement
  change (roundDecision (iterate g) upper i).numerator -
    iterate g upper i = 0
  rw [h]
  ring

/-- A single ORIGINAL upper cell has exactly one winner's integer
increase: Buchstab or at most ONE indexed winning bank row. No other
bank candidate is charged, and retained mass contributes zero. -/
theorem upper_cell_chosen_partition (g : ℕ) (i : Fin 200) :
    literalIncrement g true i =
      buchstabPaid g true i + ∑ k : Fin 106, bankPaid g i k := by
  cases hc : (roundDecision (iterate g) true i).choice with
  | retained =>
      have hz := retained_increment_zero g true i hc
      simp [buchstabPaid, bankPaid, hc, hz]
  | buchstab =>
      simp [buchstabPaid, bankPaid, hc]
  | bank k =>
      simp [buchstabPaid, bankPaid, hc]

/-- A genuine lower-table increment is entirely Buchstab: the
literal lower producer NEVER scans the upper-only bank rows. -/
theorem lower_cell_chosen_partition (g : ℕ) (i : Fin 200) :
    literalIncrement g false i = buchstabPaid g false i := by
  cases hc : (roundDecision (iterate g) false i).choice with
  | retained =>
      have hz := retained_increment_zero g false i hc
      simp [buchstabPaid, hc, hz]
  | buchstab =>
      simp [buchstabPaid, hc]
  | bank k =>
      have hfalse :=
        ((literal_round_winner_origin (iterate g) false i).2.2.2 k hc).1
      cases hfalse

/-- A NONZERO bank payment identifies its authentic target and its
exact old-to-new winning numerator difference, not an arbitrary offer. -/
theorem bank_paid_authentic_target (g : ℕ) (i : Fin 200)
    (k : Fin 106) (hn : bankPaid g i k ≠ 0) :
    i.val ∈ (rows k).targets ∧
      bankPaid g i k =
        candidate (iterate g) (rows k) - iterate g true i := by
  have hc : (roundDecision (iterate g) true i).choice = .bank k := by
    by_contra hnot
    exact hn (by simp [bankPaid, hnot])
  have ho := (literal_round_winner_origin (iterate g) true i).2.2.2 k hc
  refine ⟨ho.2.1, ?_⟩
  simp only [bankPaid, if_pos hc]
  unfold literalIncrement
  change (roundDecision (iterate g) true i).numerator -
    iterate g true i = _
  rw [ho.2.2.1]

/-- No two distinct bank rows can both own a nonzero payment
at the same generation and physical upper cell. -/
theorem bank_paid_unique_index (g : ℕ) (i : Fin 200)
    (k l : Fin 106) (hk : bankPaid g i k ≠ 0)
    (hl : bankPaid g i l ≠ 0) : k = l := by
  have ck : (roundDecision (iterate g) true i).choice = .bank k := by
    by_contra hn
    exact hk (by simp [bankPaid, hn])
  have cl : (roundDecision (iterate g) true i).choice = .bank l := by
    by_contra hn
    exact hl (by simp [bankPaid, hn])
  exact Choice.bank.inj (ck.symm.trans cl)

/-- Buchstab and bank cannot both receive nonzero credit from
one upper physical site in one round. -/
theorem buchstab_bank_payment_disjoint (g : ℕ) (i : Fin 200)
    (k : Fin 106) (hb : buchstabPaid g true i ≠ 0) :
    bankPaid g i k = 0 := by
  have hc : (roundDecision (iterate g) true i).choice = .buchstab := by
    by_contra hn
    exact hb (by simp [buchstabPaid, hn])
  simp [bankPaid, hc]

/-- Per-entry nonnegativity is inherited from original Q80 retention,
not a new assumed positivity for the winning source. -/
theorem bank_paid_nonneg (g : ℕ) (i : Fin 200)
    (k : Fin 106) : 0 ≤ bankPaid g i k := by
  unfold bankPaid
  split_ifs
  · exact literal_increment_nonneg g true i
  · omega

theorem buchstab_paid_nonneg (g : ℕ) (upper : Bool)
    (i : Fin 200) : 0 ≤ buchstabPaid g upper i := by
  unfold buchstabPaid
  split_ifs
  · exact literal_increment_nonneg g upper i
  · omega

/-- The complete 430-round UPPER physical growth account, partitioned
without charging any defeated bank row or any retained old mass. -/
theorem upper_430_chosen_account :
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       literalIncrement g true i) =
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       buchstabPaid g true i) +
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       ∑ k : Fin 106, bankPaid g i k) := by
  simp_rw [upper_cell_chosen_partition, Finset.sum_add_distrib]

/-- The complete lower table has no bank lane. -/
theorem lower_430_chosen_account :
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       literalIncrement g false i) =
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       buchstabPaid g false i) := by
  simp_rw [lower_cell_chosen_partition]

/-- The original two-table raw Q80 telescope is now exactly split into
the chosen Buchstab payments and chosen upper bank-row payments.
This is still NOT a selected-count equality. -/
theorem full_430_chosen_physical_account :
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       literalIncrement g true i) +
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       literalIncrement g false i) =
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       buchstabPaid g true i) +
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       buchstabPaid g false i) +
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       ∑ k : Fin 106, bankPaid g i k) := by
  rw [upper_430_chosen_account, lower_430_chosen_account]
  ring

/-- The formerly obtained Q80 NET-growth necessary floor is owed
entirely to ACTUAL winning physical actions, not to all 106 bank offers.
This is a raw numerator floor and cannot pay the original U3/U4 count. -/
theorem chosen_physical_430_necessary_floor :
    (1731100593645017731014086 : ℤ) ≤
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       buchstabPaid g true i) +
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       buchstabPaid g false i) +
    (∑ i : Fin 200, ∑ g in Finset.range 430,
       ∑ k : Fin 106, bankPaid g i k) := by
  have hf := full_430_increment_necessary_floor
  rw [full_430_chosen_physical_account] at hf
  exact hf

end
end ImbalancedChen.Part5OriginalH430ChosenPhysicalPaymentPartition
