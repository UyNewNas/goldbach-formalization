import ImbalancedChen.Part5OriginalH430LiteralIncrementTelescope
import ImbalancedChen.Part5OriginalH430LiteralRoundActionStep

/-!
P5.6 -> h34: a strict, literal SOURCE test for Q80 physical increases.

The old 430-generation telescope identifies *how much* mass changed, but
it does not prove which of the real non-retention offers can cause a change.
This module proves a two-sided exact test at the original one-round max:
there is strict new numerator iff an enabled original Buchstab suffix or
an actually TARGETED one of the 106 upper bank offers strictly exceeds the
same predecessor cell's old numerator. Retention alone never increases it.

In particular, a positive 430-round physical net-growth ledger forces at
least one real non-retained offer somewhere in the original 430-step run.
This is NOT a unique winning action/owner, a count-source multiplicity
certificate, an analytic upper F payment, or a U3/U4 selected-count result.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430StrictIncrementActualSources
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430LiteralRoundActionStep
open Part5OriginalH430LiteralIncrementTelescope

/-- Scan never discards an already reached numerator. The proof follows
actual left-to-right original 106-row offers, not a hypothetical max. -/
private theorem scan_retains_numerator (old : Table) (i : Fin 200) :
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
      have hrow : d.numerator ≤ (offerRow old i d k).numerator := by
        by_cases ht : i.val ∈ (rows k).targets
        · simpa only [offerRow, if_pos ht, offer_numerator] using
            (le_max_left d.numerator (candidate old (rows k)))
        · simpa only [offerRow, if_neg ht] using (le_refl d.numerator)
      exact hrow.trans (ih (offerRow old i d k))

/-- Every original targeted offer is below the resulting scan, even if
another bank row wins. This is dominance, NOT permission to charge it. -/
private theorem targeted_offer_le_scan (old : Table) (i : Fin 200)
    (ks : List (Fin 106)) (d : Decision) (k : Fin 106)
    (htarget : i.val ∈ (rows k).targets) (hk : k ∈ ks) :
    candidate old (rows k) ≤ (scan old i ks d).numerator := by
  induction ks generalizing d with
  | nil => cases hk
  | cons j js ih =>
      rcases List.mem_cons.mp hk with h | h
      · subst j
        have hrow : candidate old (rows k) ≤
            (offerRow old i d k).numerator := by
          simpa only [offerRow, if_pos htarget, offer_numerator] using
            (le_max_right d.numerator (candidate old (rows k)))
        exact hrow.trans
          (scan_retains_numerator old i js (offerRow old i d k))
      · change candidate old (rows k) ≤
          (scan old i js (offerRow old i d j)).numerator
        exact ih (offerRow old i d j) h

/-- When enabled, the literal opposite-table Buchstab suffix is
present in the original ordinary max, with upper max-50 / lower offset. -/
private theorem actual_suffix_le_ordinary (old : Table) (upper : Bool)
    (i : Fin 200) (h50 : 50 ≤ i.val) :
    (if upper then suffix old false (max 50 (i.val - 49))
     else suffix old true (i.val - 49)) ≤
       (ordinaryDecision old upper i).numerator := by
  rw [ordinaryDecision_numerator]
  simpa [h50] using
    (le_max_right (old upper i)
      (if upper then suffix old false (max 50 (i.val - 49))
       else suffix old true (i.val - 49)))

/-- Exact old-to-new strict-increase classification at the ORIGINAL
Q80 one-round max. The right side speaks about offers above the SAME
old physical numerator; it does NOT claim that every such offer wins. -/
theorem literal_round_strict_increase_iff (old : Table)
    (upper : Bool) (i : Fin 200) :
    old upper i < roundTable old upper i ↔
      (50 ≤ i.val ∧ old upper i <
        (if upper then suffix old false (max 50 (i.val - 49))
         else suffix old true (i.val - 49))) ∨
      (upper = true ∧ ∃ k : Fin 106,
        i.val ∈ (rows k).targets ∧
          old upper i < candidate old (rows k)) := by
  constructor
  · intro hraise
    rcases literal_round_overflow_has_actual_action_witness
      old upper i (old upper i) hraise with hret | hbuch | hbank
    · exact False.elim (lt_irrefl _ hret)
    · exact Or.inl hbuch
    · exact Or.inr hbank
  · intro hsource
    rcases hsource with ⟨h50, hsource⟩ | ⟨hu, k, htarget, hsource⟩
    · cases upper with
      | false =>
          change old false i < (ordinaryDecision old false i).numerator
          exact hsource.trans (actual_suffix_le_ordinary old false i h50)
      | true =>
          change old true i <
            (scan old i (List.finRange 106)
              (ordinaryDecision old true i)).numerator
          exact hsource.trans
            ((actual_suffix_le_ordinary old true i h50).trans
              (scan_retains_numerator old i (List.finRange 106)
                (ordinaryDecision old true i)))
    · cases upper with
      | false => cases hu
      | true =>
          change old true i <
            (scan old i (List.finRange 106)
              (ordinaryDecision old true i)).numerator
          exact hsource.trans
            (targeted_offer_le_scan old i (List.finRange 106)
              (ordinaryDecision old true i) k htarget (by simp))

/-- A positive genuine Q80 increment is precisely an enabled original
non-retention offer above the old numerator. This criterion applies at
EVERY actual generation, not just at the initial seed. -/
theorem actual_increment_positive_iff_source (g : Fin 430)
    (upper : Bool) (i : Fin 200) :
    0 < literalIncrement g.val upper i ↔
      (50 ≤ i.val ∧ iterate g.val upper i <
        (if upper then
           suffix (iterate g.val) false (max 50 (i.val - 49))
         else suffix (iterate g.val) true (i.val - 49))) ∨
      (upper = true ∧ ∃ k : Fin 106,
        i.val ∈ (rows k).targets ∧
          iterate g.val upper i < candidate (iterate g.val) (rows k)) := by
  have hchange : 0 < literalIncrement g.val upper i ↔
      iterate g.val upper i < iterate (g.val + 1) upper i := by
    unfold literalIncrement
    omega
  rw [hchange]
  change (iterate g.val upper i <
    roundTable (iterate g.val) upper i) ↔ _
  exact literal_round_strict_increase_iff (iterate g.val) upper i

/-- Exact absence-of-new-mass criterion for the original Q80 producer.
No unchosen offer is paid: candidates are used only to test whether the
single physical integer numerator changed. -/
theorem actual_increment_zero_iff_no_strict_source (g : Fin 430)
    (upper : Bool) (i : Fin 200) :
    literalIncrement g.val upper i = 0 ↔
      (50 ≤ i.val →
        (if upper then
           suffix (iterate g.val) false (max 50 (i.val - 49))
         else suffix (iterate g.val) true (i.val - 49)) ≤
            iterate g.val upper i) ∧
      (upper = true → ∀ k : Fin 106,
        i.val ∈ (rows k).targets →
          candidate (iterate g.val) (rows k) ≤ iterate g.val upper i) := by
  constructor
  · intro hzero
    have hnot : ¬ 0 < literalIncrement g.val upper i := by omega
    have hnotSource : ¬ ((50 ≤ i.val ∧ iterate g.val upper i <
        (if upper then
           suffix (iterate g.val) false (max 50 (i.val - 49))
         else suffix (iterate g.val) true (i.val - 49))) ∨
      (upper = true ∧ ∃ k : Fin 106,
        i.val ∈ (rows k).targets ∧
          iterate g.val upper i < candidate (iterate g.val) (rows k))) :=
      fun h => hnot ((actual_increment_positive_iff_source g upper i).2 h)
    constructor
    · intro h50
      exact le_of_not_gt (fun h => hnotSource (Or.inl ⟨h50, h⟩))
    · intro hu k ht
      exact le_of_not_gt (fun h =>
        hnotSource (Or.inr ⟨hu, k, ht, h⟩))
  · rintro ⟨hbuch, hbank⟩
    have hnot : ¬ 0 < literalIncrement g.val upper i := by
      intro hpositive
      rcases (actual_increment_positive_iff_source g upper i).1
          hpositive with hb | hk
      · exact (not_lt_of_ge (hbuch hb.1)) hb.2
      · rcases hk with ⟨hu, k, ht, hgt⟩
        exact (not_lt_of_ge (hbank hu k ht)) hgt
    have hn := literal_increment_nonneg g.val upper i
    omega

/-- The previous independently recorded strictly positive 430-round
net physical numerator floor forces at least one real original
non-retained positive source occurrence somewhere before generation430.
No root/owner count or unique action selection is inferred. -/
theorem necessary_positive_original_source_before_430 :
    ∃ g : Fin 430, ∃ upper : Bool, ∃ i : Fin 200,
      (50 ≤ i.val ∧ iterate g.val upper i <
        (if upper then
           suffix (iterate g.val) false (max 50 (i.val - 49))
         else suffix (iterate g.val) true (i.val - 49))) ∨
      (upper = true ∧ ∃ k : Fin 106,
        i.val ∈ (rows k).targets ∧
          iterate g.val upper i < candidate (iterate g.val) (rows k)) := by
  by_contra hnone
  have hz (g : Fin 430) (upper : Bool) (i : Fin 200) :
      literalIncrement g.val upper i = 0 := by
    have hnot : ¬ 0 < literalIncrement g.val upper i := by
      intro hpos
      exact hnone ⟨g, upper, i,
        (actual_increment_positive_iff_source g upper i).1 hpos⟩
    have hn := literal_increment_nonneg g.val upper i
    omega
  have hsum (upper : Bool) :
      (∑ i : Fin 200,
        ∑ g in Finset.range 430, literalIncrement g upper i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro g hg
    exact hz ⟨g, Finset.mem_range.mp hg⟩ upper i
  have hfloor := full_430_increment_necessary_floor
  rw [hsum true, hsum false] at hfloor
  norm_num at hfloor

end
end ImbalancedChen.Part5OriginalH430StrictIncrementActualSources
