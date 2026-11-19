import ImbalancedChen.Part5OriginalH430FirstRoundActiveSupport

/-!
P5.6 / h34: actual Q80 finite-speed causal support, including round TWO.

These are unconditional integer-producer support facts, NOT a CLOSED-CELL
analytic majorant, F seed, coefficient/payment estimate, or h34 closure.
We use the original 106 bank targets, the same q and logWeights, the
original ordinaryDecision, the original floor and the actual iterate.
No generic assumed action, counting licence, or external analytic input.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430TwoRoundCausalCutoffs
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (logWeights)
open Part5OriginalH430FirstRoundActiveSupport

/-- A genuine zero tail of an old table makes the ORIGINAL weighted
Buchstab suffix zero, including the integer division by the fixed q. -/
theorem actual_suffix_zero_of_tail
    (old : Table) (upper : Bool) (cutoff k : ℕ)
    (hzero : ∀ i : Fin 200, cutoff ≤ i.val → old upper i = 0)
    (hk : cutoff ≤ k) :
    suffix old upper k = 0 := by
  unfold suffix
  have hsum :
      (∑ r ∈ Finset.range (200 - k),
        read old upper (k + r) *
          (if hj : k + r < 200 then
            logWeights ⟨k + r, hj⟩ else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hread : read old upper (k + r) = 0 := by
      by_cases hj : k + r < 200
      · have hv : old upper (⟨k + r, hj⟩ : Fin 200) = 0 :=
          hzero ⟨k + r, hj⟩ (by dsimp; omega)
        simpa [read, hj] using hv
      · simp [read, hj]
    simp [hread]
  rw [hsum]
  simp

/-- The REAL 106-bank scan cannot introduce positive mass beyond
index 99, regardless of the previous table or decision provenance. -/
private theorem high_scan_unchanged
    (old : Table) (i : Fin 200) (hi : 100 ≤ i.val)
    (ks : List (Fin 106)) :
    ∀ d : Decision, scan old i ks d = d := by
  induction ks with
  | nil =>
      intro d
      rfl
  | cons k ks ih =>
      intro d
      change scan old i ks (offerRow old i d k) = d
      have hnot : i.val ∉ (P2Selected430LiteralActionData.rows k).targets :=
        original_bank_untargeted_from_hundred i hi k
      have hrow : offerRow old i d k = d := by
        simp [offerRow, hnot]
      rw [hrow]
      exact ih d

/-- One real upper generation propagates only through previous upper
retention, opposite lower Buchstab suffix, and original 106 bank targets. -/
theorem upper_tail_next
    (g upperCut lowerCut : ℕ)
    (hu : ∀ i : Fin 200, upperCut ≤ i.val → iterate g true i = 0)
    (hl : ∀ i : Fin 200, lowerCut ≤ i.val → iterate g false i = 0)
    (i : Fin 200)
    (hi : max 100 (max upperCut (lowerCut + 49)) ≤ i.val) :
    iterate (g + 1) true i = 0 := by
  change (scan (iterate g) i (List.finRange 106)
    (ordinaryDecision (iterate g) true i)).numerator = 0
  have hi100 : 100 ≤ i.val := by omega
  rw [high_scan_unchanged (iterate g) i hi100
    (List.finRange 106) (ordinaryDecision (iterate g) true i)]
  rw [ordinaryDecision_numerator]
  have h50 : 50 ≤ i.val := by omega
  have hk : lowerCut ≤ max 50 (i.val - 49) := by omega
  have hs : suffix (iterate g) false (max 50 (i.val - 49)) = 0 :=
    actual_suffix_zero_of_tail (iterate g) false lowerCut
      (max 50 (i.val - 49)) hl hk
  have hret : iterate g true i = 0 := hu i (by omega)
  simp [h50, hret, hs]

/-- The actual lower update has NO bank alternative. It retains
old lower mass or takes exactly the opposite upper weighted suffix. -/
theorem lower_tail_next
    (g upperCut lowerCut : ℕ)
    (hu : ∀ i : Fin 200, upperCut ≤ i.val → iterate g true i = 0)
    (hl : ∀ i : Fin 200, lowerCut ≤ i.val → iterate g false i = 0)
    (i : Fin 200)
    (hi : max 50 (max lowerCut (upperCut + 49)) ≤ i.val) :
    iterate (g + 1) false i = 0 := by
  change (ordinaryDecision (iterate g) false i).numerator = 0
  rw [ordinaryDecision_numerator]
  have h50 : 50 ≤ i.val := by omega
  have hk : upperCut ≤ i.val - 49 := by omega
  have hs : suffix (iterate g) true (i.val - 49) = 0 :=
    actual_suffix_zero_of_tail (iterate g) true upperCut
      (i.val - 49) hu hk
  have hret : iterate g false i = 0 := hl i (by omega)
  simp [h50, hret, hs]

/-- Simultaneous upper/lower causal tail bounds from the original
seed (60,0). The recurrence respects BOTH ordinary directions and
all 106 bank targets, without any upper-envelope premise. -/
def causalCut : ℕ → ℕ × ℕ
  | 0 => (60, 0)
  | g + 1 =>
      (max 100 (max (causalCut g).1 ((causalCut g).2 + 49)),
       max 50 (max (causalCut g).2 ((causalCut g).1 + 49)))

theorem original_q80_causal_tails (g : ℕ) :
    (∀ i : Fin 200, (causalCut g).1 ≤ i.val → iterate g true i = 0) ∧
    (∀ i : Fin 200, (causalCut g).2 ≤ i.val → iterate g false i = 0) := by
  induction g with
  | zero =>
      constructor
      · intro i hi
        change seed true i = 0
        have hnot : ¬ i.val < 60 := by omega
        simp [seed, hnot]
      · intro i _
        change seed false i = 0
        simp [seed]
  | succ g ih =>
      obtain ⟨hu, hl⟩ := ih
      constructor
      · intro i hi
        have hcut :
            max 100 (max (causalCut g).1 ((causalCut g).2 + 49)) ≤
              i.val := by
          simpa only [causalCut] using hi
        exact upper_tail_next g (causalCut g).1 (causalCut g).2
          hu hl i hcut
      · intro i hi
        have hcut :
            max 50 (max (causalCut g).2 ((causalCut g).1 + 49)) ≤
              i.val := by
          simpa only [causalCut] using hi
        exact lower_tail_next g (causalCut g).1 (causalCut g).2
          hu hl i hcut

/-- At the actual second update, upper cells 158..199 are exactly zero. -/
theorem second_upper_zero_from_158
    (i : Fin 200) (hi : 158 ≤ i.val) :
    iterate 2 true i = 0 := by
  apply (original_q80_causal_tails 2).1 i
  norm_num [causalCut] at *

/-- At the actual second update, lower cells 149..199 are exactly zero. -/
theorem second_lower_zero_from_149
    (i : Fin 200) (hi : 149 ≤ i.val) :
    iterate 2 false i = 0 := by
  apply (original_q80_causal_tails 2).2 i
  norm_num [causalCut] at *

/-- The second real generation has at most 158 upper plus 99 lower
potentially nonzero cells. Lower positions 0..49 stay zero for ALL g.
This is a source-support result, not a positive-mass estimate. -/
theorem second_round_nonzero_only_in_causal_window
    (upper : Bool) (i : Fin 200)
    (hnonzero : iterate 2 upper i ≠ 0) :
    (upper = true ∧ i.val < 158) ∨
    (upper = false ∧ 50 ≤ i.val ∧ i.val < 149) := by
  cases upper with
  | false =>
      have h50 : 50 ≤ i.val := by
        by_contra hn
        exact hnonzero
          (Part5OriginalH430Q80InitialSupport.lower_first_fifty_zero
            2 i (by omega))
      have h149 : i.val < 149 := by
        by_contra hn
        exact hnonzero (second_lower_zero_from_149 i (by omega))
      exact Or.inr ⟨rfl, h50, h149⟩
  | true =>
      have h158 : i.val < 158 := by
        by_contra hn
        exact hnonzero (second_upper_zero_from_158 i (by omega))
      exact Or.inl ⟨rfl, h158⟩

end
end ImbalancedChen.Part5OriginalH430TwoRoundCausalCutoffs
