import ImbalancedChen.Part5OriginalH430ThirdRoundExactSupport

/-!
P5.6/h34, literal Q80: the last seven upper physical positions at
generation FOUR, and exact saturated support for all later generations.
We use the original 106-bank target list, strict maximal choice, genuine
opposite-table suffix with PER-SUMMAND integer division by the original
q=2^80, and the 56 exact third-round lower exterior receipts.

These are physical producer facts only. They neither pay a CLOSED-CELL
analytic F ceiling nor identify U3/U4 selected-source multiplicities.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FourthRoundSaturatedSupport
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430ThirdRoundExactSupport
open Part5OriginalH430ThirdRoundExterior91
open Part5OriginalH430FirstRoundActiveSupport
open Part5OriginalH430Q80InitialSupport

/-- All real bank targets lie below physical index 100; the original
left-to-right scan therefore changes no decision at high indices. -/
private theorem high_bank_scan_identity
    (old : Table) (i : Fin 200) (hi : 100 ≤ i.val)
    (ks : List (Fin 106)) :
    ∀ d : Decision, scan old i ks d = d := by
  induction ks with
  | nil =>
      intro d
      rfl
  | cons row rest ih =>
      intro d
      change scan old i rest (offerRow old i d row) = d
      have hn : i.val ∉
          (P2Selected430LiteralActionData.rows row).targets :=
        original_bank_untargeted_from_hundred i hi row
      have hrow : offerRow old i d row = d := by
        simp [offerRow, hn]
      rw [hrow]
      exact ih d

/-- Upper sites 193..199 were truly zero at generation 3.
At generation 4 the ORIGINAL producer can only take the lower-table
Buchstab suffix there; neither retention nor a bank row contributes. -/
theorem fourth_upper_last_seven_from_suffix
    (i : Fin 200) (hi : 193 ≤ i.val) :
    iterate 4 true i =
      max 0 (suffix (iterate 3) false (i.val - 49)) := by
  change (scan (iterate 3) i (List.finRange 106)
    (ordinaryDecision (iterate 3) true i)).numerator = _
  rw [high_bank_scan_identity (iterate 3) i (by omega)
    (List.finRange 106) (ordinaryDecision (iterate 3) true i)]
  rw [ordinaryDecision_numerator]
  have h50 : 50 ≤ i.val := by omega
  have hz : iterate 3 true i = 0 :=
    third_upper_zero_from_193 i hi
  have hk : max 50 (i.val - 49) = i.val - 49 := by omega
  simp [h50, hz, hk]

/-- The value of this auxiliary table below index 144 is deliberately
irrelevant: only suffixes beginning at 144 or later are compared. -/
private def lowerThirdExteriorOnly : Table :=
  fun upper i =>
    if upper then 0
    else if h : 144 ≤ i.val then
      thirdLowerNew56Numerators ⟨i.val - 144, by omega⟩
    else 0

private theorem lower_third_exterior_read
    (j : ℕ) (hj : 144 ≤ j) :
    read (iterate 3) false j =
      read lowerThirdExteriorOnly false j := by
  by_cases h200 : j < 200
  · simp only [read, dif_pos h200]
    let r : Fin 56 := ⟨j - 144, by omega⟩
    have heq : (⟨144 + r.val, by omega⟩ : Fin 200) =
        (⟨j, h200⟩ : Fin 200) := by
      apply Fin.ext
      dsimp [r]
      omega
    have hv := third_lower_new_56_actual r
    rw [heq] at hv
    simpa [lowerThirdExteriorOnly, hj, r] using hv
  · simp [read, h200]

/-- This preserves the producer's exact per-term division by q:
it does NOT replace a sum of quotients by a quotient of sums. -/
theorem fourth_suffix_uses_real_third_lower_receipts
    (k : ℕ) (hk : 144 ≤ k) :
    suffix (iterate 3) false k =
      suffix lowerThirdExteriorOnly false k := by
  unfold suffix
  apply Finset.sum_congr rfl
  intro r hr
  rw [lower_third_exterior_read (k + r) (by omega)]

/-- Seven exact ORIGINAL Q80 numerators at upper indices 193..199,
computed from the 56 literal third-round lower exterior receipts and
the unchanged integer logWeights. -/
def fourthUpperNew7Numerators : Fin 7 → ℤ :=
  ![
    46623454541799936325,
    43235920789862635038,
    40036165703553161443,
    37021120464638114366,
    34187778486770303024,
    31533193847533544662,
    29054479768141714228
  ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem fourth_upper_new_7_actual (r : Fin 7) :
    iterate 4 true (⟨193 + r.val, by omega⟩ : Fin 200) =
      fourthUpperNew7Numerators r := by
  rw [fourth_upper_last_seven_from_suffix _ (by omega)]
  rw [fourth_suffix_uses_real_third_lower_receipts _ (by omega)]
  fin_cases r <;> decide

theorem fourth_upper_new_7_positive (r : Fin 7) :
    0 < fourthUpperNew7Numerators r := by
  fin_cases r <;> decide

/-- Exactly the last seven previously zero upper cells turn positive
on the fourth original Q80 generation. -/
theorem fourth_upper_new_7_active (r : Fin 7) :
    0 < iterate 4 true (⟨193 + r.val, by omega⟩ : Fin 200) := by
  rw [fourth_upper_new_7_actual]
  exact fourth_upper_new_7_positive r

/-- From generation 4 onward EVERY upper physical position is positive.
The earlier 193 survive literal retention; the seven new cells come
from the exact fourth-generation Buchstab quotient receipts. -/
theorem fourth_upper_all_200_positive (i : Fin 200) :
    0 < iterate 4 true i := by
  by_cases h193 : i.val < 193
  · exact (third_upper_inside_193_positive i h193).trans_le
      (original_iterate_succ_ge 3 true i)
  · let r : Fin 7 := ⟨i.val - 193, by omega⟩
    have heq : (⟨193 + r.val, by omega⟩ : Fin 200) = i := by
      apply Fin.ext
      dsimp [r]
      omega
    have hv := fourth_upper_new_7_active r
    simpa only [heq] using hv

theorem fourth_lower_from_50_positive (i : Fin 200)
    (h50 : 50 ≤ i.val) :
    0 < iterate 4 false i := by
  exact (third_lower_from_50_positive i h50).trans_le
    (original_iterate_succ_ge 3 false i)

/-- From generation four, the support has saturated the 200 upper
plus 150 lower admissible sites; the original first 50 lower sites
remain identically zero at every generation. -/
theorem future_upper_all_positive (g : ℕ) (hg : 4 ≤ g)
    (i : Fin 200) :
    0 < iterate g true i :=
  (fourth_upper_all_200_positive i).trans_le
    (original_iterate_le_of_le 4 g hg true i)

theorem future_lower_nonzero_iff (g : ℕ) (hg : 4 ≤ g)
    (i : Fin 200) :
    iterate g false i ≠ 0 ↔ 50 ≤ i.val := by
  constructor
  · intro hn
    by_contra hlt
    exact hn (lower_first_fifty_zero g i (by omega))
  · intro h50
    exact ne_of_gt ((fourth_lower_from_50_positive i h50).trans_le
      (original_iterate_le_of_le 4 g hg false i))

/-- Full and stable physical support cardinality for EVERY generation
g>=4 (in particular 430). This is NOT 350 selected-count occurrences,
independent bank payments or a manuscript h34 lower bound. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem future_exactly_350_nonzero_physical (g : ℕ) (hg : 4 ≤ g) :
    (∑ i : Fin 200,
      if iterate g true i ≠ 0 then (1 : ℕ) else 0) +
    (∑ i : Fin 200,
      if iterate g false i ≠ 0 then (1 : ℕ) else 0) = 350 := by
  have hu : (∑ i : Fin 200,
      if iterate g true i ≠ 0 then (1 : ℕ) else 0) = 200 := by
    simp [ne_of_gt (future_upper_all_positive g hg)]
  have hl : (∑ i : Fin 200,
      if iterate g false i ≠ 0 then (1 : ℕ) else 0) = 150 := by
    simp_rw [future_lower_nonzero_iff g hg]
    decide
  omega

theorem generation_430_exactly_350_nonzero_physical :
    (∑ i : Fin 200,
      if iterate 430 true i ≠ 0 then (1 : ℕ) else 0) +
    (∑ i : Fin 200,
      if iterate 430 false i ≠ 0 then (1 : ℕ) else 0) = 350 :=
  future_exactly_350_nonzero_physical 430 (by omega)

end
end ImbalancedChen.Part5OriginalH430FourthRoundSaturatedSupport
