import ImbalancedChen.Part5OriginalH430FutureQuantitativePhysicalFloor

/-!
P5.6/h34 — a necessary frozen closed-cell analytic-envelope test, derived
from ACTUAL generation-two original Q80 receipts and literal retention to
generation 430. The first 53 upper physical sites share one exact integer
receipt. Thus any claimed analytic F upper envelope on their true query
cells must dominate one explicit rational floor at EVERY point in those
cells. A 53-sample inequality and a falsification witness follow.

This DOES NOT prove F is an envelope, perform the 430 positive-source
induction, identify U3/U4 selected counts, or discharge seven integrals.
No numerical experiment is treated as formal verification.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FrozenEnvelopeFirst53Necessary
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalUpsilon5CausalDictionary (floorValue)
open Part5OriginalH430SecondRoundComplete400
open Part5OriginalH430FutureQuantitativePhysicalFloor

/-- An EXACT source table fact about the first 53 ACTUAL original
second-generation upper cells, not an independently constructed F model. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem first53_second_round_literal_receipt (j : Fin 53) :
    secondRoundExactReceipts true
      (⟨j.val, by omega⟩ : Fin 200) =
        (30793941994237432342163 : ℤ) := by
  fin_cases j <;> decide

/-- Literal producer retention carries the exact second-generation
receipt through every generation g>=4. The same actual Q, row table,
physical coordinate, and 2^80 normalization are preserved. -/
theorem first53_future_upper_numerator_floor
    (g : ℕ) (hg : 4 ≤ g) (j : Fin 53) :
    (30793941994237432342163 : ℤ) ≤
      iterate g true (⟨j.val, by omega⟩ : Fin 200) := by
  let i : Fin 200 := ⟨j.val, by omega⟩
  calc
    (30793941994237432342163 : ℤ) =
        secondRoundExactReceipts true i :=
      (first53_second_round_literal_receipt j).symm
    _ = iterate 2 true i :=
      (second_round_all_400_exact true i).symm
    _ ≤ iterate g true i :=
      original_iterate_le_of_le 2 g (by omega) true i

/-- A concrete rational threshold: the 53 equal source receipts each
exceed 0.02547 at the unchanged original Q80 scale. -/
theorem first53_exact_ratio_gt_2547_over_100000 :
    (2547 : ℝ) / 100000 <
      (30793941994237432342163 : ℝ) / (2 ^ 80 : ℝ) := by
  norm_num

/-- A NECESSARY pointwise F test on genuine closed query cells:
if the frozen generation-430 producer is dominated by F, F must be
at least the explicit original source receipt on each of these cells.
No assumption that F passes this test is introduced. -/
theorem any_frozen_closed_upper_must_cover_first53
    (F : ℝ → ℝ)
    (hclosed : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate 430 true) i ≤ F s)
    (j : Fin 53) (s : ℝ)
    (hs : s ∈ queryCell (⟨j.val, by omega⟩ : Fin 200)) :
    (30793941994237432342163 : ℝ) / (2 ^ 80 : ℝ) ≤ F s := by
  let i : Fin 200 := ⟨j.val, by omega⟩
  have hnum : (30793941994237432342163 : ℤ) ≤ iterate 430 true i :=
    first53_future_upper_numerator_floor 430 (by omega) j
  have hreal : (30793941994237432342163 : ℝ) ≤
      (iterate 430 true i : ℝ) := by
    exact_mod_cast hnum
  have hscaled :
      (30793941994237432342163 : ℝ) / (2 ^ 80 : ℝ) ≤
        (iterate 430 true i : ℝ) / (2 ^ 80 : ℝ) :=
    div_le_div_of_nonneg_right hreal (by positivity)
  have hF := hclosed i s hs
  change (iterate 430 true i : ℝ) / (2 ^ 80 : ℝ) ≤ F s at hF
  exact hscaled.trans hF

/-- A simpler strict numerical gate for any original F on the same
53 cells. It is a necessary test, NOT a proved analytic F bound. -/
theorem any_frozen_closed_upper_first53_gt_2547_over_100000
    (F : ℝ → ℝ)
    (hclosed : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate 430 true) i ≤ F s)
    (j : Fin 53) (s : ℝ)
    (hs : s ∈ queryCell (⟨j.val, by omega⟩ : Fin 200)) :
    (2547 : ℝ) / 100000 < F s :=
  lt_of_lt_of_le first53_exact_ratio_gt_2547_over_100000
    (any_frozen_closed_upper_must_cover_first53 F hclosed j s hs)

/-- An explicit failure witness: any proposed F falling BELOW the
source receipt at one true mesh point cannot majorize the actual
generation-430 upper producer. This does not say that frozen F fails. -/
theorem first53_low_F_refutes_frozen_closed_upper
    (F : ℝ → ℝ) (j : Fin 53) (s : ℝ)
    (hs : s ∈ queryCell (⟨j.val, by omega⟩ : Fin 200))
    (hsmall : F s <
      (30793941994237432342163 : ℝ) / (2 ^ 80 : ℝ)) :
    ¬ (∀ (i : Fin 200) (x : ℝ),
        x ∈ queryCell i →
          floorValue (iterate 430 true) i ≤ F x) := by
  intro hclosed
  exact (not_lt_of_ge
    (any_frozen_closed_upper_must_cover_first53 F hclosed j s hs))
      hsmall

/-- EVERY choice of one genuine point per first-53 closed cell has
an exact finite lower sum. It is not an integral or a selected-count
identity: no quadrature direction is inferred without a separate
analytic enclosure of F. -/
theorem first53_sampled_frozen_F_necessary_mass
    (F : ℝ → ℝ) (samples : Fin 53 → ℝ)
    (hsamples : ∀ j : Fin 53,
      samples j ∈ queryCell (⟨j.val, by omega⟩ : Fin 200))
    (hclosed : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate 430 true) i ≤ F s) :
    (1632078925694583914134639 : ℝ) / (2 ^ 80 : ℝ) ≤
      ∑ j : Fin 53, F (samples j) := by
  have hsum :
      (∑ _j : Fin 53,
        (30793941994237432342163 : ℝ) / (2 ^ 80 : ℝ)) ≤
      ∑ j : Fin 53, F (samples j) := by
    apply Finset.sum_le_sum
    intro j _
    exact any_frozen_closed_upper_must_cover_first53
      F hclosed j (samples j) (hsamples j)
  calc
    (1632078925694583914134639 : ℝ) / (2 ^ 80 : ℝ) =
        (∑ _j : Fin 53,
          (30793941994237432342163 : ℝ) / (2 ^ 80 : ℝ)) := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            norm_num
    _ ≤ ∑ j : Fin 53, F (samples j) := hsum

end
end ImbalancedChen.Part5OriginalH430FrozenEnvelopeFirst53Necessary
