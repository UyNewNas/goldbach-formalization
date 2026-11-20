import ImbalancedChen.Part5OriginalH430FourthRoundSaturatedSupport

/-!
P5.6/h34: a concrete quantitative FLOOR for all original Q80 physical
numerators at every future generation >= 4, including generation 430.
The floor is built from the already recorded *actual* second, third and
fourth-generation numerators, not an invented recurrence and not a new
selected-count or closed-cell upper envelope.

The key point is pointwise retention: a receipt from generation two,
three or four is preserved under every later original 106-bank/Buchstab
round. This is a LOWER floor, not the still-unpaid analytic F ceiling.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FutureQuantitativePhysicalFloor
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430SecondRoundComplete400
open Part5OriginalH430ThirdRoundExterior91
open Part5OriginalH430ThirdRoundExactSupport
open Part5OriginalH430FourthRoundSaturatedSupport

/-- For each of the 400 physical Q80 sites, take its actual numeral at
its LAST support-activation generation. Upper: second 0..157,
third 158..192, fourth 193..199. Lower: second 0..143,
third 144..199. The first 50 lower positions correctly remain zero. -/
def physicalFloor (upper : Bool) (i : Fin 200) : ℤ :=
  if upper then
    if h158 : i.val < 158 then
      secondRoundExactReceipts true i
    else if h193 : i.val < 193 then
      thirdUpperNew35Numerators ⟨i.val - 158, by omega⟩
    else
      fourthUpperNew7Numerators ⟨i.val - 193, by omega⟩
  else
    if h144 : i.val < 144 then
      secondRoundExactReceipts false i
    else
      thirdLowerNew56Numerators ⟨i.val - 144, by omega⟩

/-- A single unconditional pointwise quantitative floor for EVERY original
future Q80 generation, assembled from actual generation 2/3/4 receipts.
The induction is the existing original retention theorem, not a claim that
the physical table stops evolving at generation 4. -/
theorem physicalFloor_le_future (g : ℕ) (hg : 4 ≤ g)
    (upper : Bool) (i : Fin 200) :
    physicalFloor upper i ≤ iterate g upper i := by
  cases upper with
  | false =>
      by_cases h144 : i.val < 144
      · calc
          physicalFloor false i = secondRoundExactReceipts false i := by
            simp [physicalFloor, h144]
          _ = iterate 2 false i :=
            (second_round_all_400_exact false i).symm
          _ ≤ iterate g false i :=
            original_iterate_le_of_le 2 g (by omega) false i
      · let j : Fin 56 := ⟨i.val - 144, by omega⟩
        have heq :
            (⟨144 + j.val, by omega⟩ : Fin 200) = i := by
          apply Fin.ext
          dsimp [j]
          omega
        have hv := third_lower_new_56_actual j
        rw [heq] at hv
        calc
          physicalFloor false i = thirdLowerNew56Numerators j := by
            simp [physicalFloor, h144, j]
          _ = iterate 3 false i := hv.symm
          _ ≤ iterate g false i :=
            original_iterate_le_of_le 3 g (by omega) false i
  | true =>
      by_cases h158 : i.val < 158
      · calc
          physicalFloor true i = secondRoundExactReceipts true i := by
            simp [physicalFloor, h158]
          _ = iterate 2 true i :=
            (second_round_all_400_exact true i).symm
          _ ≤ iterate g true i :=
            original_iterate_le_of_le 2 g (by omega) true i
      · by_cases h193 : i.val < 193
        · let j : Fin 35 := ⟨i.val - 158, by omega⟩
          have heq :
              (⟨158 + j.val, by omega⟩ : Fin 200) = i := by
            apply Fin.ext
            dsimp [j]
            omega
          have hv := third_upper_new_35_actual j
          rw [heq] at hv
          calc
            physicalFloor true i = thirdUpperNew35Numerators j := by
              simp [physicalFloor, h158, h193, j]
            _ = iterate 3 true i := hv.symm
            _ ≤ iterate g true i :=
              original_iterate_le_of_le 3 g (by omega) true i
        · let j : Fin 7 := ⟨i.val - 193, by omega⟩
          have heq :
              (⟨193 + j.val, by omega⟩ : Fin 200) = i := by
            apply Fin.ext
            dsimp [j]
            omega
          have hv := fourth_upper_new_7_actual j
          rw [heq] at hv
          calc
            physicalFloor true i = fourthUpperNew7Numerators j := by
              simp [physicalFloor, h158, h193, j]
            _ = iterate 4 true i := hv.symm
            _ ≤ iterate g true i :=
              original_iterate_le_of_le 4 g hg true i

/-- Exact sum of all 200 upper pointwise floor numerators. This is
finite definitional arithmetic on the pinned genuine receipt vectors. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem upper_physicalFloor_sum :
    (∑ i : Fin 200, physicalFloor true i) =
      (2531008222310275142702497 : ℤ) := by
  decide

/-- Exact sum of all 200 lower pointwise floor numerators, including
the unchanged initial 50 structural zeros. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem lower_physicalFloor_sum :
    (∑ i : Fin 200, physicalFloor false i) =
      (887994600680687842036309 : ℤ) := by
  decide

/-- Hence a real explicit physical numerator mass floor is preserved
at every generation >= 4. This is NOT a U3/U4 selected-count lower
bound; no original owner/filter/Theta correspondence is asserted. -/
theorem future_physical_numerator_total_lower (g : ℕ) (hg : 4 ≤ g) :
    (3419002822990962984738806 : ℤ) ≤
      (∑ i : Fin 200, iterate g true i) +
      (∑ i : Fin 200, iterate g false i) := by
  have hu :
      (∑ i : Fin 200, physicalFloor true i) ≤
      (∑ i : Fin 200, iterate g true i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact physicalFloor_le_future g hg true i
  have hl :
      (∑ i : Fin 200, physicalFloor false i) ≤
      (∑ i : Fin 200, iterate g false i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact physicalFloor_le_future g hg false i
  calc
    (3419002822990962984738806 : ℤ) =
        (∑ i : Fin 200, physicalFloor true i) +
        (∑ i : Fin 200, physicalFloor false i) := by
      rw [upper_physicalFloor_sum, lower_physicalFloor_sum]
      norm_num
    _ ≤ (∑ i : Fin 200, iterate g true i) +
        (∑ i : Fin 200, iterate g false i) :=
      add_le_add hu hl

theorem generation_430_physical_numerator_total_lower :
    (3419002822990962984738806 : ℤ) ≤
      (∑ i : Fin 200, iterate 430 true i) +
      (∑ i : Fin 200, iterate 430 false i) :=
  future_physical_numerator_total_lower 430 (by omega)

/-- Necessary numerical sanity condition for any subsequent ACTUAL
physical Q80 upper-envelope proof: it must dominate the independent
fixed original receipt floor at every indexed site. No F was assumed
to exist or to pass this check. -/
theorem any_430_ceiling_must_dominate_floor (ceiling : Table)
    (h : ∀ upper i, iterate 430 upper i ≤ ceiling upper i) :
    ∀ upper i, physicalFloor upper i ≤ ceiling upper i := by
  intro upper i
  exact (physicalFloor_le_future 430 (by omega) upper i).trans
    (h upper i)

end
end ImbalancedChen.Part5OriginalH430FutureQuantitativePhysicalFloor
