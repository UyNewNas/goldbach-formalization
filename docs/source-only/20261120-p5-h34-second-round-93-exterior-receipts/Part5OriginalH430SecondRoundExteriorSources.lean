import ImbalancedChen.Part5OriginalH430FirstRoundPhysicalMassMoment
import ImbalancedChen.Part5OriginalH430TwoRoundCausalCutoffs

/-!
P5.6/h34: true second-generation Q80 exterior Buchstab receipts.
The first-generation 400-position integer receipt table is read through
its already supplied actual-iterate equality. No replacement action
producer, weight normalization, common-Q change, selected-count licence,
or analytic envelope is introduced.

Upper new exterior = physical 100..157 (58 positions).
Lower new exterior = physical 109..143 (35 positions).
All receipts are the authentic weighted opposite-table suffix, with
integer division performed separately for every summand.

The five lower positions 144..148 are proved permanently absent at
generation two by the prior EXACT upper first-round support at 95,
not by an independently invented truncate-and-forget rule.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / COMPLETE_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430SecondRoundExteriorSources
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430FirstRoundExact400
open Part5OriginalH430FirstRoundActiveSupport
open Part5OriginalH430Q80InitialSupport
open Part5OriginalH430TwoRoundCausalCutoffs

/-- All original 106 rows have targets below 100, irrespective of old Q80. -/
private theorem no_bank_change_above_99
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
      have hn : i.val ∉ (P2Selected430LiteralActionData.rows k).targets :=
        original_bank_untargeted_from_hundred i hi k
      have hrow : offerRow old i d k = d := by
        simp [offerRow, hn]
      rw [hrow]
      exact ih d

/-- On the true upper second-round exterior there is no bank or retention
contribution. The ONLY possible new positive source is the old lower
Buchstab suffix, evaluated with the real finite Q80 integer divisions. -/
theorem second_upper_exterior_from_true_suffix
    (i : Fin 200) (hi : 100 ≤ i.val) :
    iterate 2 true i =
      max 0 (suffix (iterate 1) false (i.val - 49)) := by
  change (scan (iterate 1) i (List.finRange 106)
    (ordinaryDecision (iterate 1) true i)).numerator = _
  rw [no_bank_change_above_99 (iterate 1) i hi
    (List.finRange 106) (ordinaryDecision (iterate 1) true i)]
  rw [ordinaryDecision_numerator]
  have h50 : 50 ≤ i.val := by omega
  have hret : iterate 1 true i = 0 :=
    first_upper_round_zero_from_hundred i hi
  have hk : max 50 (i.val - 49) = i.val - 49 := by omega
  simp [h50, hret, hk]

/-- The true lower second-round exterior has neither original bank
actions nor retention (first lower round is zero beyond index108). -/
theorem second_lower_exterior_from_true_suffix
    (i : Fin 200) (hi : 109 ≤ i.val) :
    iterate 2 false i =
      max 0 (suffix (iterate 1) true (i.val - 49)) := by
  change (ordinaryDecision (iterate 1) false i).numerator = _
  rw [ordinaryDecision_numerator]
  have h50 : 50 ≤ i.val := by omega
  have hret : iterate 1 false i = 0 := first_lower_tail_zero i hi
  simp [h50, hret]

/-- Reading any original first-round physical cell is exactly reading its
previously supplied, per-cell, unchanged Q80 integer receipt. -/
private theorem first_round_read_receipt (upper : Bool) (j : ℕ) :
    read (iterate 1) upper j =
      read firstRoundExactReceipts upper j := by
  by_cases hj : j < 200
  · simp only [read, dif_pos hj]
    exact first_round_all_400_exact upper ⟨j, hj⟩
  · simp [read, hj]

/-- The literal weighted finite suffix respects that exact table equality,
without moving the integer division outside the summation. -/
theorem original_suffix_first_round_receipts
    (upper : Bool) (k : ℕ) :
    suffix (iterate 1) upper k =
      suffix firstRoundExactReceipts upper k := by
  unfold suffix
  apply Finset.sum_congr rfl
  intro r hr
  rw [first_round_read_receipt upper (k + r)]

/-- Exact Q80 numerators in the 58 newly activated upper exterior cells,
ordered by physical index 100..157. -/
def upperNew58Numerators : Fin 58 → ℤ :=
  ![
    4633331466965873374382,
    4425671625134975947027,
    4225265691421106550987,
    4031876711402175723645,
    3845278051186537031294,
    3665252817730419273633,
    3491593319583943560270,
    3324100564670759573412,
    3162583792041077618049,
    3006860034834667738619,
    2856753711954103250790,
    2712096246183310207871,
    2572725706695929387789,
    2438486474085192159450,
    2309228926214625762110,
    2184809143339250213553,
    2065088631082017143533,
    1949934059971819008813,
    1839217020358990930704,
    1732813791623170539257,
    1630605124677842168232,
    1532476036856896240869,
    1438315618341984888151,
    1348016849356145748021,
    1261476427409799347517,
    1178594603940422169883,
    1099275029737507340473,
    1023424608590335792814,
    950953358638026519331,
    881774280939701183873,
    815803234817730236510,
    752958819559232128025,
    693162262090549161688,
    636337310266569105603,
    582410131441721660426,
    531309216012451443498,
    482965285642132520619,
    437311205898904122436,
    394281903054917629554,
    353814284812121698207,
    315847164735093433528,
    280321190185655452691,
    247178773567198095688,
    216364026698840492532,
    187822698150893140389,
    161502113383600267975,
    137351117540908212555,
    115320020760086063891,
    95360545866471389384,
    77425778330476606672,
    61470118371315850341,
    47449235098739413485,
    35320022590430918420,
    25040557808665962613,
    16570060265381866210,
    9868853349995446634,
    4898327239156194922,
    1620903312160377526
  ]

/-- Exact Q80 numerators in the 35 newly activated lower exterior cells,
ordered by physical index 109..143. The old upper source ends at94. -/
def lowerNew35Numerators : Fin 35 → ℤ :=
  ![
    4160357137780757348506,
    3912607292662161772938,
    3667079449171715215380,
    3433009320574653298038,
    3201001510659851269184,
    2976592820686461524380,
    2756780079671018564906,
    2550351869762204779992,
    2345680516981979460852,
    2155967682707645855327,
    1967842422138868942311,
    1796712223599566421059,
    1626990520028615923537,
    1473731545583178774110,
    1321713548109558584949,
    1177880286613181539322,
    1041649910336109475673,
    920511548636137033884,
    800323301513362152152,
    696311232436173494659,
    593102353372954669182,
    507031057763105264720,
    421614303053435665811,
    353482498753573948187,
    285861049838384867716,
    224376138854734252576,
    175292468377166946858,
    142606985984217679846,
    110159218293728102724,
    77945732557348034178,
    45963169850550804603,
    36640597153782368535,
    27383908913378254866,
    18192180423748719701,
    9064506311444454468
  ]

/-- Each table entry is strictly positive as an integer numerator.
This does not imply any analytic or arithmetic selected-count payment. -/
theorem upper_new_58_positive (j : Fin 58) :
    0 < upperNew58Numerators j := by
  fin_cases j <;> decide

theorem lower_new_35_positive (j : Fin 35) :
    0 < lowerNew35Numerators j := by
  fin_cases j <;> decide

/-- Finite certificate against the actual original upper second-generation
producer and the PREVIOUS real lower table; not an independent model. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem second_upper_new_58_actual (j : Fin 58) :
    iterate 2 true (⟨100 + j.val, by omega⟩ : Fin 200) =
      upperNew58Numerators j := by
  let i : Fin 200 := ⟨100 + j.val, by omega⟩
  change iterate 2 true i = upperNew58Numerators j
  calc
    iterate 2 true i =
      max 0 (suffix (iterate 1) false (i.val - 49)) :=
        second_upper_exterior_from_true_suffix i (by dsimp [i]; omega)
    _ = max 0 (suffix firstRoundExactReceipts false (i.val - 49)) := by
      rw [original_suffix_first_round_receipts]
    _ = upperNew58Numerators j := by
      have hcell : suffix firstRoundExactReceipts false (i.val - 49) =
          upperNew58Numerators j := by
        fin_cases j <;> decide
      rw [hcell]
      exact max_eq_right (le_of_lt (upper_new_58_positive j))

/-- Finite certificate against the actual original lower second-generation
producer, retaining the row-wise Q80 integer truncation convention. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem second_lower_new_35_actual (j : Fin 35) :
    iterate 2 false (⟨109 + j.val, by omega⟩ : Fin 200) =
      lowerNew35Numerators j := by
  let i : Fin 200 := ⟨109 + j.val, by omega⟩
  change iterate 2 false i = lowerNew35Numerators j
  calc
    iterate 2 false i =
      max 0 (suffix (iterate 1) true (i.val - 49)) :=
        second_lower_exterior_from_true_suffix i (by dsimp [i]; omega)
    _ = max 0 (suffix firstRoundExactReceipts true (i.val - 49)) := by
      rw [original_suffix_first_round_receipts]
    _ = lowerNew35Numerators j := by
      have hcell : suffix firstRoundExactReceipts true (i.val - 49) =
          lowerNew35Numerators j := by
        fin_cases j <;> decide
      rw [hcell]
      exact max_eq_right (le_of_lt (lower_new_35_positive j))

/-- New, sharper CAUSAL zero tail: the first upper round actually stops at
95, not at the previous coarse bank target cutoff100. Thus second-round
lower physical indices 144..199 are provably zero; this removes five
previously unneeded CLOSED-CELL positive-source checks. -/
theorem second_lower_zero_from_144
    (i : Fin 200) (hi : 144 ≤ i.val) :
    iterate 2 false i = 0 := by
  have hu : ∀ j : Fin 200, 95 ≤ j.val → iterate 1 true j = 0 :=
    fun j hj => first_upper_round_zero_from_95 j hj
  have hl : ∀ j : Fin 200, 109 ≤ j.val → iterate 1 false j = 0 :=
    fun j hj => first_lower_tail_zero j hj
  exact lower_tail_next 1 95 109 hu hl i (by omega)

/-- The second real Q80 output has at most 158 upper + 94 lower =
252 potentially nonzero physical cells (not a 252-action payment).
The lower first 50 positions remain zero in every generation. -/
theorem second_round_nonzero_inside_252
    (upper : Bool) (i : Fin 200)
    (hnz : iterate 2 upper i ≠ 0) :
    (upper = true ∧ i.val < 158) ∨
    (upper = false ∧ 50 ≤ i.val ∧ i.val < 144) := by
  cases upper with
  | false =>
      have h50 : 50 ≤ i.val := by
        by_contra h
        exact hnz (lower_first_fifty_zero 2 i (by omega))
      have h144 : i.val < 144 := by
        by_contra h
        exact hnz (second_lower_zero_from_144 i (by omega))
      exact Or.inr ⟨rfl, h50, h144⟩
  | true =>
      have h158 : i.val < 158 := by
        by_contra h
        exact hnz (second_upper_zero_from_158 i (by omega))
      exact Or.inl ⟨rfl, h158⟩

end
end ImbalancedChen.Part5OriginalH430SecondRoundExteriorSources
