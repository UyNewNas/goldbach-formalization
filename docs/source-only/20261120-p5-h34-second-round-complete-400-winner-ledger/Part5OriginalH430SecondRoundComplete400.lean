import ImbalancedChen.Part5OriginalH430SecondRoundExteriorSources

/-!
P5.6/h34 second ORIGINAL Q80 generation: all 400 physical numerators and
the actual original-action winning rows in the first 100 upper positions.
The 100 upper and 59 lower interior integers were independently calculated
from the previous *actual* first-round table, the original 106 literal rows,
integer sign, divisor and scan order, and the original per-summand Q80
division. The 58+35 exterior integers are reused, not redefined.
This source-only file is an UNCOMPILED candidate; the physical Q80
receipts are NOT an analytic F-envelope or U3/U4 selected-count licence.
-/

namespace ImbalancedChen.Part5OriginalH430SecondRoundComplete400
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430FirstRoundExact400
open Part5OriginalH430SecondRoundExteriorSources
open Part5OriginalH430Q80InitialSupport
open Part5OriginalH430TwoRoundCausalCutoffs

/-- Original second-round upper physical positions 0..99, integer numerators.
Every original bank candidate reads the same frozen first-round old table. -/
def secondUpperInterior100 : Fin 100 → ℤ :=
  ![
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30793941994237432342163,
    30781067295929156182245,
    30781067295929156182245,
    30496726483353897161964,
    30496726483353897161964,
    30054271206726079149197,
    29670337525362364675120,
    29670337525362364675120,
    28845914288373649237560,
    28845914288373649237560,
    27761045267065412639539,
    27761045267065412639539,
    27157702427330598043604,
    26820586571357891153179,
    25518852121164419348107,
    25518852121164419348107,
    24123932250127954325221,
    24123932250127954325221,
    22667450046106964996204,
    22667450046106964996204,
    21002205137519672071766,
    21002205137519672071766,
    20147352046308902477843,
    19278967969395781053105,
    17388655547205121830307,
    17388655547205121830307,
    16135294257126889968390,
    16135294257126889968390,
    13116702644000296082390,
    13116702644000296082390,
    11604518777995476720826,
    11604518777995476720826,
    10894213542955329947616,
    8338590303318285579182,
    6581114124046773385157,
    6581114124046773385157,
    6581114124046773385157,
    6581114124046773385157,
    4848493115750821917597,
    4848493115750821917597,
    4848493115750821917597,
    4848493115750821917597,
    4848493115750821917597,
    4848493115750821917597,
    4848493115750821917597,
    4848493115750821917597,
    4848493115750821917597,
    4848493115750821917597
  ]

/-- Original second-round lower physical positions 50..108, retaining
the exact per-term Q80 quotient in Buchstab suffix. -/
def secondLowerInterior59 : Fin 59 → ℤ :=
  ![
    26508015401694600732242,
    25942764298533441593579,
    25388280540471563151247,
    24844161574096190837822,
    24310027007456504632180,
    23785517012616849400573,
    23270290869600109322572,
    22764025636964740079599,
    22266414936025054765765,
    21777167837252948589241,
    21296007838725664617846,
    20822671927638041270056,
    20356909716903799026668,
    19898482649749760536363,
    19447163265977148971092,
    19002734524240266205397,
    18564989175287652248089,
    18133729181635120056878,
    17708765179603110894229,
    17289915980060556778088,
    16877008104580675050172,
    16469875354036710162459,
    16068358406952626330890,
    15672304445179501812564,
    15281566804696655966757,
    14896004649540628647211,
    14515482667047874394246,
    14139870782760910544312,
    13769043893494832074401,
    13402881617193467913880,
    13041268058323659788556,
    12684091587663648368076,
    12331244635438629383697,
    11982623496844318351308,
    11638128149078827434395,
    11297662079075186768219,
    10961132121192209030335,
    10628448304180785530037,
    10299523706796722496589,
    9974274321480417539977,
    9652618925568518733160,
    9334478959543630218869,
    9019778411865510220792,
    8708443709961390570978,
    8400403616984336024728,
    8095589133977229487100,
    7793933407106260318664,
    7495371639651926540156,
    7199841008467735156134,
    6907280584637175291397,
    6617631258078306059692,
    6330835665862589007615,
    6046838124030533498366,
    5765584562701429868952,
    5487022464288025728825,
    5213210070284561297919,
    4941968722634497030744,
    4676899358571383111429,
    4417443501691828328115
  ]

/-- Actual winning bank row at each of the first 90 upper positions.
A *winner* is one scan decision, not 90 extra chargeable bank masses. -/
def secondUpper90WinningBank : Fin 90 → Fin 106 :=
  ![
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨75, by decide⟩,
    ⟨78, by decide⟩,
    ⟨78, by decide⟩,
    ⟨80, by decide⟩,
    ⟨80, by decide⟩,
    ⟨81, by decide⟩,
    ⟨83, by decide⟩,
    ⟨83, by decide⟩,
    ⟨85, by decide⟩,
    ⟨85, by decide⟩,
    ⟨86, by decide⟩,
    ⟨86, by decide⟩,
    ⟨87, by decide⟩,
    ⟨89, by decide⟩,
    ⟨90, by decide⟩,
    ⟨90, by decide⟩,
    ⟨91, by decide⟩,
    ⟨91, by decide⟩,
    ⟨92, by decide⟩,
    ⟨92, by decide⟩,
    ⟨94, by decide⟩,
    ⟨94, by decide⟩,
    ⟨95, by decide⟩,
    ⟨96, by decide⟩,
    ⟨98, by decide⟩,
    ⟨98, by decide⟩,
    ⟨22, by decide⟩,
    ⟨22, by decide⟩,
    ⟨100, by decide⟩,
    ⟨100, by decide⟩,
    ⟨101, by decide⟩,
    ⟨101, by decide⟩,
    ⟨31, by decide⟩,
    ⟨103, by decide⟩,
    ⟨41, by decide⟩,
    ⟨41, by decide⟩,
    ⟨41, by decide⟩,
    ⟨41, by decide⟩
  ]

/-- Real original decision: bank on cells 0..89, Buchstab on 90..99.
The exact producer proof below is required to justify this finite ledger. -/
def secondUpper100WinningChoice (j : Fin 100) : Choice :=
  if h : j.val < 90 then
    .bank (secondUpper90WinningBank ⟨j.val, h⟩)
  else .buchstab

/-- Function extensionality makes the original iterate1 table (not
a substitute arithmetic recurrence) available for finite certificates. -/
private theorem first_round_table_ext :
    iterate 1 = firstRoundExactReceipts := by
  funext upper i
  exact first_round_all_400_exact upper i

/-- Exact interior upper receipts against the original 106-row max scan. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem second_upper_interior_100_actual (j : Fin 100) :
    iterate 2 true (⟨j.val, by omega⟩ : Fin 200) =
      secondUpperInterior100 j := by
  change (roundDecision (iterate 1) true (⟨j.val, by omega⟩ : Fin 200)).numerator = _
  rw [first_round_table_ext]
  fin_cases j <;> decide

/-- Exact interior lower receipts against the original Buchstab/retention
maximum, with the 50-cell offset and per-term integer division intact. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem second_lower_interior_59_actual (j : Fin 59) :
    iterate 2 false (⟨50 + j.val, by omega⟩ : Fin 200) =
      secondLowerInterior59 j := by
  change (roundDecision (iterate 1) false (⟨50 + j.val, by omega⟩ : Fin 200)).numerator = _
  rw [first_round_table_ext]
  fin_cases j <;> decide

/-- Winner identity, including retained-vs-Buchstab-vs-bank priority
and the authentic 106-row left-to-right strict improvement rule. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem second_upper_100_winning_choice_actual (j : Fin 100) :
    (roundDecision (iterate 1) true (⟨j.val, by omega⟩ : Fin 200)).choice =
      secondUpper100WinningChoice j := by
  rw [first_round_table_ext]
  fin_cases j <;> decide

/-- Original second-generation full 400-cell physical Q80 receipt table. -/
def secondRoundExactReceipts (upper : Bool) (i : Fin 200) : ℤ :=
  if upper then
    if h100 : i.val < 100 then
      secondUpperInterior100 ⟨i.val, h100⟩
    else if h158 : i.val < 158 then
      upperNew58Numerators ⟨i.val - 100, by omega⟩
    else 0
  else
    if h50 : 50 ≤ i.val then
      if h109 : i.val < 109 then
        secondLowerInterior59 ⟨i.val - 50, by omega⟩
      else if h144 : i.val < 144 then
        lowerNew35Numerators ⟨i.val - 109, by omega⟩
      else 0
    else 0

/-- All 400 original physical Q80 cells, combining the new interior
certificates and the already supplied genuine 93 exterior certificates.
No analytic envelope or selected-count identity is smuggled into the claim. -/
theorem second_round_all_400_exact (upper : Bool) (i : Fin 200) :
    iterate 2 upper i = secondRoundExactReceipts upper i := by
  cases upper with
  | true =>
      by_cases h100 : i.val < 100
      · let j : Fin 100 := ⟨i.val, h100⟩
        have hc : (⟨j.val, by omega⟩ : Fin 200) = i := by
          apply Fin.ext
          rfl
        have hr := second_upper_interior_100_actual j
        rw [hc] at hr
        simpa [secondRoundExactReceipts, h100, j] using hr
      · by_cases h158 : i.val < 158
        · let j : Fin 58 := ⟨i.val - 100, by omega⟩
          have hc : (⟨100 + j.val, by omega⟩ : Fin 200) = i := by
            apply Fin.ext
            dsimp [j]
            omega
          have hr := second_upper_new_58_actual j
          rw [hc] at hr
          simpa [secondRoundExactReceipts, h100, h158, j] using hr
        · have hz := second_upper_zero_from_158 i (by omega)
          simp [secondRoundExactReceipts, h100, h158, hz]
  | false =>
      by_cases h50 : 50 ≤ i.val
      · by_cases h109 : i.val < 109
        · let j : Fin 59 := ⟨i.val - 50, by omega⟩
          have hc : (⟨50 + j.val, by omega⟩ : Fin 200) = i := by
            apply Fin.ext
            dsimp [j]
            omega
          have hr := second_lower_interior_59_actual j
          rw [hc] at hr
          simpa [secondRoundExactReceipts, h50, h109, j] using hr
        · by_cases h144 : i.val < 144
          · let j : Fin 35 := ⟨i.val - 109, by omega⟩
            have hc : (⟨109 + j.val, by omega⟩ : Fin 200) = i := by
              apply Fin.ext
              dsimp [j]
              omega
            have hr := second_lower_new_35_actual j
            rw [hc] at hr
            simpa [secondRoundExactReceipts, h50, h109, h144, j] using hr
          · have hz := second_lower_zero_from_144 i (by omega)
            simp [secondRoundExactReceipts, h50, h109, h144, hz]
      · have hz := lower_first_fifty_zero 2 i (by omega)
        simp [secondRoundExactReceipts, h50, hz]

/-- The exact necessary-and-sufficient numerical check for ANY
proposed physical integer second-generation upper envelope. This does
NOT establish the original analytic closed-cell envelope F. -/
theorem second_round_ceiling_iff_receipts (ceiling : Table) :
    (∀ upper i, iterate 2 upper i ≤ ceiling upper i) ↔
    (∀ upper i, secondRoundExactReceipts upper i ≤ ceiling upper i) := by
  constructor
  · intro h upper i
    rw [← second_round_all_400_exact]
    exact h upper i
  · intro h upper i
    rw [second_round_all_400_exact]
    exact h upper i

/-- Physical bank winner count, not selected-count source multiplicity. -/
def isBankChoice : Choice → Bool
  | .bank _ => true
  | _ => false

theorem second_upper_100_bank_winner_count :
    (∑ j : Fin 100,
      if isBankChoice (roundDecision (iterate 1) true
        (⟨j.val, by omega⟩ : Fin 200)).choice then (1 : ℕ) else 0) = 90 := by
  simp_rw [second_upper_100_winning_choice_actual]
  decide

/-- Exactly 10 upper interior physical positions choose genuine Buchstab;
these do not conceal a bank winner or an extra bank mass payment. -/
theorem second_upper_buchstab_from_90 (j : Fin 100) (hj : 90 ≤ j.val) :
    (roundDecision (iterate 1) true
      (⟨j.val, by omega⟩ : Fin 200)).choice = .buchstab := by
  rw [second_upper_100_winning_choice_actual]
  have hnot : ¬j.val < 90 := by omega
  simp [secondUpper100WinningChoice, hnot]

end
end ImbalancedChen.Part5OriginalH430SecondRoundComplete400
