import ImbalancedChen.Part5OriginalH430SecondRoundComplete400

/-!
P5.6/h34 ORIGINAL Q80 generation three, new exterior only.
The upper 158..192 and lower 144..199 entries are the first newly
activated cells outside the exact generation-two support. Both come
from the original opposite-table per-summand integer Buchstab suffix.
The original 106-row scan is shown irrelevant for upper indices >=100.
No surrogate producer, altered Q, analytic F envelope, selected count,
or additional payment is introduced.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ThirdRoundExterior91
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430SecondRoundComplete400
open Part5OriginalH430SecondRoundExteriorSources
open Part5OriginalH430TwoRoundCausalCutoffs
open Part5OriginalH430Q80InitialSupport
open Part5OriginalH430FirstRoundActiveSupport

/-- No row of the ORIGINAL 106-bank can target a physical index >=100. -/
private theorem scan_high_no_bank
    (old : Table) (i : Fin 200) (hi : 100 <= i.val)
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

/-- The real third-generation upper exterior has no retention
or bank contribution: only the old lower-table Buchstab read remains. -/
theorem third_upper_exterior_from_true_suffix
    (i : Fin 200) (hi : 158 <= i.val) :
    iterate 3 true i =
      max 0 (suffix (iterate 2) false (i.val - 49)) := by
  change (scan (iterate 2) i (List.finRange 106)
    (ordinaryDecision (iterate 2) true i)).numerator = _
  rw [scan_high_no_bank (iterate 2) i (by omega)
    (List.finRange 106) (ordinaryDecision (iterate 2) true i)]
  rw [ordinaryDecision_numerator]
  have h50 : 50 <= i.val := by omega
  have hret : iterate 2 true i = 0 := second_upper_zero_from_158 i hi
  have hk : max 50 (i.val - 49) = i.val - 49 := by omega
  simp [h50, hret, hk]

/-- The real third-generation lower exterior has no retained positive
value, and has no bank actions at all. -/
theorem third_lower_exterior_from_true_suffix
    (i : Fin 200) (hi : 144 <= i.val) :
    iterate 3 false i =
      max 0 (suffix (iterate 2) true (i.val - 49)) := by
  change (ordinaryDecision (iterate 2) false i).numerator = _
  rw [ordinaryDecision_numerator]
  have h50 : 50 <= i.val := by omega
  have hret : iterate 2 false i = 0 :=
    second_lower_zero_from_144 i hi
  simp [h50, hret]

/-- The all-400 second-round receipts are the same genuine Q80 iterate. -/
private theorem second_round_read_receipt (upper : Bool) (j : ℕ) :
    read (iterate 2) upper j =
      read secondRoundExactReceipts upper j := by
  by_cases hj : j < 200
  · simp only [read, dif_pos hj]
    exact second_round_all_400_exact upper ⟨j, hj⟩
  · simp [read, hj]

/-- The exact original weighted suffix reads the certified previous table,
and still divides EACH individual summand by q before summing. -/
theorem third_suffix_second_round_receipts (upper : Bool) (k : ℕ) :
    suffix (iterate 2) upper k =
      suffix secondRoundExactReceipts upper k := by
  unfold suffix
  apply Finset.sum_congr rfl
  intro r hr
  rw [second_round_read_receipt upper (k + r)]

/-- Numerators newly activated in upper positions 158..192 (35 cells). -/
def thirdUpperNew35Numerators : Fin 35 → ℤ :=
  ![
    281424519658986784614,
    255340690406752053791,
    230962996015118936271,
    208256549169084856676,
    187130271294680800947,
    167552219372329284734,
    149457374464747863036,
    132800042337441876462,
    117482567645643733887,
    103478463262272712877,
    90683365276135387154,
    79073641795422898088,
    68535709982427675049,
    59048857913724828600,
    50505462708875634908,
    42887496097444086906,
    36137447328737893406,
    30202104145582246063,
    24986727312449988453,
    20477851716050865201,
    16576938250534171690,
    13272738320955437152,
    10463694804908777953,
    8140745110102516593,
    6203849859788000507,
    4646020119727694046,
    3429886308625213641,
    2484911144770043822,
    1720260594358327166,
    1132743370822384345,
    719237188523957360,
    476686916686820196,
    284347382345791563,
    141350144015170279,
    46845098118559360
  ]

/-- Numerators newly activated in lower positions 144..199 (56 cells). -/
def thirdLowerNew56Numerators : Fin 56 → ℤ :=
  ![
    658873863363749544747,
    625550755451648897520,
    592455110799459586816,
    559583845123905217965,
    526933936451413966400,
    494502423450937786884,
    463716054588931688290,
    434503594564895334755,
    406796835012303369935,
    380530444320738764896,
    355641826356301458635,
    332070987452689168971,
    309760411097530122909,
    288654939785677368767,
    268701663553813477922,
    249849814749354138885,
    232050668621709821461,
    215257449355844322215,
    199425241197090264245,
    184510904342637945359,
    170472995299264672987,
    157271691428946607282,
    144868719424198009139,
    133227287473494900314,
    122312020894122921348,
    112088901025386659620,
    102525207189458653392,
    93589461540345909300,
    85251376633613440232,
    77481805560720839511,
    70252694502182716967,
    63537037563332101745,
    57308833765315459967,
    51543046072140008617,
    46215562342183896199,
    41303158099617696437,
    36783461027716969342,
    32634917092111632724,
    28836758207656038443,
    25368971367848059145,
    22212269160607216040,
    19348061598769227096,
    16758429197893164859,
    14426097237931287416,
    12334411149002128916,
    10467312964954363926,
    8809318791630393239,
    7345497239751135746,
    6061448775162386015,
    4943285941822304775,
    3977614415382016033,
    3151514847528729201,
    2452525463434189868,
    1868625376690636638,
    1388218588031071224,
    1000118635929088657
  ]

/-- Real original third round equals each of the 35 exact upper exterior
integer receipts. No aggregate/divide interchange is used. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem third_upper_new_35_actual (j : Fin 35) :
    iterate 3 true (⟨158 + j.val, by omega⟩ : Fin 200) =
      thirdUpperNew35Numerators j := by
  rw [third_upper_exterior_from_true_suffix _ (by omega)]
  rw [third_suffix_second_round_receipts]
  fin_cases j <;> decide

/-- Real original third round equals each of the 56 exact lower exterior
integer receipts, through the actual opposite-table suffix. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem third_lower_new_56_actual (j : Fin 56) :
    iterate 3 false (⟨144 + j.val, by omega⟩ : Fin 200) =
      thirdLowerNew56Numerators j := by
  rw [third_lower_exterior_from_true_suffix _ (by omega)]
  rw [third_suffix_second_round_receipts]
  fin_cases j <;> decide

/-- All 35 NEW upper cells are strictly positive integer numerators. -/
theorem third_upper_new_35_positive (j : Fin 35) :
    0 < thirdUpperNew35Numerators j := by
  fin_cases j <;> decide

/-- All 56 NEW lower cells are strictly positive integer numerators. -/
theorem third_lower_new_56_positive (j : Fin 56) :
    0 < thirdLowerNew56Numerators j := by
  fin_cases j <;> decide

/-- Physical activation at all 91 exterior sites, not a new
U3/U4 selected-count mass or 91 independent payments. -/
theorem third_upper_new_35_genuinely_active (j : Fin 35) :
    0 < iterate 3 true (⟨158 + j.val, by omega⟩ : Fin 200) := by
  rw [third_upper_new_35_actual]
  exact third_upper_new_35_positive j

theorem third_lower_new_56_genuinely_active (j : Fin 56) :
    0 < iterate 3 false (⟨144 + j.val, by omega⟩ : Fin 200) := by
  rw [third_lower_new_56_actual]
  exact third_lower_new_56_positive j

/-- The improved TRUE generation-two lower cutoff 144 (not 149)
propagates to a TRUE third-generation upper zero tail from 193. -/
theorem third_upper_zero_from_193 (i : Fin 200)
    (hi : 193 <= i.val) : iterate 3 true i = 0 := by
  have hread : ∀ j : Fin 200, 144 <= j.val →
      iterate 2 false j = 0 := by
    intro j hj
    exact second_lower_zero_from_144 j hj
  have hs : suffix (iterate 2) false (i.val - 49) = 0 :=
    actual_suffix_zero_of_tail (iterate 2) false 144
      (i.val - 49) hread (by omega)
  rw [third_upper_exterior_from_true_suffix i (by omega), hs]
  simp

/-- The full third-round support cannot escape 193 upper positions and
150 lower positions. This is a support cap of 343, not a count estimate. -/
theorem third_round_nonzero_support (upper : Bool) (i : Fin 200)
    (h : iterate 3 upper i ≠ 0) :
    (upper = true ∧ i.val < 193) ∨
    (upper = false ∧ 50 <= i.val) := by
  cases upper with
  | false =>
      have h50 : 50 <= i.val := by
        by_contra hn
        exact h (lower_first_fifty_zero 3 i (by omega))
      exact Or.inr ⟨rfl, h50⟩
  | true =>
      have h193 : i.val < 193 := by
        by_contra hn
        exact h (third_upper_zero_from_193 i (by omega))
      exact Or.inl ⟨rfl, h193⟩

end
end ImbalancedChen.Part5OriginalH430ThirdRoundExterior91
