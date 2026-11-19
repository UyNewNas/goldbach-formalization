import ImbalancedChen.Part5OriginalH430FirstRoundQuantitativeReceipts

/-!
P5.6 / h34: EXACT first-round Q80 numerators at every physical cell.

An exhaustive 100-entry upper table complements the already-present exact
59 lower numerators.  The upper numbers are the original maximum of genuine
retention and all 106 TARGETED bank offers from the frozen integer seed.
Signed negative offers are NOT added, and untargeted rows are NOT counted.
The scan winner is selected by the original left-to-right max, with all
candidate divisors and repeated weights unchanged.

Both physical tables are identified with a fully specified integer receipt
table.  In particular the five upper cells 95..99 are zero, strengthening
the previous 159-cell possible support to 154 cells. This is not a closed
F-envelope comparison, later-round induction or count theorem.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FirstRoundExact400
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430FirstRoundQuantitativeReceipts
open Part5OriginalH430FirstRoundActiveSupport
open Part5OriginalH430Q80InitialSupport

/-- Every possible nonzero upper numerator in the true first Q80 round,
ordered by physical index 0..99. This is not a synthetic uniform ceiling.
Exact row targets and sign-preserving maxima determine each entry. -/
def upper100Numerators : Fin 100 → ℤ :=
  ![
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    29109517144010128037267,
    28886991284558173495734,
    28886991284558173495734,
    28494751155472161150499,
    28150761195451506922535,
    28150761195451506922535,
    27376171044580813427812,
    27376171044580813427812,
    26332716080975708802052,
    26332716080975708802052,
    25694631676020723399342,
    25388212991439852232241,
    24048738793987756917441,
    24048738793987756917441,
    22480837448192808577221,
    22480837448192808577221,
    20621070576140687824105,
    20621070576140687824105,
    18774120111297126531702,
    18774120111297126531702,
    17907144781948119349657,
    17096821763972471460204,
    15323922953421760061180,
    15323922953421760061180,
    13365483423442724634256,
    13365483423442724634256,
    11232249114357028389140,
    11232249114357028389140,
    9027421219377577001502,
    9027421219377577001502,
    8269682432420232577004,
    6650807162841548739717,
    4461548392059221307064,
    4461548392059221307064,
    4461548392059221307064,
    4461548392059221307064,
    1309815934474742776558,
    1309815934474742776558,
    1309815934474742776558,
    1309815934474742776558,
    1309815934474742776558,
    0,
    0,
    0,
    0,
    0
  ]

/-- Candidate finite certificate against the actual original 106-row scan.
All 100 positions are checked individually against the REAL producer. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem first_upper_100_exact (j : Fin 100) :
    iterate 1 true (⟨j.val, by omega⟩ : Fin 200) =
      upper100Numerators j := by
  fin_cases j <;> decide

/-- The five upper physical cells 95..99 have exact zero receipts;
this does not follow from the old >=100 structural support cutoff. -/
theorem upper100_zero_from_95 (j : Fin 100) (hj : 95 ≤ j.val) :
    upper100Numerators j = 0 := by
  fin_cases j <;> simp_all [upper100Numerators]

/-- Original first-round UPPER support can be sharpened from 100 to 95
physical indices; this is an actual computed-zero conclusion. -/
theorem first_upper_round_zero_from_95 (i : Fin 200)
    (hi : 95 ≤ i.val) : iterate 1 true i = 0 := by
  by_cases h100 : i.val < 100
  · let j : Fin 100 := ⟨i.val, h100⟩
    have hcast : (⟨j.val, by omega⟩ : Fin 200) = i := by
      apply Fin.ext
      rfl
    have hreceipt := first_upper_100_exact j
    rw [hcast] at hreceipt
    rw [hreceipt]
    exact upper100_zero_from_95 j (by simpa [j] using hi)
  · exact first_upper_round_zero_from_hundred i (by omega)

/-- One exact integer table for BOTH original 200-cell Q80 outputs.
The lower window keeps the independently certified 59 values with the
original per-summand division. No approximation and no F substitution. -/
def firstRoundExactReceipts (upper : Bool) (i : Fin 200) : ℤ :=
  if upper then
    if h : i.val < 100 then upper100Numerators ⟨i.val, h⟩ else 0
  else
    if h50 : 50 ≤ i.val then
      if h109 : i.val < 109 then
        lower59Numerators ⟨i.val - 50, by omega⟩
      else 0
    else 0

/-- Exact original Q80 first update in all 400 physical table positions.
The first-round upper vector and the prior lower59 vector are brought
together; the other 241 slots are eliminated by genuine producer lemmas. -/
theorem first_round_all_400_exact (upper : Bool) (i : Fin 200) :
    iterate 1 upper i = firstRoundExactReceipts upper i := by
  cases upper with
  | true =>
      by_cases h100 : i.val < 100
      · let j : Fin 100 := ⟨i.val, h100⟩
        have hcast : (⟨j.val, by omega⟩ : Fin 200) = i := by
          apply Fin.ext
          rfl
        have hrec := first_upper_100_exact j
        rw [hcast] at hrec
        simpa [firstRoundExactReceipts, h100, j] using hrec
      · have hz := first_upper_round_zero_from_hundred i (by omega)
        simp [firstRoundExactReceipts, h100, hz]
  | false =>
      by_cases h50 : 50 ≤ i.val
      · by_cases h109 : i.val < 109
        · let j : Fin 59 := ⟨i.val - 50, by omega⟩
          have hcast : (⟨j.val + 50, by omega⟩ : Fin 200) = i := by
            apply Fin.ext
            dsimp [j]
            omega
          have hrec := first_lower_59_exact j
          rw [hcast] at hrec
          simpa [firstRoundExactReceipts, h50, h109, j] using hrec
        · have hz : iterate 1 false i = 0 :=
            first_round_outside_active_window_zero false i
              (Or.inr ⟨rfl, Or.inr (by omega)⟩)
          simp [firstRoundExactReceipts, h50, h109, hz]
      · have hz : iterate 1 false i = 0 :=
          first_round_outside_active_window_zero false i
            (Or.inr ⟨rfl, Or.inl (by omega)⟩)
        simp [firstRoundExactReceipts, h50, hz]

/-- Stronger first-generation two-table active support: at most
95 upper plus 59 lower positions, without claiming these are positive. -/
theorem first_round_nonzero_inside_154 (upper : Bool) (i : Fin 200)
    (hnonzero : iterate 1 upper i ≠ 0) :
    (upper = true ∧ i.val < 95) ∨
    (upper = false ∧ 50 ≤ i.val ∧ i.val < 109) := by
  cases upper with
  | true =>
      have h95 : i.val < 95 := by
        by_contra h
        exact hnonzero (first_upper_round_zero_from_95 i (by omega))
      exact Or.inl ⟨rfl, h95⟩
  | false =>
      rcases first_round_nonzero_only_inside_active_window false i hnonzero with
          ⟨hfalse, _⟩ | ⟨hfalse, h50, h109⟩
      · cases hfalse
      · exact Or.inr ⟨hfalse, h50, h109⟩

/-- Any proposed integer first-round ceiling can now be compared with
explicit physical receipts rather than a global maximum. It still
requires an actual F comparison at the relevant query endpoints. -/
theorem first_round_ceiling_iff_receipts (ceiling : Table) :
    (∀ upper i, iterate 1 upper i ≤ ceiling upper i) ↔
      (∀ upper i, firstRoundExactReceipts upper i ≤ ceiling upper i) := by
  constructor
  · intro h upper i
    rw [← first_round_all_400_exact]
    exact h upper i
  · intro h upper i
    rw [first_round_all_400_exact]
    exact h upper i

end
end ImbalancedChen.Part5OriginalH430FirstRoundExact400
