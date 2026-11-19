import ImbalancedChen.Part5OriginalH430FirstRoundExactActionIff

/-!
P5.6 / h34: first ORIGINAL Q80 generation, quantitative finite receipts.

Unlike the preceding first-round iff, this packet supplies actual INTEGER
candidate bounds for all 106 original bank rows and the exact numerical
59-cell lower Buchstab output. No generic paid-source premise is asserted.
The literal exporter divides EACH weighted suffix summand by the same q
before summing; the numerators below preserve that rounding order.
All finite comparisons are proposed kernel-decided Lean proofs. They have
NOT been compiled or replayed, so their correctness remains UNEVALUATED.

The constant ceiling here is deliberately coarse in the upper tail. It is
not the frozen analytic F, a later-round invariant, or h34 closure.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FirstRoundQuantitativeReceipts
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430FirstRoundExactActionIff
open Part5OriginalH430FirstRoundSourcePartition

/-- Literal Q80 lower numerators for physical indices 50..108 at
generation one. Each weighted term has its OWN integer /q before summing,
as in the original P2Selected430CausalOccurrenceExporter.suffix. -/
def lower59Numerators : Fin 59 → ℤ :=
  ![
  21623567292382372447434,
  21077303452251826906197,
  20541445272984303008578,
  20015603723276915891636,
  19499411188866468885477,
  18992519928742253730471,
  18494600667999599583355,
  18005341313073348028451,
  17524445776797208721576,
  17051632902212192800666,
  16586635475329182906535,
  16129199318165778694557,
  15679082454349877177987,
  15236054340432246277621,
  14799895156794727262742,
  14370395152694145809948,
  13947354040556831430203,
  13530580435145326280935,
  13119891333666361131702,
  12715111633285154087016,
  12316073682862124651302,
  11922616866039869725137,
  11534587213085596482008,
  11151837039141363420296,
  10774224606755093157210,
  10401613810762553416855,
  10033873883767107096299,
  9670879120622404187214,
  9312508620465418341312,
  8958646044975146634166,
  8609179391647493172653,
  8264000780980749757037,
  7923006256559903775977,
  7586095597112831011488,
  7253172139688226637481,
  6924142613174736974146,
  6598916981443925309468,
  6277408295457099643451,
  5959532553728236026698,
  5645208570582770081684,
  5334357851695365473567,
  5026904476429314965205,
  4722774986536355975576,
  4421898280808717549095,
  4124205515305453773403,
  3829630008802823558641,
  3538107153143884596280,
  3249574328185792297842,
  2963970821064723090969,
  2681237749518046990715,
  2401317989021511182669,
  2124156103515903561956,
  1849698279513068305448,
  1577892263385358020719,
  1308687301655731368037,
  1042034084117834123100,
  777884689626619553073,
  516192534410447006158,
  256912322765215023118
  ]

/-- All 59 first-round lower receipts are checked against the REAL
producer, not just a reimplemented or approximate suffix formula. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem first_lower_59_exact (j : Fin 59) :
    iterate 1 false (⟨j.val + 50, by omega⟩ : Fin 200) =
      lower59Numerators j := by
  fin_cases j <;> decide

/-- The maximum exact lower receipt occurs at physical index 50. -/
theorem first_lower_59_bounded (j : Fin 59) :
    lower59Numerators j ≤ 21623567292382372447434 := by
  fin_cases j <;> decide

/-- The TRUE original row-local arithmetic, including every divisor,
repeated weight and negative base, is bounded at the initial seed.
No phantom multiplication by target multiplicities is introduced. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem first_bank_106_initial_numerical_bound (k : Fin 106) :
    candidate seed (rows k) ≤ 29109517144010128037267 := by
  fin_cases k <;> decide

/-- A direct bound for every genuine first-generation lower suffix.
Only actual physical indices 50..108 are needed. -/
theorem first_lower_suffix_numerical_bound
    (i : Fin 200) (h50 : 50 ≤ i.val) (h109 : i.val < 109) :
    suffix seed true (i.val - 49) ≤ 21623567292382372447434 := by
  let j : Fin 59 := ⟨i.val - 50, by omega⟩
  have hij : (⟨j.val + 50, by omega⟩ : Fin 200) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  have hrec := first_lower_59_exact j
  rw [hij] at hrec
  calc
    suffix seed true (i.val - 49) ≤ iterate 1 false i :=
      first_lower_suffix_le_actual i h50
    _ = lower59Numerators j := hrec
    _ ≤ 21623567292382372447434 := first_lower_59_bounded j

/-- An explicit integer two-table ceiling on the ACTUAL first Q80
generation; this is numerical, not a supplied 430-round CLOSED-CELL
analytic envelope. No theorem for g>1 follows from this bound. -/
def firstRoundNumericalCeiling : Table :=
  fun upper _ => if upper then 29109517144010128037267 else 21623567292382372447434

private theorem authentic_seed_below_numerical_ceiling :
    ∀ upper i, iterate 0 upper i ≤ firstRoundNumericalCeiling upper i := by
  intro upper i
  cases upper with
  | false =>
      norm_num [iterate, seed, firstRoundNumericalCeiling]
  | true =>
      by_cases hi : i.val < 60
      · norm_num [iterate, seed, firstRoundNumericalCeiling,
          P2Selected430LiteralActionData.q, hi]
      · simp [iterate, seed, firstRoundNumericalCeiling, hi]

/-- First genuinely quantitative, two-table numerator majorant
obtained from the authentic seed and literal 106+59 receipts.
No bound on the frozen F or any later round is inferred. -/
theorem first_round_both_tables_numerical_ceiling :
    ∀ upper i, iterate 1 upper i ≤ firstRoundNumericalCeiling upper i := by
  apply first_round_safe_of_paid_actual_sources
    firstRoundNumericalCeiling authentic_seed_below_numerical_ceiling
  · intro i k _
    simpa [firstRoundNumericalCeiling] using
      first_bank_106_initial_numerical_bound k
  · intro i h50 h109
    simpa [firstRoundNumericalCeiling] using
      first_lower_suffix_numerical_bound i h50 h109

end
end ImbalancedChen.Part5OriginalH430FirstRoundQuantitativeReceipts
