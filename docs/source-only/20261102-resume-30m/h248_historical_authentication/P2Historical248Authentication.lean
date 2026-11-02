import ImbalancedChen.P2HistoricalSourceJSON
import ImbalancedChen.P2HistoricalLowerBankAncestry
import ImbalancedChen.Part5AdoptedH248Data

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The only file IO is original_text%, run only if the USER compiles. The
total pure parser and every closed `by decide` guard below are UNEVALUATED.
No guard truth is a parameter. No producer, checker, numerical replay,
compiler or generator was run to prepare this file.

The schedule is the frozen historical 24→56→120→184→248 schedule. It has
no seed-only430 input. All source values read the immutable old table;
only retention reads the accumulating table. The final theorem still
requires the UNPROVED analytic H247 invariant. This source claims no
analytic seed, W1/W2 licence, endpoint licence, or full original target.
-/

namespace ImbalancedChen.P2Historical248Authentication

noncomputable section

open P2HistoricalSourceJSON P2TableActionSourceOnly P2SimultaneousTableSourceOnly
open P2HistoricalBankLogWeights P2HistoricalLowerBankAncestry
open Certificates.P2HistoricQ80DefectLookup
open P2HistoricSavedOrdinaryDefectAssembly
open scoped BigOperators




def text24 : String := original_text% "../goldbach-research/certify_finite_step_table.json"
def textOldW2 : String := original_text% "../goldbach-research/certify_finite_w2_action_bank.json"
def text56 : String := original_text% "../goldbach-research/certify_combined_finite_table.json"
def text120 : String := original_text% "../goldbach-research/certify_lower_k_finite_table.json"
def text184 : String := original_text% "../goldbach-research/certify_variable_kernel_finite_table.json"
def textNewW2 : String := original_text% "../goldbach-research/expanded-w2-midpoint-bank33-v1.json"
def text248 : String := original_text% "../goldbach-research/expanded-w2-midpoint-table248-v1.json"
def textSavings : String := original_text% "../goldbach-research/certify_w2_variable_kernel_savings.json"

def json24 := parsed text24
def jsonOldW2 := parsed textOldW2
def json56 := parsed text56
def json120 := parsed text120
def json184 := parsed text184
def jsonNewW2 := parsed textNewW2
def json248 := parsed text248
def jsonSavings := parsed textSavings

def sourceTexts : List String :=
  [text24,textOldW2,text56,text120,text184,textNewW2,text248,textSavings]

/-- All eight actual original files must parse completely. -/
theorem original_files_parse_guard :
    sourceTexts.all (fun s => (parse s).isSome) = true := by decide

/-- Total decoding is accompanied by the closed IndexOK guards below;
modulo is only a totality device, never a licence to wrap a source index. -/
def finIndex (v : Value) : Fin 200 := ⟨natural v % 200, Nat.mod_lt _ (by decide)⟩

theorem finIndex_exact {v : Value} (hv : IndexOK v) :
    (finIndex v).val = natural v := by
  rcases hv with ⟨_, hlo, hhi⟩
  have hn : natural v < 200 := by dsimp [natural]; omega
  exact Nat.mod_eq_of_lt hn

def readWeight (v : Value) : P2OriginalW2CandidateIntegerABI.WeightRow :=
  ⟨finIndex (at v 0), integer (at v 1), integer (at v 2)⟩

def readW1Weight (v : Value) : P2OriginalW2CandidateIntegerABI.WeightRow :=
  ⟨finIndex (at v 0), integer (at v 1), integer (at v 1)⟩

def readPoint (v : Value) : P2OriginalW2CandidateIntegerABI.PointRow := ⟨finIndex (at v 0), integer (at v 1)⟩

structure SourceW1 where
  s : ℚ
  s0 : ℚ
  originalBase : ℤ
  effectiveBase : ℤ
  pointIndex : Fin 200
  feedback : List P2OriginalW2CandidateIntegerABI.WeightRow
  targets : List (Fin 200)

def readW1 (v : Value) : SourceW1 :=
  ⟨rational (field v "s"), rational (field v "s0"),
    integer (field v "base_lower"), integer (field v "base_lower"),
    finIndex (field v "point_index"),
    (items (field v "feedback_weights")).map readW1Weight,
    (items (field v "targets")).map finIndex⟩

def readW2 (v : Value) : P2OriginalW2CandidateIntegerABI.Action :=
  ⟨integer (field v "base_lower_numerator"),
    (items (field v "Gamma1_points")).map readPoint,
    (items (field v "negative_h_weights")).map
      (fun row => (items (field row "weights")).map readWeight),
    (items (field v "ordinary_pair_H_weights")).map
      (fun row => (items (field row "weights")).map readWeight),
    (items (field v "targets")).map finIndex⟩

def w1Original : List SourceW1 := (items (field json24 "candidate_bank")).map readW1
def w2Original : List P2OriginalW2CandidateIntegerABI.Action := (items (field jsonOldW2 "actions")).map readW2
def w2Added : List P2OriginalW2CandidateIntegerABI.Action := (items (field jsonNewW2 "actions")).map readW2

def w1Retained : List SourceW1 :=
  (w1Original.zip (items (field json120 "W1_baseline_updates"))).map
    (fun p => { p.1 with effectiveBase := integer (field p.2 "new_base") })

def w2LowerK : List P2OriginalW2CandidateIntegerABI.Action :=
  (w2Original.zip (items (field json120 "W2_baseline_updates"))).map
    (fun p => { p.1 with base := integer (field p.2 "new_base") })

def w2Retained : List P2OriginalW2CandidateIntegerABI.Action :=
  (w2Original.zip (items (field json184 "W2_baseline_updates"))).map
    (fun p => { p.1 with base := integer (field p.2 "new_base") })

def gridAt (j : Nat) : ℚ := 1 + (j : ℚ)/50
def parameters (v : Value) : List ℚ := (items (field v "parameters")).map rational
def scalarArrayOK (v : Value) : Bool := (items v).all (fun x => decide (ScalarOK x))
def indexArrayOK (v : Value) : Bool := (items v).all (fun x => decide (IndexOK x))
def integerFieldsOK (v : Value) (ks : List String) : Bool :=
  ks.all (fun k => decide (ScalarOK (field v k)))
def rationalFieldsOK (v : Value) (ks : List String) : Bool :=
  ks.all (fun k => decide (RationalOK (field v k)))

def w1RowOK (v : Value) : Bool :=
  decide (RationalOK (field v "s") ∧ RationalOK (field v "s0") ∧
    ScalarOK (field v "base_lower") ∧ IndexOK (field v "point_index") ∧
    0 < rational (field v "s") ∧ rational (field v "s") < rational (field v "s0") ∧
    gridAt (natural (field v "point_index")) < rational (field v "s0") ∧
    rational (field v "s0") ≤ gridAt (natural (field v "point_index")+1)) &&
  (items (field v "feedback_weights")).all (fun r =>
    decide ((items r).length = 2 ∧ IndexOK (at r 0) ∧ ScalarOK (at r 1) ∧
      0 ≤ integer (at r 1))) && indexArrayOK (field v "targets") &&
  decide ((items (field v "targets")).map natural =
    (List.range 200).filter (fun j => decide (gridAt (j+1) ≤ rational (field v "s"))))

def w2RowOK (v : Value) : Bool :=
  decide ((parameters v).length = 5 ∧ ScalarOK (field v "base_lower_numerator")) &&
  (items (field v "parameters")).all (fun x => decide (RationalOK x)) &&
  (items (field v "Gamma1_points")).all (fun r =>
    decide ((items r).length = 2 ∧ IndexOK (at r 0) ∧ ScalarOK (at r 1) ∧
      0 < integer (at r 1))) &&
  decide ((items (field v "Gamma1_points")).length = 2 ∧
    integer (at (at (field v "Gamma1_points") 0) 1) = 4 ∧
    integer (at (at (field v "Gamma1_points") 1) 1) = 1 ∧
    gridAt (natural (at (at (field v "Gamma1_points") 0) 0)) <
      rational (at (field v "parameters") 1) ∧
    rational (at (field v "parameters") 1) ≤
      gridAt (natural (at (at (field v "Gamma1_points") 0) 0)+1) ∧
    gridAt (natural (at (at (field v "Gamma1_points") 1) 0)) <
      rational (at (field v "parameters") 2) ∧
    rational (at (field v "parameters") 2) ≤
      gridAt (natural (at (at (field v "Gamma1_points") 1) 0)+1)) &&
  (["negative_h_weights", "ordinary_pair_H_weights"].all (fun k =>
    (items (field v k)).all (fun row => (items (field row "weights")).all
      (fun r => decide ((items r).length = 3 ∧ IndexOK (at r 0) ∧
        ScalarOK (at r 1) ∧ ScalarOK (at r 2) ∧
        0 ≤ integer (at r 1) ∧ integer (at r 1) ≤ integer (at r 2)))))) &&
  indexArrayOK (field v "targets") &&
  decide ((items (field v "targets")).map natural =
    (List.range 200).filter (fun j => decide (gridAt (j+1) ≤ rational (at (field v "parameters") 0)))) &&
  decide ((items (field v "negative_h_weights")).map (fun r => natural (field r "gamma")) = [2,3,4] ∧
    (items (field v "ordinary_pair_H_weights")).map (fun r => natural (field r "gamma")) = [5,6,7,8])

def tableShapeOK (v : Value) : Bool :=
  decide (natural (field v "grid_denominator") = 50 ∧
    integer (field v "fixed_point_denominator") = (tableQ : ℤ) ∧
    (items (field v "grid")).map rational = (List.range 201).map gridAt) &&
  ["H_cell_lower_numerators", "h_cell_lower_numerators"].all (fun k =>
    decide ((items (field v k)).length = 200) && scalarArrayOK (field v k))

/-- No silently wrapped index, truncated zip, omitted group, changed
normalization, or defaulted malformed scalar is admitted by this guard. -/
theorem original_schema_guard :
    [json24,json56,json120,json184,json248].all tableShapeOK = true ∧
    (items (field json24 "candidate_bank")).all w1RowOK = true ∧
    (items (field jsonOldW2 "actions")).all w2RowOK = true ∧
    (items (field jsonNewW2 "actions")).all w2RowOK = true ∧
    (items (field json24 "log_weight_lower_numerators")).length = 200 ∧
    scalarArrayOK (field json24 "log_weight_lower_numerators") = true ∧
    (items (field json120 "W1_baseline_updates")).length = 70 ∧
    (items (field json120 "W2_baseline_updates")).length = 3 ∧
    (items (field json184 "W2_baseline_updates")).length = 3 ∧
    (items (field jsonSavings "actions")).length = 3 ∧
    (items (field json120 "W1_baseline_updates")).all (fun v =>
      integerFieldsOK v ["old_base","increment","new_base"] &&
      rationalFieldsOK v ["s","s0","mass_lower"]) = true ∧
    (items (field json120 "W2_baseline_updates")).all (fun v =>
      integerFieldsOK v ["old_base","increment","new_base"] &&
      rationalFieldsOK v ["old_cost_lower"]) = true ∧
    (items (field json184 "W2_baseline_updates")).all (fun v =>
      integerFieldsOK v ["original_base","K_recalibration","box_gain","new_base"] &&
      rationalFieldsOK v ["original_positive_cost_lower"]) = true ∧
    (items (field jsonSavings "actions")).all (fun v =>
      rationalFieldsOK v ["seed_gain_lower"]) = true ∧
    ((items (field jsonOldW2 "actions") ++ items (field jsonNewW2 "actions")).map parameters).Nodup := by decide

def historyLabels (v : Value) : List Nat :=
  (items (field v "history")).map (fun row => natural (field row "generation"))

/-- Metadata fixes the recorded input/output generations and retained K
anchors. These are structural statements, not uses of recorded hashes. -/
theorem original_metadata_guard :
    natural (field json24 "generations") = 24 ∧
    rational (field json24 "initial_seed") = 2327/100000 ∧
    rational (field json24 "K") = 681/100 ∧ rational (field jsonOldW2 "K") = 681/100 ∧
    [natural (field json56 "initial_generations"), natural (field json56 "additional_generations"),
      natural (field json56 "total_finite_generations")] = [24,32,56] ∧
    [natural (field json120 "initial_generations"), natural (field json120 "additional_generations"),
      natural (field json120 "total_finite_generations")] = [56,64,120] ∧
    [natural (field json184 "initial_generations"), natural (field json184 "additional_generations"),
      natural (field json184 "total_finite_generations")] = [120,64,184] ∧
    [natural (field json248 "initial_generations"), natural (field json248 "additional_generations"),
      natural (field json248 "total_finite_generations")] = [184,64,248] ∧
    rational (field json120 "K") = 67633/10000 ∧
    rational (field json184 "K_W1_retained") = 67633/10000 ∧
    rational (field json248 "K_W1_retained") = 67633/10000 ∧
    rational (field json184 "K_W2") = 67619/10000 ∧
    rational (field json248 "K_W2") = 67619/10000 ∧
    rational (field jsonNewW2 "K") = 67619/10000 ∧
    historyLabels json24 = (List.range 24).map (·+1) ∧
    historyLabels json56 = (List.range 32).map (·+1) ∧
    [json120,json184,json248].all (fun v => decide (historyLabels v = (List.range 64).map (·+1))) = true ∧
    [jsonOldW2,jsonNewW2].all (fun v => decide
      ((items (field v "grid")).map rational = (List.range 201).map gridAt ∧
        integer (field v "Q") = (tableQ : ℤ))) = true := by decide

def positiveCost (a : Value) : ℚ :=
  let c := field a "ordinary_components"
  ((integer (field (field c "bad5_positive_replacement") "lower_numerator") +
    integer (field (field c "switched_cost") "lower_numerator") : ℤ) : ℚ) / tableQ

def w2Recalibration (newK : ℚ) (a : Value) : ℤ :=
  ⌊(tableQ : ℚ) * (681/100-newK) * positiveCost a / (5*(681/100))⌋

def w1UpdateOK (p : Value × Value) : Bool :=
  let a := readW1 p.1
  let u := p.2
  decide (rational (field u "s") = a.s ∧ rational (field u "s0") = a.s0 ∧
    integer (field u "old_base") = a.originalBase ∧
    rational (field u "mass_lower") = P2OriginalW1CandidateIntegerABI.recalibrationMass a.s a.s0 ∧
    integer (field u "increment") = P2OriginalW1CandidateIntegerABI.baselineIncrement a.s a.s0 ∧
    integer (field u "new_base") = P2OriginalW1CandidateIntegerABI.recalibratedBase a.originalBase a.s a.s0)

def w2LowerUpdateOK (p : Value × Value) : Bool :=
  let a := p.1
  let u := p.2
  decide (parameters a = parameters u ∧
    integer (field u "old_base") = integer (field a "base_lower_numerator") ∧
    rational (field u "old_cost_lower") = positiveCost a ∧
    integer (field u "increment") = w2Recalibration (67633/10000) a ∧
    integer (field u "new_base") = integer (field a "base_lower_numerator") + w2Recalibration (67633/10000) a)

def w2VariableUpdateOK (p : (Value × Value) × Value) : Bool :=
  let a := p.1.1
  let u := p.1.2
  let g := p.2
  let box := ⌊(tableQ : ℚ) * rational (field g "seed_gain_lower")⌋
  decide (parameters a = parameters u ∧ parameters a = parameters g ∧
    integer (field u "original_base") = integer (field a "base_lower_numerator") ∧
    rational (field u "original_positive_cost_lower") = positiveCost a ∧
    integer (field u "K_recalibration") = w2Recalibration (67619/10000) a ∧
    integer (field u "box_gain") = box ∧
    integer (field u "new_base") = integer (field a "base_lower_numerator") +
      w2Recalibration (67619/10000) a + box)

def w2AddedBaselineOK (a : Value) : Bool :=
  let gain := field a "variable_kernel_saving"
  let extra := if text gain = "null" then 0
    else ⌊(tableQ : ℚ) * rational (field gain "seed_gain_lower")⌋
  integerFieldsOK a ["base_lower_numerator","coarse_base_lower_numerator","variable_kernel_seed_floor"] &&
  (if text gain = "null" then true else rationalFieldsOK gain ["seed_gain_lower"]) &&
  decide (integer (field a "variable_kernel_seed_floor") = extra ∧
    integer (field a "base_lower_numerator") = integer (field a "coarse_base_lower_numerator") + extra)

/-- Recompute all70+3+3 copied integer bases from original fields and the
producer's exact48-term lower log / rational floor formulas. Primitive
cost and variable-gain ANALYTIC certificates are not asserted here. -/
theorem original_baselines_guard :
    ((items (field json24 "candidate_bank")).zip
      (items (field json120 "W1_baseline_updates"))).all w1UpdateOK = true ∧
    ((items (field jsonOldW2 "actions")).zip
      (items (field json120 "W2_baseline_updates"))).all w2LowerUpdateOK = true ∧
    (((items (field jsonOldW2 "actions")).zip
      (items (field json184 "W2_baseline_updates"))).zip
      (items (field jsonSavings "actions"))).all w2VariableUpdateOK = true ∧
    (items (field jsonNewW2 "actions")).all w2AddedBaselineOK = true ∧
    (items (field jsonOldW2 "actions")).all (fun a =>
      ["bad5_positive_replacement", "switched_cost"].all (fun k => decide
        (integer (field (field (field a "ordinary_components") k) "denominator") = (tableQ : ℤ)))) = true := by decide

/-- Literal original stage banks. The three old W2 actions are recalibrated
FROM their original baselines at120 and184; they are not cumulatively
recosted. The70 W1 K1 bases are copied unchanged after120. -/
def sourceW1Schedule (n : Nat) : List SourceW1 := if n < 56 then w1Original else w1Retained
def sourceW2Schedule (n : Nat) : List P2OriginalW2CandidateIntegerABI.Action :=
  if n < 24 then []
  else if n < 56 then w2Original
  else if n < 120 then w2LowerK
  else if n < 184 then w2Retained
  else w2Retained ++ w2Added

/-- W1's existing ABI stores oldBase before its own recalibration. This
adapter encodes an ALREADY selected effective integer by subtracting that
same increment once. originalBase remains separately preserved above.
This adapter makes no analytic oldBase assertion. Its exact candidate
equality is proved below for arbitrary signed effective bases. -/
def SourceW1.toABI (a : SourceW1) : P2OriginalW1CandidateIntegerABI.Action :=
  ⟨a.effectiveBase - P2OriginalW1CandidateIntegerABI.baselineIncrement a.s a.s0, a.s, a.s0,
    a.pointIndex, a.feedback, a.targets⟩

theorem SourceW1.toABI_base (a : SourceW1) : a.toABI.base = a.effectiveBase := by
  simp [SourceW1.toABI, P2OriginalW1CandidateIntegerABI.Action.base, P2OriginalW1CandidateIntegerABI.recalibratedBase]

def designatedW1 (n : Nat) : List P2OriginalW1CandidateIntegerABI.Action := (sourceW1Schedule n).map SourceW1.toABI
def designatedW2 (n : Nat) : List P2OriginalW2CandidateIntegerABI.Action := sourceW2Schedule n

def sourceWeightSum (old : Table) (upper : Bool) : List P2OriginalW2CandidateIntegerABI.WeightRow → ℤ
  | [] => 0
  | r :: rs => old upper r.index * r.lower / (tableQ : ℤ) + sourceWeightSum old upper rs

def sourcePointSum (old : Table) : List P2OriginalW2CandidateIntegerABI.PointRow → ℤ
  | [] => 0
  | r :: rs => old true r.index * r.multiplicity + sourcePointSum old rs

theorem sourceWeightSum_eq (old : Table) (upper : Bool) (rs : List P2OriginalW2CandidateIntegerABI.WeightRow) :
    sourceWeightSum old upper rs = P2OriginalW2CandidateIntegerABI.weightedSum old upper rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [sourceWeightSum, P2OriginalW2CandidateIntegerABI.weightedSum, P2OriginalW2CandidateIntegerABI.q, ih]

theorem sourcePointSum_eq (old : Table) (rs : List P2OriginalW2CandidateIntegerABI.PointRow) :
    sourcePointSum old rs = P2OriginalW2CandidateIntegerABI.pointSum old rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [sourcePointSum, P2OriginalW2CandidateIntegerABI.pointSum, ih]

def sourceW1Value (old : Table) (a : SourceW1) : ℤ :=
  a.effectiveBase + old true a.pointIndex + sourceWeightSum old false a.feedback

def sourceW2Value (old : Table) (a : P2OriginalW2CandidateIntegerABI.Action) : ℤ :=
  a.base + (sourcePointSum old a.points + sourceWeightSum old false a.negativeRows.flatten +
    sourceWeightSum old true a.pairRows.flatten) / 5

theorem sourceW1Value_eq (old : Table) (a : SourceW1) :
    sourceW1Value old a = P2OriginalW1CandidateIntegerABI.candidate old a.toABI := by
  simp [sourceW1Value, P2OriginalW1CandidateIntegerABI.candidate, sourceWeightSum_eq, SourceW1.toABI_base,
    SourceW1.toABI]

theorem sourceW2Value_eq (old : Table) (a : P2OriginalW2CandidateIntegerABI.Action) :
    sourceW2Value old a = P2OriginalW2CandidateIntegerABI.candidate old a := by
  simp only [sourceW2Value, P2OriginalW2CandidateIntegerABI.candidate, P2OriginalW2CandidateIntegerABI.total, sourcePointSum_eq, sourceWeightSum_eq]

def sourceW1Apply (old current : Table) (a : SourceW1) : Table := fun side i =>
  if side = true ∧ i ∈ a.targets then max (current side i) (sourceW1Value old a)
  else current side i

def sourceW2Apply (old current : Table) (a : P2OriginalW2CandidateIntegerABI.Action) : Table := fun side i =>
  if side = true ∧ i ∈ a.targets then max (current side i) (sourceW2Value old a)
  else current side i

theorem sourceW1Apply_eq (old current : Table) (a : SourceW1) :
    sourceW1Apply old current a = P2OriginalW1CandidateIntegerABI.apply old current a.toABI := by
  funext side i
  simp only [sourceW1Apply, P2OriginalW1CandidateIntegerABI.apply, sourceW1Value_eq, SourceW1.toABI]

theorem sourceW2Apply_eq (old current : Table) (a : P2OriginalW2CandidateIntegerABI.Action) :
    sourceW2Apply old current a = P2OriginalW2CandidateIntegerABI.apply old current a := by
  funext side i
  simp only [sourceW2Apply, P2OriginalW2CandidateIntegerABI.apply, sourceW2Value_eq]

def sourceW1Bank (old : Table) (current : Table) : List SourceW1 → Table
  | [] => current
  | a :: bank => sourceW1Bank old (sourceW1Apply old current a) bank

def sourceW2Bank (old : Table) (current : Table) : List P2OriginalW2CandidateIntegerABI.Action → Table
  | [] => current
  | a :: bank => sourceW2Bank old (sourceW2Apply old current a) bank

theorem sourceW1Bank_eq (old current : Table) (bank : List SourceW1) :
    sourceW1Bank old current bank = applyW1Bank old current (bank.map SourceW1.toABI) := by
  induction bank generalizing current with
  | nil => rfl
  | cons a bank ih =>
      simp only [sourceW1Bank, List.map_cons, applyW1Bank, sourceW1Apply_eq, ih]

theorem sourceW2Bank_eq (old current : Table) (bank : List P2OriginalW2CandidateIntegerABI.Action) :
    sourceW2Bank old current bank = applyW2Bank old current bank := by
  induction bank generalizing current with
  | nil => rfl
  | cons a bank ih => simp only [sourceW2Bank, applyW2Bank, sourceW2Apply_eq, ih]

def savedWeights : List ℤ :=
  (items (field json24 "log_weight_lower_numerators")).map integer

def sourceWeight (j : Nat) : ℤ := (savedWeights[j]?).getD 0

/-- Actual original rounded-log outputs, compared in the kernel with J's
proved historical scalar interpreter; hash equality is not used. -/
theorem original_log_weights_guard :
    savedWeights = List.ofFn (fun j : Fin 200 => logWeight j.val) := by decide

theorem sourceWeight_eq {j : Nat} (hj : j < 200) : sourceWeight j = logWeight j := by
  simp [sourceWeight, original_log_weights_guard, List.getElem?_ofFn, hj]

def sourceSuffix (old : Table) (upper : Bool) (k : Nat) : ℤ :=
  ∑ j ∈ Finset.range (200-k), read old upper (k+j) * sourceWeight (k+j) / (tableQ : ℤ)

theorem sourceSuffix_eq (old : Table) (upper : Bool) (k : Nat) :
    sourceSuffix old upper k = suffixNumerator historicalLogWeights old upper k := by
  unfold sourceSuffix suffixNumerator
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  rw [sourceWeight_eq (by omega)]
  rfl

def sourceBuchstab (old : Table) : Table := fun upper i =>
  if 50 ≤ i.val then max (old upper i)
    (sourceSuffix old (!upper) (if upper then max 50 (i.val-49) else i.val-49))
  else old upper i

theorem sourceBuchstab_eq (old : Table) : sourceBuchstab old = buchstabStep old := by
  funext upper i
  simp only [sourceBuchstab, buchstabStep, sourceSuffix_eq]

/-- Direct source reconstruction: Buchstab, then all W1 maxima, then all
W2 maxima. Candidates always read old, on both sides of every bank fold. -/
def sourceRound (old : Table) (w1 : List SourceW1) (w2 : List P2OriginalW2CandidateIntegerABI.Action) : Table :=
  sourceW2Bank old (sourceW1Bank old (sourceBuchstab old) w1) w2

theorem sourceRound_eq_oneRound (old : Table) (w1 : List SourceW1) (w2 : List P2OriginalW2CandidateIntegerABI.Action) :
    sourceRound old w1 w2 = oneRound old (w1.map SourceW1.toABI) w2 := by
  simp only [sourceRound, oneRound, sourceW2Bank_eq, sourceW1Bank_eq, sourceBuchstab_eq]

def sourceIterate : Nat → Table
  | 0 => originalSeed
  | n+1 => sourceRound (sourceIterate n) (sourceW1Schedule n) (sourceW2Schedule n)

theorem sourceIterate_eq (n : Nat) :
    sourceIterate n = iterate designatedW1 designatedW2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sourceIterate, iterate, sourceRound_eq_oneRound, ih,
        designatedW1, designatedW2]

def snapshot (v : Value) : Table := fun upper i =>
  (((items (field v (if upper then "H_cell_lower_numerators" else "h_cell_lower_numerators"))).map
    integer)[i.val]?).getD 0

def SnapshotEq (n : Nat) (v : Value) : Prop :=
  ∀ upper : Bool, ∀ i : Fin 200, sourceIterate n upper i = snapshot v upper i

instance (n : Nat) (v : Value) : Decidable (SnapshotEq n v) := by
  unfold SnapshotEq; infer_instance

/-- Each full400-entry checkpoint is recomputed from the original seed
and the literal designated schedule. No checkpoint is an assumed seed. -/
theorem stage24_guard : SnapshotEq 24 json24 := by decide
theorem stage56_guard : SnapshotEq 56 json56 := by decide
theorem stage120_guard : SnapshotEq 120 json120 := by decide
theorem stage184_guard : SnapshotEq 184 json184 := by decide
theorem stage248_guard : SnapshotEq 248 json248 := by decide

/-- Exact schedule boundaries, indexed by the PRECEDING round count. -/
theorem historical_boundaries_guard :
    [(sourceW2Schedule 23).length, (sourceW2Schedule 24).length,
      (sourceW2Schedule 55).length, (sourceW2Schedule 56).length,
      (sourceW2Schedule 119).length, (sourceW2Schedule 120).length,
      (sourceW2Schedule 183).length, (sourceW2Schedule 184).length,
      (sourceW2Schedule 247).length] = [0,3,3,3,3,3,3,36,36] ∧
    w1Original.length = 70 ∧ w1Retained.length = 70 ∧ w2Added.length = 33 := by decide

/-- The ORIGINAL copied lower-bank integers and the separate adopted
Fin200 vector are both bound entry by entry to the actual original file. -/
theorem copied_bank_guard (i : Fin 200) :
    bankLowerTable (i.val : ℤ) = snapshot json248 false i := by
  exact (by decide : ∀ j : Fin 200, bankLowerTable (j.val : ℤ) = snapshot json248 false j) i

theorem adopted_vector_guard (i : Fin 200) :
    Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators i = snapshot json248 false i := by
  exact (by decide : ∀ j : Fin 200,
    Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators j = snapshot json248 false j) i

/-- No schedule, copied-array equality or guard-truth premise. This is a
source theorem candidate, with all finite guards UNEVALUATED. -/
theorem designated_h248_eq_history (i : Fin 200) :
    bankLowerTable (i.val : ℤ) = iterate designatedW1 designatedW2 248 false i := by
  rw [copied_bank_guard]
  exact (stage248_guard false i).symm.trans
    (congrFun (congrFun (sourceIterate_eq 248) false) i)

/-- J's suffix ancestry now consumes the actual historical source schedule
and the original copied bank; neither is a caller hypothesis. -/
theorem designated_h248_eq_last_H247_suffix (i : Fin 200) :
    bankLowerTable (i.val : ℤ) = if 50 ≤ i.val then
      suffixNumerator historicalLogWeights (iterate designatedW1 designatedW2 247)
        true (i.val-49) else 0 := by
  rw [designated_h248_eq_history]
  exact iterate_lower_last_suffix designatedW1 designatedW2 247 i

/-- The only analytic hypothesis here remains H247. It is internal,
UNPROVED, and is not weakened to an assumed h248 endpoint assertion. -/
theorem designated_h248_endpoints_from_H247 {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (hupper : UpperEndpoints δ (iterate designatedW1 designatedW2 247)) (i : Fin 200) :
    (bankLowerTable (i.val : ℤ) : ℝ)/tableQ ≤
      P2TableActionSourceOnly.h δ (bankCellRight (i.val : ℤ) : ℝ) := by
  rw [designated_h248_eq_history]
  exact historical_248_lower_from_H247 hδ hδhi designatedW1 designatedW2 hupper i

/-- Conditional installation API for the unchanged original saved-floor
consumer. The sole H247 invariant is deliberately still visible. -/
theorem bankEndpointLicences_from_H247 {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (hupper : UpperEndpoints δ (iterate designatedW1 designatedW2 247)) :
    BankEndpointLicences δ := by
  intro k hk0 hk199 _
  let i : Fin 200 := ⟨k.toNat, by omega⟩
  have hi : (i.val : ℤ) = k := by dsimp [i]; omega
  have h := designated_h248_endpoints_from_H247 hδ hδhi hupper i
  rw [hi] at h
  simpa [P2HistoricOrdinaryParentClosed.decodeQ80, tableQ, Q] using h

/-- J's existing closed crossing minimum is consumed unchanged. In
particular both cells at a knot remain selected and guard refusal remains
literal zero; there is no pointwise interpolation or a new bank premise. -/
theorem original_closed_lookup_from_H247 {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (hupper : UpperEndpoints δ (iterate designatedW1 designatedW2 247))
    (x : I80) (horder : x.lo ≤ x.hi)
    (hs2 : 2 ≤ s) (hs5 : s ≤ 5) (hs : s ≤ (x.decodeHi : ℝ)) :
    ((bankDefectLookup x).decodeLo : ℝ) ≤ P2TableActionSourceOnly.h δ s :=
  bankDefectLookup_endpoint_sound hδ hδhi
    (bankEndpointLicences_from_H247 hδ hδhi hupper) x horder hs2 hs5 hs

end
end ImbalancedChen.P2Historical248Authentication
