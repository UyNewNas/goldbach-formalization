import ImbalancedChen.P2IndependentMercator320
import ImbalancedChen.P2HistoricalFullFloorProxyChain

/-!
SOURCE ONLY; uncompiled and UNEVALUATED.  The two `decide +kernel` bodies
below are closed rational proof proposals over the ORIGINAL dependent Row
mask.  They are not numerical results obtained in this author task.

The actual floor-proxy log queries all lie in [1,3/2], so the original
logq range-reduction loop makes zero shifts for these queries.  No extra
gross/fibre log query or atanh/project log evaluator is substituted.
-/

namespace ImbalancedChen.P2IndependentFullProxyFiniteCertificate

noncomputable section

open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2DirectedLogRounding
open P2SavedFloorSemantics P2HistoricalSavedFloorRowsBinder
open P2HistoricalSavedFloorFullBinder P2HistoricalOrdinaryProxyIntegral
open P2HistoricalOrdinaryProxySourceUpper P2HistoricalDefectClosedProxy
open P2HistoricalFullFloorProxyChain P2HistoricalSavedFloorSelectedUnion

namespace D
abbrev point := P2IndependentMercator320.point
abbrev mul := P2IndependentMercator320.mul
abbrev divide := P2IndependentMercator320.divide
abbrev mercator := P2IndependentMercator320.mercator
end D

def tQuery (r : Row) : ℚ := rowTR r / rowTL r
def uQuery (r : Row) : ℚ := rowUR r / rowUL r
def chordDenominator (r : Row) : ℚ :=
  Certificates.P2HistoricQ80DefectLookup.a * (sourceRH r - sourceRL r)

/-- Only primitive rational range/divisor guards, never a proxy inequality. -/
def RowGuards (r : Row) : Prop :=
  (1 ≤ tQuery r ∧ tQuery r ≤ 3 / 2) ∧
  (1 ≤ uQuery r ∧ uQuery r ≤ 3 / 2) ∧
  (2 ≤ rowSL r →
    (1 ≤ rowSL r - 1 ∧ rowSL r - 1 ≤ 3 / 2) ∧
    (1 ≤ rowSH r - 1 ∧ rowSH r - 1 ≤ 3 / 2) ∧
    (D.point (rowSL r)).reciprocalCheck = true ∧
    (D.point (rowSH r)).reciprocalCheck = true ∧
    (D.point Certificates.P2HistoricQ80DefectLookup.a).reciprocalCheck = true ∧
    (D.point (chordDenominator r)).reciprocalCheck = true ∧
    (D.point (sourceRH r)).reciprocalCheck = true)

instance (r : Row) : Decidable (RowGuards r) := by unfold RowGuards; infer_instance

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Compiler-owned finite rational guard reduction. NOT RUN here. -/
theorem all_original_row_guards : ∀ r : Row, RowGuards r := by
  decide +kernel

def maxInterval (a b : Enclosure) : Enclosure :=
  ⟨max a.lower b.lower, max a.upper b.upper⟩

theorem maxInterval_contains {a b : Enclosure} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) : (maxInterval a b).Contains (max x y) := by
  exact ⟨by simpa only [maxInterval, Rat.cast_max] using max_le_max ha.1 hb.1,
    by simpa only [maxInterval, Rat.cast_max] using max_le_max ha.2 hb.2⟩

/-- Exact source expression/order for loss proxy only. Each multiplication
and positive interval division rounds to 10^80; addition/negation are exact. -/
def rowProxyInterval (r : Row) : Enclosure :=
  if 2 ≤ rowSL r then
    let lt := D.mercator (tQuery r)
    let lu := D.mercator (uQuery r)
    let mass := D.mul lt lu
    let fl := D.divide (D.mercator (rowSL r - 1)) (D.point (rowSL r))
    let fh := D.divide (D.mercator (rowSH r - 1)) (D.point (rowSH r))
    let constant := D.divide (D.mul fl mass) (D.point Certificates.P2HistoricQ80DefectLookup.a)
    let moment := ((D.mul (D.point (57 / 64)) mass).sub
      (D.mul (D.mul (D.point (5 / 2)) (D.point (rowTR r - rowTL r))) lu)).sub
        (D.mul (D.point (rowUR r - rowUL r)) lt)
    let left := (D.mul (D.point (sourceRH r)) mass).sub moment
    let right := moment.sub (D.mul (D.point (sourceRL r)) mass)
    let chord := D.divide ((D.mul fl left).add (D.mul fh right)) (D.point (chordDenominator r))
    let hq : ℚ := (rowHNumerator r : ℚ) / Certificates.P2HistoricQ80DefectLookup.Q
    let defect := D.divide (D.mul (D.point hq) mass) (D.point (sourceRH r))
    (maxInterval constant chord).add defect
  else D.point 0

theorem positive_row_iff (r : Row) :
    (2 : ℚ) ≤ rowSL r ↔ 2 * ordinaryA ≤ rowResidualLo r := by
  have hq : (rowSL r : ℝ) = rowResidualLo r / ordinaryA := (source_query_casts r).1
  constructor
  · intro h
    have hR : (2 : ℝ) ≤ (rowSL r : ℝ) := by exact_mod_cast h
    rw [hq] at hR
    exact (le_div_iff₀ ordinaryA_pos).mp hR
  · intro h
    have hR : (2 : ℝ) ≤ (rowSL r : ℝ) := by
      rw [hq]
      exact (le_div_iff₀ ordinaryA_pos).mpr h
    exact_mod_cast hR

/-- All semantic guards are discharged by the closed finite guard theorem.
No backend-contract or expression-bound hypothesis is passed by a caller. -/
theorem rowProxyInterval_contains (r : Row) :
    (rowProxyInterval r).Contains (rowFullProxy r) := by
  have hg := all_original_row_guards r
  rcases hg with ⟨hgt, hgu, hgpos⟩
  by_cases hpos : (2 : ℚ) ≤ rowSL r
  · have hposR := (positive_row_iff r).mp hpos
    rcases hgpos hpos with ⟨hgl, hgh, hdsl, hdsh, hda, hdch, hdrh⟩
    have hlt := P2IndependentMercator320.mercator_contains hgt.1 hgt.2
    have hlu := P2IndependentMercator320.mercator_contains hgu.1 hgu.2
    have hm := P2IndependentMercator320.mul_contains hlt hlu
    have hm' : (D.mul (D.mercator (tQuery r)) (D.mercator (uQuery r))).Contains (rowMass r) := by
      simpa only [tQuery, uQuery, rowMass, P2HistoricQ80OrdinaryEstimatorSoundness.realMass,
        Rat.cast_div] using hm
    have hfl := P2IndependentMercator320.divide_contains
      (P2IndependentMercator320.mercator_contains hgl.1 hgl.2)
      (P2IndependentMercator320.point_contains (rowSL r)) hdsl
    have hfh := P2IndependentMercator320.divide_contains
      (P2IndependentMercator320.mercator_contains hgh.1 hgh.2)
      (P2IndependentMercator320.point_contains (rowSH r)) hdsh
    have hfl' : (D.divide (D.mercator (rowSL r - 1)) (D.point (rowSL r))).Contains (rowFL r) := by
      simpa only [rowFL, logFactor, Rat.cast_sub, Rat.cast_one, rowSL, (source_query_casts r).1] using hfl
    have hfh' : (D.divide (D.mercator (rowSH r - 1)) (D.point (rowSH r))).Contains (rowFH r) := by
      simpa only [rowFH, logFactor, Rat.cast_sub, Rat.cast_one, rowSH, (source_query_casts r).2] using hfh
    have hconst := P2IndependentMercator320.divide_contains
      (P2IndependentMercator320.mul_contains hfl' hm')
      (P2IndependentMercator320.point_contains Certificates.P2HistoricQ80DefectLookup.a) hda
    have hconst' : (D.divide
        (D.mul (D.divide (D.mercator (rowSL r - 1)) (D.point (rowSL r)))
          (D.mul (D.mercator (tQuery r)) (D.mercator (uQuery r))))
        (D.point Certificates.P2HistoricQ80DefectLookup.a)).Contains (rowConstantProxy r) := by
      simpa only [rowConstantProxy, P2HistoricQ80OrdinaryEstimatorSoundness.cast_source_a] using hconst
    let lt := D.mercator (tQuery r)
    let lu := D.mercator (uQuery r)
    let mass := D.mul lt lu
    let moment := ((D.mul (D.point (57 / 64)) mass).sub
      (D.mul (D.mul (D.point (5 / 2)) (D.point (rowTR r - rowTL r))) lu)).sub
        (D.mul (D.point (rowUR r - rowUL r)) lt)
    have hmom : moment.Contains (rowResidualMoment r) := by
      have hv := Enclosure.sub_contains
        (Enclosure.sub_contains (P2IndependentMercator320.mul_contains
          (P2IndependentMercator320.point_contains (57 / 64)) hm')
          (P2IndependentMercator320.mul_contains
            (P2IndependentMercator320.mul_contains (P2IndependentMercator320.point_contains (5 / 2))
              (P2IndependentMercator320.point_contains (rowTR r - rowTL r))) hlu))
        (P2IndependentMercator320.mul_contains
          (P2IndependentMercator320.point_contains (rowUR r - rowUL r)) hlt)
      convert hv using 1 <;> simp only [moment, mass, lt, lu, rowResidualMoment,
        tQuery, uQuery, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] <;> norm_num <;> ring
    have hlft := Enclosure.sub_contains
      (P2IndependentMercator320.mul_contains (P2IndependentMercator320.point_contains (sourceRH r)) hm') hmom
    have hrgt := Enclosure.sub_contains hmom
      (P2IndependentMercator320.mul_contains (P2IndependentMercator320.point_contains (sourceRL r)) hm')
    rw [(source_residual_casts r).2] at hlft
    rw [(source_residual_casts r).1] at hrgt
    have hch := P2IndependentMercator320.divide_contains
      (Enclosure.add_contains (P2IndependentMercator320.mul_contains hfl' hlft)
        (P2IndependentMercator320.mul_contains hfh' hrgt))
      (P2IndependentMercator320.point_contains (chordDenominator r)) hdch
    have hdenR : (chordDenominator r : ℝ) = ordinaryA * (rowResidualHi r - rowResidualLo r) := by
      simp only [chordDenominator, Rat.cast_mul, Rat.cast_sub,
        P2HistoricQ80OrdinaryEstimatorSoundness.cast_source_a,
        (source_residual_casts r).1, (source_residual_casts r).2]
    rw [hdenR] at hch
    have hch' := hch
    change Enclosure.Contains _ (rowChordProxy r) at hch'
    have hdef := P2IndependentMercator320.divide_contains
      (P2IndependentMercator320.mul_contains
        (P2IndependentMercator320.point_contains
          ((rowHNumerator r : ℚ) / Certificates.P2HistoricQ80DefectLookup.Q)) hm')
      (P2IndependentMercator320.point_contains (sourceRH r)) hdrh
    have hhq : (((rowHNumerator r : ℚ) / Certificates.P2HistoricQ80DefectLookup.Q : ℚ) : ℝ) = rowHB r := rfl
    rw [hhq, (source_residual_casts r).2] at hdef
    have hv := Enclosure.add_contains (maxInterval_contains hconst' hch') hdef
    simpa only [rowProxyInterval, if_pos hpos, rowFullProxy, rowOrdinaryProxy,
      rowDefectProxy, if_pos hposR, rowChordProxy, moment, mass, lt, lu] using hv
  · have hneg : ¬ 2 * ordinaryA ≤ rowResidualLo r := fun h => hpos ((positive_row_iff r).mpr h)
    simpa only [rowProxyInterval, if_neg hpos, rowFullProxy, rowOrdinaryProxy,
      rowDefectProxy, if_neg hneg, zero_add, Rat.cast_zero] using P2IndependentMercator320.point_contains 0

def selectedProxyUpper : ℚ := ∑ r : Row, (rowProxyInterval r).upper
def lambda : ℚ := 466977 / 200000000

theorem selectedFullProxy_le_directed_upper : selectedFullProxy ≤ (selectedProxyUpper : ℝ) := by
  unfold selectedFullProxy selectedProxyUpper
  push_cast
  exact Finset.sum_le_sum (fun r _hr => (rowProxyInterval_contains r).2)

/-- Closed original-mask rational comparison, for compiler-owned reduction.
NOT RUN or accepted in this source-only batch. No stored sum token occurs. -/
theorem original_selected_upper_lt_lambda : selectedProxyUpper < lambda := by
  decide +kernel

theorem selectedFullProxy_lt_lambda : selectedFullProxy < (lambda : ℝ) := by
  have hq : (selectedProxyUpper : ℝ) < (lambda : ℝ) := by
    exact_mod_cast original_selected_upper_lt_lambda
  exact selectedFullProxy_le_directed_upper.trans_lt hq

theorem checked_full_saved_sum_lt_lambda
    (hc : ∀ r : Row, fullSourceRowCheck r = true) :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80 / 4) < (lambda : ℝ) := by
  exact (Finset.sum_le_sum (fun r _hr => checked_frozen_full_saved_le_proxy r (hc r))).trans_lt
    selectedFullProxy_lt_lambda

end

end ImbalancedChen.P2IndependentFullProxyFiniteCertificate
