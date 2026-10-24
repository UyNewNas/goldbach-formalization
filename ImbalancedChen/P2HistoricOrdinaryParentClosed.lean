import ImbalancedChen.P2HistoricBackendTypeAdapters
import ImbalancedChen.P2HistoricLogCallerGuards

/-!
# Literal historical ordinary parent estimator, with all backends closed

The functions here are the source sf(16384,8), source log_point wrapper,
and source savedOrdinaryRectangle, on the actual imported paired512 knots.
The actual historical table induction, positive rounded log arguments,
Q80 chord divisors and real ordinary chord semantics are composed through
their proved APIs. No backend-query enclosure, state/node validity, log
contract, chord divisor, or target floor inequality is a hypothesis.

The adopted-row theorem uses the actual 17572-row FullMask index map.
The sum theorem decodes the sum of literal raw ordinary integers and
bounds it by the corresponding sum of genuine ordinary integrals.

This is the ordinary part of pair_cell. The separately nonnegative defect
part needs its actual-h licence, and equality with the published saved row
integers requires the separate literal-evaluation/source-binding theorem.
No published saved total or final loss bound is asserted here.

SOURCE_WRITTEN_UNCOMPILED. No historical producer or evaluator was run.
-/

namespace ImbalancedChen.P2HistoricOrdinaryParentClosed

noncomputable section

open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricBackendTypeAdapters
open Certificates.P2HistoricLogCallerGuards
open Certificates.PairedV2
open scoped BigOperators

/-- The exact literal source estimator, with its sf and log implementations
fixed here rather than supplied as semantic parameters. -/
def rawOrdinaryParent (i j : ℕ) : ℤ :=
  savedOrdinaryRectangle sourceSf sourceLogI (tLower i) (tUpper i) (uLower j) (uUpper j)

def decodeQ80 (n : ℤ) : ℝ := (((n : ℚ) / Q : ℚ) : ℝ)

/-- Genuine kernel integral on the same original parent rectangle. -/
def ordinaryParentIntegral (i j : ℕ) : ℝ :=
  P2SavedFloorSemantics.ordinaryCellIntegral
    (tLower i : ℝ) (tUpper i : ℝ) (uLower j : ℝ) (uUpper j : ℝ)

/-- Every actual parent of the complete 512-by-512 grid. The only inputs
are the original finite grid indices; all analytic backend obligations
have been proved in the imported source modules. -/
theorem parent_ordinary_lower (i j : Fin 512) :
    decodeQ80 (rawOrdinaryParent i.val j.val) ≤ ordinaryParentIntegral i.val j.val := by
  exact parent_savedOrdinaryRectangle_actual_lower_logClosed sourceSf i j
    sourceSf_contains_actual

theorem all_512_parents_ordinary_lower : ∀ i j : Fin 512,
    decodeQ80 (rawOrdinaryParent i.val j.val) ≤ ordinaryParentIntegral i.val j.val := by
  intro i j
  exact parent_ordinary_lower i j

theorem rawOrdinaryParent_nonneg (i j : ℕ) : 0 ≤ rawOrdinaryParent i j := by
  exact savedOrdinaryRectangle_nonneg sourceSf sourceLogI _ _ _ _

theorem decodeQ80_nonneg {n : ℤ} (hn : 0 ≤ n) : 0 ≤ decodeQ80 n := by
  have hnQ : (0 : ℚ) ≤ n := by exact_mod_cast hn
  have hQ := div_nonneg hnQ Q_pos.le
  unfold decodeQ80
  exact_mod_cast hQ

theorem parent_decoded_nonneg (i j : ℕ) : 0 ≤ decodeQ80 (rawOrdinaryParent i j) :=
  decodeQ80_nonneg (rawOrdinaryParent_nonneg i j)

theorem complete_grid_ordinary_lower :
    (∑ i : Fin 512, ∑ j : Fin 512, decodeQ80 (rawOrdinaryParent i.val j.val)) ≤
      ∑ i : Fin 512, ∑ j : Fin 512, ordinaryParentIntegral i.val j.val := by
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_le_sum (fun j _ => parent_ordinary_lower i j)

/-- No new row carrier: this is exactly the established adopted mask. -/
abbrev AdoptedRow := FullMask.Row

def rawAdoptedOrdinary (r : AdoptedRow) : ℤ :=
  rawOrdinaryParent (FullMask.indices r).1 (FullMask.indices r).2

def adoptedOrdinaryIntegral (r : AdoptedRow) : ℝ :=
  ordinaryParentIntegral (FullMask.indices r).1 (FullMask.indices r).2

theorem adopted_row_count : Fintype.card AdoptedRow = 17572 := FullMask.row_count

/-- Every one of the actual 17572 adopted rows, with no query/state/log/
divisor/floor licence among its arguments. -/
theorem adopted_ordinary_lower (r : AdoptedRow) :
    decodeQ80 (rawAdoptedOrdinary r) ≤ adoptedOrdinaryIntegral r := by
  exact adopted_savedOrdinaryRectangle_actual_lower_logClosed sourceSf r
    sourceSf_contains_actual

theorem all_17572_adopted_ordinary_lower : ∀ r : AdoptedRow,
    decodeQ80 (rawAdoptedOrdinary r) ≤ adoptedOrdinaryIntegral r := by
  intro r
  exact adopted_ordinary_lower r

theorem rawAdoptedOrdinary_nonneg (r : AdoptedRow) : 0 ≤ rawAdoptedOrdinary r :=
  rawOrdinaryParent_nonneg _ _

/-- Exact linear decoding of a finite integer sum; there is no extra
rounding operation and no assumed numerical output on the right. -/
theorem decodeQ80_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    decodeQ80 (∑ i ∈ s, f i) = ∑ i ∈ s, decodeQ80 (f i) := by
  simp [decodeQ80, Finset.sum_div]

def rawAdoptedOrdinaryTotal : ℤ := ∑ r : AdoptedRow, rawAdoptedOrdinary r

def adoptedOrdinaryIntegralTotal : ℝ := ∑ r : AdoptedRow, adoptedOrdinaryIntegral r

theorem rawAdoptedOrdinaryTotal_nonneg : 0 ≤ rawAdoptedOrdinaryTotal := by
  exact Finset.sum_nonneg (fun r _ => rawAdoptedOrdinary_nonneg r)

/-- Decoding the literal full adopted ordinary raw total is bounded by
the full true ordinary integral sum. This is not the separate paired
gross-deletion integral and is not a numerical saved-loss theorem. -/
theorem adopted_ordinary_total_lower :
    decodeQ80 rawAdoptedOrdinaryTotal ≤ adoptedOrdinaryIntegralTotal := by
  rw [rawAdoptedOrdinaryTotal, decodeQ80_sum]
  exact Finset.sum_le_sum (fun r _ => adopted_ordinary_lower r)

/-- The same conclusion for any selected finite portion of the original
mask, without inventing a new per-row floor certificate. -/
theorem adopted_ordinary_partial_lower (s : Finset AdoptedRow) :
    decodeQ80 (∑ r ∈ s, rawAdoptedOrdinary r) ≤ ∑ r ∈ s, adoptedOrdinaryIntegral r := by
  rw [decodeQ80_sum]
  exact Finset.sum_le_sum (fun r _ => adopted_ordinary_lower r)

end

end ImbalancedChen.P2HistoricOrdinaryParentClosed
