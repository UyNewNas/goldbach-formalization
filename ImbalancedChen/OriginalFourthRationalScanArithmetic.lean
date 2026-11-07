import ImbalancedChen.OriginalFourthBankStreamingScan
import ImbalancedChen.VariableEnvelopeRegularity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact rational specialization of the original raw fourth-row scan. The
wire decoder's original processing-slot masks and 204800 lattice are kept.
The rational box checks and candidate use only rational/finite arithmetic.
Licence flags are explicit INPUTS; neither their truth nor original row
licensing is inferred from a mask, a saved statistic, or a scan result.

The common -2e loss cancels from every strict comparison, so the rational
scan has exactly the same updates as the original real scan. Definitions
before the noncomputable section use no Classical decision procedure.
Nothing is executed and no archived pass or chronological22 map is claimed.
-/

namespace ImbalancedChen.OriginalFourthRationalScanArithmetic20261026b

open scoped BigOperators
open VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFourthContinuation
open OriginalFourthBankStreamingScan20261026b

abbrev RationalPoint := Fin 4 → ℚ

def rationalBox (raw : FourthWireRow) (t : RationalPoint) : Prop :=
  ∀ i, (raw.lo i : ℚ) / 204800 ≤ t i ∧ t i ≤ (raw.hi i : ℚ) / 204800

def rationalBoxCheck (raw : FourthWireRow) (t : RationalPoint) : Bool :=
  @decide (rationalBox raw t) (by unfold rationalBox; infer_instance)

def rationalCandidate (raw : FourthWireRow) (t : RationalPoint) : ℚ :=
  qV (∑ i ∈ maskSlots 4 raw.mask, t i)

def rationalEligible (flag : ProducerRow → Bool) (raw : FourthWireRow)
    (t : RationalPoint) : Bool := flag raw.toProducerRow && rationalBoxCheck raw t

@[ext] structure RationalScanState where
  seen : ℕ
  value : ℚ
  first : ℕ

def rationalStep (flag : ProducerRow → Bool) (t : RationalPoint)
    (state : RationalScanState) (raw : FourthWireRow) : RationalScanState :=
  if rationalEligible flag raw t = true ∧ state.value < rationalCandidate raw t then
    ⟨state.seen + 1, rationalCandidate raw t, state.seen + 1⟩
  else ⟨state.seen + 1, state.value, state.first⟩

def rationalScan (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (t : RationalPoint) : RationalScanState :=
  records.foldl (rationalStep flag t) ⟨0, seed, 0⟩

noncomputable section
open scoped Classical

def castPoint (t : RationalPoint) : Point := fun i => (t i : ℝ)

def castScanState (e : ℝ) (state : RationalScanState) : ScanState :=
  ⟨state.seen, (state.value : ℝ) - 2 * e, state.first⟩

theorem rationalScan_append_one (front : List FourthWireRow) (raw : FourthWireRow)
    (seed : ℚ) (flag : ProducerRow → Bool) (t : RationalPoint) :
    rationalScan (front ++ [raw]) seed flag t =
      rationalStep flag t (rationalScan front seed flag t) raw := by
  simp only [rationalScan, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Reuses the literal decoder's real closed-box theorem. All four
endpoint inequalities are retained, including equality on box faces. -/
theorem rationalBox_iff_original_box (raw : FourthWireRow) (t : RationalPoint) :
    rationalBox raw t ↔ castPoint t ∈ raw.toProducerRow.box := by
  rw [fourth_box]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · change (raw.lo i : ℝ) / 204800 ≤ (t i : ℝ)
      exact_mod_cast (h i).1
    · change (t i : ℝ) ≤ (raw.hi i : ℝ) / 204800
      exact_mod_cast (h i).2
  · rintro ⟨hl, hu⟩
    intro i
    constructor
    · have h := hl i
      change (raw.lo i : ℝ) / 204800 ≤ (t i : ℝ) at h
      exact_mod_cast h
    · have h := hu i
      change (t i : ℝ) ≤ (raw.hi i : ℝ) / 204800 at h
      exact_mod_cast h

/-- The existing rational tent cast lemma is reused; no new density
function or alternative cap replaces the original selected-mask tent. -/
theorem rationalCandidate_cast (raw : FourthWireRow) (t : RationalPoint) :
    (rationalCandidate raw t : ℝ) = raw.toProducerRow.candidate (castPoint t) := by
  rw [ProducerRow.candidate_eq, fourth_selected]
  simp only [rationalCandidate, cast_qV, Rat.cast_sum, castPoint]

theorem rationalCandidate_buffered (raw : FourthWireRow) (t : RationalPoint) (e : ℝ) :
    (rationalCandidate raw t : ℝ) - 2 * e =
      raw.toProducerRow.bufferedCandidate e (castPoint t) := by
  rw [ProducerRow.bufferedCandidate, rationalCandidate_cast]

/-- This is an explicit flag-to-original-licence equivalence input. It is
not manufactured by the rational checker or by a positive saved gain. -/
theorem rationalEligible_iff_original (flag : ProducerRow → Bool)
    (licensed : ProducerRow → Prop) (hflag : ∀ r, flag r = true ↔ licensed r)
    (raw : FourthWireRow) (t : RationalPoint) :
    rationalEligible flag raw t = true ↔ producerEligible licensed raw.toProducerRow (castPoint t) := by
  simp only [rationalEligible, Bool.and_eq_true, rationalBoxCheck, decide_eq_true_eq]
  rw [hflag, rationalBox_iff_original_box]
  rfl

/-- The exact common loss cancels even for negative e or negative current
values. Strict comparison preserves the original first-occurrence ties. -/
theorem buffered_strict_comparison (raw : FourthWireRow) (t : RationalPoint)
    (e : ℝ) (current : ℚ) :
    (current : ℝ) - 2 * e < raw.toProducerRow.bufferedCandidate e (castPoint t) ↔
      current < rationalCandidate raw t := by
  rw [← rationalCandidate_buffered, sub_lt_sub_iff_right]
  exact Rat.cast_lt

theorem rationalStep_cast (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflag : ∀ r, flag r = true ↔ licensed r) (t : RationalPoint) (e : ℝ)
    (state : RationalScanState) (raw : FourthWireRow) :
    castScanState e (rationalStep flag t state raw) =
      scanStep e licensed (castPoint t) (castScanState e state) raw := by
  have hc : (rationalEligible flag raw t = true ∧ state.value < rationalCandidate raw t) ↔
      (producerEligible licensed raw.toProducerRow (castPoint t) ∧
        (state.value : ℝ) - 2 * e < raw.toProducerRow.bufferedCandidate e (castPoint t)) := by
    rw [rationalEligible_iff_original flag licensed hflag, buffered_strict_comparison]
  by_cases hq : rationalEligible flag raw t = true ∧ state.value < rationalCandidate raw t
  · have hr := hc.mp hq
    simp only [rationalStep, if_pos hq, castScanState, scanStep, if_pos hr]
    rw [rationalCandidate_buffered]
  · have hr : ¬ (producerEligible licensed raw.toProducerRow (castPoint t) ∧
        (state.value : ℝ) - 2 * e < raw.toProducerRow.bufferedCandidate e (castPoint t)) :=
      fun h => hq (hc.mpr h)
    simp only [rationalStep, if_neg hq, castScanState, scanStep, if_neg hr]

/-- The computable rational fold and the original real fold have the same
state at EVERY finite raw-bank prefix. No archive is run to prove this. -/
theorem rationalScan_cast (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflag : ∀ r, flag r = true ↔ licensed r) (t : RationalPoint) (e : ℝ) :
    castScanState e (rationalScan records seed flag t) =
      scan records e ((seed : ℝ) - 2 * e) licensed (castPoint t) := by
  induction records using List.reverseRecOn with
  | nil => rfl
  | append_singleton front raw ih =>
      rw [rationalScan_append_one, scan_append_one, ← ih]
      exact rationalStep_cast flag licensed hflag t e (rationalScan front seed flag t) raw

end
end ImbalancedChen.OriginalFourthRationalScanArithmetic20261026b
