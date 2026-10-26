import ImbalancedChen.P1OriginalVariableFourthEligibilityPartition
import ImbalancedChen.OriginalFourthUniformIntegerMeshRealization

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

A constant ANALYTIC upper cap on each literal original eligibility atom
intersected with a sufficiently small refinement box. The actual policy
remains the full variable maximum. Every eligible row, losing row and tie
remains in the extension. The reference corner need not belong to the
atom; this is why the already defined fixed-row extension is used.

The cap lies between actualProfile+e/2 and actualProfile+e. Thus e/2 pays
the whole endpoint vector while one original e buffer remains below the
unbuffered winning tent. No endpoint argmax is selected after N, no global
wall continuity is asserted, and no support/analytic target is assumed.
-/

namespace ImbalancedChen.OriginalFourthFrozenAtomCap20261026b

noncomputable section
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthProfileRegularity
open P1OriginalVariableFourthCellTestLimit
open P1OriginalVariableFourthEligibilityPartition
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open OriginalFullFourthPriorityOwnership20261026a

/-- Every original row has at most four slots; its common buffer cancels
in the oscillation. The same six-delta modulus passes through the FULL
fixed eligible maximum, without choosing any particular maximizer. -/
theorem fixedCellExponent_oscillation (e seed : ℝ) (rows E : Finset ProducerRow)
    (t u : Point) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hcoord : ∀ i, |t i - u i| ≤ delta) :
    |fixedCellExponent e rows E seed t - fixedCellExponent e rows E seed u| ≤ 6 * delta := by
  unfold fixedCellExponent
  apply fixedMax_abs_sub_le seed _ (fun r => r.bufferedCandidate e) t u
    (6 * delta) (by positivity)
  intro r _hr
  have hrow := candidateExponent_abs_sub_le_of_coordinates (2 * e) r.selected
    t u delta (fun i _hi => hcoord i)
  have hcardNat : r.selected.card ≤ 4 := by
    simpa using (Finset.card_le_card (Finset.subset_univ r.selected))
  have hcard : (r.selected.card : ℝ) ≤ 4 := by exact_mod_cast hcardNat
  have hprod := mul_le_mul_of_nonneg_right hcard hdelta
  have hrow' : |r.bufferedCandidate e t - r.bufferedCandidate e u| ≤
      (3 / 2 : ℝ) * (r.selected.card : ℝ) * delta := by
    simpa only [candidateExponent, ProducerRow.bufferedCandidate_eq] using hrow
  nlinarith

/-- All parameters are finite source data fixed before N. The atom fixes
eligibility; it does NOT fix or presuppose the actual winning row. -/
def frozenAtomCap (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (s : Pattern rows) (corner : Point) (delta : ℝ) : ℝ :=
  fixedCellExponent e rows (eligibleRows rows licensed s) seed corner + 6 * delta + e / 2

theorem actual_profile_frozen_cap_bracket (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (s : Pattern rows) (corner t : Point)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ e / 24)
    (ht : t ∈ wallAtom rows s) (hcoord : ∀ i, |t i - corner i| ≤ delta) :
    producerProfile4 e rows licensed seed t + e / 2 ≤
        frozenAtomCap e seed rows licensed s corner delta ∧
      frozenAtomCap e seed rows licensed s corner delta ≤
        producerProfile4 e rows licensed seed t + e := by
  have hosc := fixedCellExponent_oscillation e seed rows (eligibleRows rows licensed s)
    t corner delta hdelta hcoord
  have hlo := (abs_le.mp hosc).1
  have hhi := (abs_le.mp hosc).2
  rw [producerProfile_eq_fixed_on_atom e seed rows licensed s ht]
  unfold frozenAtomCap
  constructor <;> nlinarith

/-- A real positional row owner identifies the original unbuffered tent
above this frozen analytic cap. The pointwise original max is untouched. -/
theorem actual_row_owned_frozen_cap (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (s : Pattern (fourthFamily records))
    (corner t : Point) (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ e / 24)
    (ht : t ∈ wallAtom (fourthFamily records) s)
    (hcoord : ∀ i, |t i - corner i| ≤ delta)
    (i : Fin records.length) (howner : owner records e seed licensed t = i.succ) :
    frozenAtomCap e seed (fourthFamily records) licensed s corner delta ≤
      (rowAt records i).candidate t - e := by
  have hcap := (actual_profile_frozen_cap_bracket e seed (fourthFamily records)
    licensed s corner t delta hdelta hsmall ht hcoord).2
  have hrow := (owned_row_is_actual_source records e seed licensed t i howner).2.2.2
  rw [hrow, ProducerRow.bufferedCandidate] at hcap
  linarith

theorem actual_seed_owned_frozen_cap (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (s : Pattern (fourthFamily records))
    (corner t : Point) (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ e / 24)
    (ht : t ∈ wallAtom (fourthFamily records) s)
    (hcoord : ∀ i, |t i - corner i| ≤ delta)
    (howner : owner records e seed licensed t = 0) :
    frozenAtomCap e seed (fourthFamily records) licensed s corner delta ≤ seed + e := by
  have hcap := (actual_profile_frozen_cap_bracket e seed (fourthFamily records)
    licensed s corner t delta hdelta hsmall ht hcoord).2
  rwa [(owner_zero_iff records e seed licensed t).mp howner] at hcap

end
end ImbalancedChen.OriginalFourthFrozenAtomCap20261026b
