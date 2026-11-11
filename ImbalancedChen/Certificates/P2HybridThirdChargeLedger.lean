import ImbalancedChen.Certificates.P2OriginalThirdTreeCertificate
import ImbalancedChen.Certificates.P2HistoricalThirdMeanDispatch
import ImbalancedChen.Certificates.P2ThirdZeroGeometry

/-!
P2 SOURCE ONLY / UNCOMPILED.
A hybrid SEMANTIC ledger joins the existing BoxGuard rule and the complete
ordinary P160 integral rule to the exact original positional Q80 tree ledger.
A separate finite zero-geometry checker pays exact zero-charge occurrences.
No executable whole-ledger Bool is supplied: ordinaryUpper still depends on
the noncomputable value-semantic reader/log/floor backend. Every actual
coordinate binding, geometry check, directed integer comparison and adopted
sum still needs proof. No original data or acceptance is manufactured.
-/
namespace ImbalancedChen.Certificates.P2HybridThirdChargeLedger
noncomputable section

open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P2ThirdCompactCertifiedBoxIntegral
open OriginalThirdClosedLeafStoredChargeP4ASourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly

abbrev Bounds := P2OriginalThirdTreeCertificate.Bounds
abbrev integerLeaves := P2OriginalThirdTreeCertificate.integerLeaves
abbrev literalLeaf := P2OriginalThirdTreeCertificate.literalLeaf

/-- The two consumers use the SAME original DEN and real coordinate map.
Only an existing coordinate binding is instantiated, not a new cover. -/
theorem decode_eq_ordinary_point (v : Fin 3 → ℤ) :
    decodeCoordinates v=realBox (P2OrdinaryIntegerGuard.rationalPoint v) := by
  have hb := realBox_grid_binding v (P2OrdinaryIntegerGuard.rationalPoint v)
    (fun _ => rfl)
  funext i
  calc
    decodeCoordinates v i=(v i:ℝ)/((48000*2^24:ℤ):ℝ) := by
      norm_num [decodeCoordinates,coordinateDenominator]
    _=realBox (P2OrdinaryIntegerGuard.rationalPoint v) i := (hb i).symm

theorem literalLeaf_eq_ordinary_leaf (bounds : Bounds) :
    literalLeaf bounds=P2OrdinaryIntegerGuard.leaf bounds.1 bounds.2 := by
  change compactRegion ∩ Icc (decodeCoordinates bounds.1) (decodeCoordinates bounds.2)=
    compactRegion ∩ Icc (realBox (P2OrdinaryIntegerGuard.rationalPoint bounds.1))
      (realBox (P2OrdinaryIntegerGuard.rationalPoint bounds.2))
  rw [decode_eq_ordinary_point,decode_eq_ordinary_point]

/-- Exact 80-to-160 unit dictionary, with no additional rounding operation.
Both source upper bounds already include the kernel's factor four. -/
theorem value_Q80_charge (q : ℤ) :
    value (q*(2:ℤ)^80)=(q:ℝ)/(2:ℝ)^80 := by
  unfold value P160
  push_cast
  norm_num <;> ring

inductive Source where
  | box (guard : BoxGuard)
  | ordinary (lo hi : Fin 3 → ℤ)
  | zero

structure Entry where
  source : Source
  charge : ℤ

/-- Ordinary coordinates are bound to THIS tree occurrence before its cost
is compared. Integer domination is a semantic obligation, not an asserted
executable evaluation of ordinaryUpper or a bitwise Q80/P160 identity. -/
def Entry.Valid (e : Entry) (table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable)
    (bounds : Bounds) : Prop :=
  match e.source with
  | .box guard =>
      (P2OriginalThirdTreeCertificate.Entry.mk guard e.charge).Valid bounds
  | .ordinary lo hi =>
      lo=bounds.1 ∧ hi=bounds.2 ∧
      P2OrdinaryIntegerGuard.check lo hi=true ∧
      P2HistoricalThirdMeanDispatch.ordinaryUpper table lo hi≤e.charge*(2:ℤ)^80
  | .zero => P2ThirdZeroGeometry.check bounds.1 bounds.2=true ∧ e.charge=0

def Entry.upper (e : Entry)
    (table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable) : ℝ :=
  match e.source with
  | .box guard => (guard.integralUpper:ℝ)
  | .ordinary lo hi => value (P2HistoricalThirdMeanDispatch.ordinaryUpper table lo hi)
  | .zero => 0

/-- No caller-supplied integral bound, integrability or real containment is
stored in an Entry. Existing actual analytic suppliers pay both cases. -/
theorem Entry.local_integral_bounds
    {table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable}
    {e : Entry} {bounds : Bounds} (h : e.Valid table bounds) :
    (∫ t in literalLeaf bounds,compactKernel t)≤e.upper table ∧
      e.upper table≤(e.charge:ℝ)/(2:ℝ)^80 := by
  cases hs : e.source with
  | box guard =>
      have hv : (P2OriginalThirdTreeCertificate.Entry.mk guard e.charge).Valid bounds := by
        simpa only [Entry.Valid,hs] using h
      have hb := P2OriginalThirdTreeCertificate.Entry.local_integral_bounds hv
      simpa only [Entry.upper,hs] using hb
  | ordinary lo hi =>
      have hv : lo=bounds.1 ∧ hi=bounds.2 ∧
          P2OrdinaryIntegerGuard.check lo hi=true ∧
          P2HistoricalThirdMeanDispatch.ordinaryUpper table lo hi≤e.charge*(2:ℤ)^80 := by
        simpa only [Entry.Valid,hs] using h
      obtain ⟨hl,hh,hg,hcost⟩ := hv
      have hleaf : literalLeaf bounds=P2OrdinaryIntegerGuard.leaf lo hi := by
        simpa only [←hl,←hh] using literalLeaf_eq_ordinary_leaf bounds
      constructor
      · rw [hleaf]
        simpa only [Entry.upper,hs] using
          P2HistoricalThirdMeanDispatch.checked_ordinary_integral_upper table lo hi hg
      · have hpaid := (value_mono hcost).trans_eq (value_Q80_charge e.charge)
        simpa only [Entry.upper,hs] using hpaid
  | zero =>
      have hv : P2ThirdZeroGeometry.check bounds.1 bounds.2=true ∧ e.charge=0 := by
        simpa only [Entry.Valid,hs] using h
      have hz : (∫ t in literalLeaf bounds,compactKernel t)=0 :=
        P2ThirdZeroGeometry.check_integral_eq_zero bounds.1 bounds.2 hv.1
      constructor
      · simpa only [Entry.upper,hs] using hz.le
      · norm_num [Entry.upper,hs,hv.2]

/-- Exact positional relation. It retains every original closed-leaf
occurrence, including duplicates, empty/zero-width leaves and shared faces.
It is deliberately a Prop, not a noncomputable Bool presented as a checker. -/
def entriesValid (table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable)
    (tree : ClosedCutTree) (entries : List Entry) : Prop :=
  List.Forall₂ (fun bounds e => e.Valid table bounds) (integerLeaves tree) entries

theorem entriesValid_count
    {table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable}
    {tree : ClosedCutTree} {entries : List Entry} (h : entriesValid table tree entries) :
    entries.length=(closedLeaves tree compactRegion).length := by
  rw [P2OriginalThirdTreeCertificate.originalLeaves_eq_integerLeaves,List.length_map]
  exact (List.Forall₂.length_eq h).symm

def realEntries (table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable)
    (entries : List Entry) : List (ℝ × ℤ) :=
  entries.map (fun e => (e.upper table,e.charge))

/-- The previous exact original integer-tree/real-leaf identity and map
transport supply the original aggregator's local estimates without a zip,
tree reconstruction, permutation, or new closed-face argument. -/
theorem actual_local_suppliers
    {table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable}
    {tree : ClosedCutTree} {entries : List Entry} (h : entriesValid table tree entries) :
    List.Forall₂ (fun leaf e =>
      (∫ t in leaf,compactKernel t)≤e.1 ∧ e.1≤(e.2:ℝ)/(2:ℝ)^80)
      (closedLeaves tree compactRegion) (realEntries table entries) := by
  rw [P2OriginalThirdTreeCertificate.originalLeaves_eq_integerLeaves,realEntries,
    List.forall₂_map_left_iff,List.forall₂_map_right_iff]
  exact (show List.Forall₂ (fun bounds e => e.Valid table bounds)
    (integerLeaves tree) entries from h).imp
    (fun bounds e he => Entry.local_integral_bounds he)

theorem compactIntegral_le_charge_sum
    {table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable}
    {tree : ClosedCutTree} {entries : List Entry} (h : entriesValid table tree entries) :
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection≤
      (((entries.map Entry.charge).sum:ℤ):ℝ)/(2:ℝ)^80 := by
  have hb := originalCompactThirdCorrection_le_sum_storedCharges tree
    (realEntries table entries) (actual_local_suppliers h)
  simpa only [realEntries,List.map_map,Function.comp_def] using hb

/-- The original exact Q80 integer allowance is reused, not replaced by a
recomputed total or independent numerical target. No truth is asserted. -/
def adoptedValid (table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable)
    (tree : ClosedCutTree) (entries : List Entry) : Prop :=
  entriesValid table tree entries ∧
    (entries.map Entry.charge).sum≤P2OriginalThirdTreeCertificate.adoptedCharge

theorem adoptedValid_sound
    {table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable}
    {tree : ClosedCutTree} {entries : List Entry} (h : adoptedValid table tree entries) :
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection≤
      144590669409566793572719/(2:ℝ)^80 := by
  apply originalCompactThirdCorrection_le_originalAllowance tree
    (realEntries table entries) (actual_local_suppliers h.1)
  simpa only [realEntries,List.map_map,Function.comp_def,
    P2OriginalThirdTreeCertificate.adoptedCharge] using h.2

/-- Existing complete-third tail transport; no new tail estimate, extra
normalization, or additional reserve is introduced by the mixed ledger. -/
theorem adoptedValid_full_integral
    {table : OriginalU2StoredNodeBlockCheckerSourceOnly.CheckedBlockTable}
    {tree : ClosedCutTree} {entries : List Entry} (h : adoptedValid table tree entries) :
    actualExtendedThirdIdealFunctional≤144590669409566793572719/(2:ℝ)^80+
      OriginalThirdTailActualIdealSourceOnly.Tnew := by
  have hb := OriginalThirdFiniteReserveSourceOnly.idealFunctional_le_compact_add_Tnew
  change actualExtendedThirdIdealFunctional≤
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection+
      OriginalThirdTailActualIdealSourceOnly.Tnew at hb
  exact hb.trans (add_le_add_right (adoptedValid_sound h) _)

end
end ImbalancedChen.Certificates.P2HybridThirdChargeLedger
