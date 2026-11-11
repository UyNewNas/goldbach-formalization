import ImbalancedChen.P2ThirdCompactUniformCover
import ImbalancedChen.P4AClosedTreeCoordinatePropagation
import ImbalancedChen.ClosedLeafStoredChargeAggregation

/-!
SOURCE ONLY; UNCOMPILED. Finite rational certificate consumer for an
arbitrary original adaptive ClosedCutTree. Reuses P4's exact original
integer-coordinate propagation, P2's genuine BoxGuard integral rule,
and the existing positional integer-charge aggregation.

No original tree or complete certificate list is manufactured here.
No original endpoint check is asserted true. Every stored occurrence,
including empty and zero-width leaves and both closed-face copies,
must have its own entry in the exact left-before-right traversal order.
-/

namespace ImbalancedChen.Certificates.P2OriginalThirdTreeCertificate

noncomputable section

open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P2ThirdCompactCertifiedBoxIntegral
open OriginalThirdClosedLeafStoredChargeP4ASourceOnly

abbrev Point := Fin 3 → ℝ
abbrev Bounds := (Fin 3 → ℤ) × (Fin 3 → ℤ)

/-- The exact existing root box, with the original DEN=48000*2^24.
Only the tree is variable: no substitute uniform tree is selected. -/
def integerLeaves (tree : ClosedCutTree) : List Bounds :=
  integerLeafBoxes tree P2ThirdCompactUniformCover.rootBox.lo
    P2ThirdCompactUniformCover.rootBox.hi

def literalLeaf (bounds : Bounds) : Set Point :=
  compactRegion ∩ Icc (decodeCoordinates bounds.1) (decodeCoordinates bounds.2)

theorem decode_eq_realPoint (v : Fin 3 → ℤ) :
    decodeCoordinates v = realPoint (P2ThirdCompactUniformCover.rationalPoint v) := by
  rw [P2ThirdCompactUniformCover.realPoint_rationalPoint]
  funext i
  simp only [decodeCoordinates, P2ThirdCompactUniformCover.normalizedPoint,
    P2ThirdCompactUniformCover.scale_eq_original]

theorem root_intersection_eq :
    compactRegion ∩ Icc
      (decodeCoordinates P2ThirdCompactUniformCover.rootBox.lo)
      (decodeCoordinates P2ThirdCompactUniformCover.rootBox.hi) = compactRegion := by
  apply inter_eq_left.mpr
  simpa only [decode_eq_realPoint, P2ThirdCompactUniformCover.realPoint_rationalPoint,
    P2ThirdCompactUniformCover.IntBox.box] using
      P2ThirdCompactUniformCover.compactRegion_subset_rootBox

/-- Exact list equality with the original source leaves. P4 already
pays min/max clipping, cuts outside boxes and all closed split faces. -/
theorem originalLeaves_eq_integerLeaves (tree : ClosedCutTree) :
    closedLeaves tree compactRegion = (integerLeaves tree).map literalLeaf := by
  calc
    _ = closedLeaves tree (compactRegion ∩ Icc
        (decodeCoordinates P2ThirdCompactUniformCover.rootBox.lo)
        (decodeCoordinates P2ThirdCompactUniformCover.rootBox.hi)) := by
      rw [root_intersection_eq]
    _ = _ := compact_closedLeaves_eq_integer_boxes tree
      P2ThirdCompactUniformCover.rootBox.lo P2ThirdCompactUniformCover.rootBox.hi

/-- A real-integral guard and its original outward Q80 integer charge.
Neither an analytic leaf estimate nor a saved numerical total is a field. -/
structure Entry where
  guard : BoxGuard
  charge : ℤ

/-- Entirely finite rational tests. The guard box may overhang the true
ordered leaf; its full positive-box volume is charged. -/
def Entry.Valid (e : Entry) (bounds : Bounds) : Prop :=
  e.guard.check = true ∧
    (∀ i, e.guard.lo i ≤ P2ThirdCompactUniformCover.rationalPoint bounds.1 i ∧
      P2ThirdCompactUniformCover.rationalPoint bounds.2 i ≤ e.guard.hi i) ∧
    e.guard.integralUpper ≤ (e.charge : ℚ) / 2^80

instance (e : Entry) (bounds : Bounds) : Decidable (e.Valid bounds) := by
  unfold Entry.Valid
  infer_instance

/-- Library Forall₂ has a constructive all₂ decision procedure which
rejects unequal lengths. It does not truncate like an unchecked zip. -/
def entriesCheck (tree : ClosedCutTree) (entries : List Entry) : Bool :=
  decide (List.Forall₂ (fun bounds e => e.Valid bounds) (integerLeaves tree) entries)

theorem entriesCheck_sound {tree : ClosedCutTree} {entries : List Entry}
    (h : entriesCheck tree entries = true) :
    List.Forall₂ (fun bounds e => e.Valid bounds) (integerLeaves tree) entries :=
  of_decide_eq_true h

theorem entriesCheck_count {tree : ClosedCutTree} {entries : List Entry}
    (h : entriesCheck tree entries = true) :
    entries.length = (closedLeaves tree compactRegion).length := by
  rw [originalLeaves_eq_integerLeaves, List.length_map]
  exact (entriesCheck_sound h).length_eq.symm

/-- Six rational endpoint comparisons imply actual real box containment.
No real leaf-containment assertion is an input to the checker. -/
theorem Entry.literalLeaf_subset_box {e : Entry} {bounds : Bounds}
    (h : e.Valid bounds) : literalLeaf bounds ⊆ e.guard.box := by
  intro t ht
  have htbox : t ∈ Icc
      (realPoint (P2ThirdCompactUniformCover.rationalPoint bounds.1))
      (realPoint (P2ThirdCompactUniformCover.rationalPoint bounds.2)) := by
    simpa only [decode_eq_realPoint] using ht.2
  constructor
  · intro i
    have hlo : (e.guard.lo i : ℝ) ≤
        (P2ThirdCompactUniformCover.rationalPoint bounds.1 i : ℝ) := by
      exact_mod_cast (h.2.1 i).1
    exact hlo.trans (htbox.1 i)
  · intro i
    have hhi : (P2ThirdCompactUniformCover.rationalPoint bounds.2 i : ℝ) ≤
        (e.guard.hi i : ℝ) := by
      exact_mod_cast (h.2.1 i).2
    exact (htbox.2 i).trans hhi

/-- Checked queries and denominator floors supply the actual compact
kernel integral estimate, including its factor four, with no target bound
assumed. The existing local integration theorem discharges integrability. -/
theorem Entry.local_integral_bounds {e : Entry} {bounds : Bounds}
    (h : e.Valid bounds) :
    (∫ t in literalLeaf bounds, compactKernel t) ≤ (e.guard.integralUpper : ℝ) ∧
      (e.guard.integralUpper : ℝ) ≤ (e.charge : ℝ) / 2^80 := by
  constructor
  · exact BoxGuard.integral_leaf_le h.1
      (measurableSet_compactRegion.inter measurableSet_Icc) inter_subset_left
      (Entry.literalLeaf_subset_box h)
  · exact_mod_cast h.2.2

def realEntries (entries : List Entry) : List (ℝ × ℤ) :=
  entries.map (fun e => ((e.guard.integralUpper : ℝ), e.charge))

/-- The exact original leaf list receives one genuine analytic supplier
and one charge per occurrence. Ordering and length come from Forall₂. -/
theorem actual_local_suppliers {tree : ClosedCutTree} {entries : List Entry}
    (h : entriesCheck tree entries = true) :
    List.Forall₂ (fun leaf e =>
      (∫ t in leaf, compactKernel t) ≤ e.1 ∧ e.1 ≤ (e.2 : ℝ) / 2^80)
      (closedLeaves tree compactRegion) (realEntries entries) := by
  rw [originalLeaves_eq_integerLeaves, realEntries,
    List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact (entriesCheck_sound h).imp (fun bounds e he => Entry.local_integral_bounds he)

/-- Directed real integral bound by the sum of the actual stored integer
charges. The existing closed-face and positional aggregation is reused. -/
theorem compactIntegral_le_charge_sum {tree : ClosedCutTree} {entries : List Entry}
    (h : entriesCheck tree entries = true) :
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection ≤
      (((entries.map Entry.charge).sum : ℤ) : ℝ) / 2^80 := by
  have hb := originalCompactThirdCorrection_le_sum_storedCharges tree
    (realEntries entries) (actual_local_suppliers h)
  simpa only [realEntries, List.map_map, Function.comp_def] using hb

/-- The historical compact allowance, in the original integer Q80 units. -/
def adoptedCharge : ℤ := 144590669409566793572719

def adoptedCheck (tree : ClosedCutTree) (entries : List Entry) : Bool :=
  entriesCheck tree entries && decide ((entries.map Entry.charge).sum ≤ adoptedCharge)

/-- Full finite-check soundness for the actual original compact integral.
The Boolean is not evaluated here: the genuine original tree, complete
entry list and proof of its acceptance are still required. -/
theorem adoptedCheck_sound {tree : ClosedCutTree} {entries : List Entry}
    (h : adoptedCheck tree entries = true) :
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection ≤
      144590669409566793572719 / (2 : ℝ)^80 := by
  have hc : entriesCheck tree entries = true := (Bool.and_eq_true.mp h).1
  have hs : (entries.map Entry.charge).sum ≤ adoptedCharge :=
    of_decide_eq_true (Bool.and_eq_true.mp h).2
  apply (compactIntegral_le_charge_sum hc).trans
  apply div_le_div_of_nonneg_right
  · have hs' : (entries.map Entry.charge).sum ≤ (144590669409566793572719 : ℤ) := hs
    exact_mod_cast hs'
  · positivity

/-- The accepted compact component may be passed to the existing complete
third-integral consumer. The tail is precisely the existing Tnew supplier;
no new tail analysis or reserve is introduced. -/
theorem adoptedCheck_full_integral {tree : ClosedCutTree} {entries : List Entry}
    (h : adoptedCheck tree entries = true) :
    actualExtendedThirdIdealFunctional ≤
      144590669409566793572719 / (2 : ℝ)^80 +
        OriginalThirdTailActualIdealSourceOnly.Tnew := by
  have hb := OriginalThirdFiniteReserveSourceOnly.idealFunctional_le_compact_add_Tnew
  change actualExtendedThirdIdealFunctional ≤
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection +
      OriginalThirdTailActualIdealSourceOnly.Tnew at hb
  exact hb.trans (add_le_add_right (adoptedCheck_sound h) _)

end

end ImbalancedChen.Certificates.P2OriginalThirdTreeCertificate
