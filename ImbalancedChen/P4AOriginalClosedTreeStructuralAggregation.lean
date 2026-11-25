import ImbalancedChen.Part4ActualThirdOriginalClosedSplitAggregation
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The frozen original compact run did not serialize its split tree. This module
therefore proves structural facts for the actual `ClosedCutTree` recursor and
the exact closed split integral identity. It does not instantiate a tree or
claim the historical 80-bit total charge.
-/

namespace ImbalancedChen.P4AOriginalClosedTreeStructuralAggregationSourceOnly

open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly

/-- Every source split contributes one more closed leaf than it removes. -/
def splitCount (tree : ClosedCutTree) : ℕ :=
  WellFounded.fix (C := fun _ => ℕ) (measure (sizeOf : ClosedCutTree → ℕ)).wf
    (fun t rec => by
      cases t with
      | leaf => exact 0
      | split axis cut left right =>
          exact 1 + rec left (by simp_wf; omega) + rec right (by simp_wf))
    tree

theorem splitCount_leaf : splitCount .leaf = 0 := by
  conv_lhs => unfold splitCount; rw [WellFounded.fix_eq]

theorem splitCount_split (axis : Fin 3) (cut : ℤ)
    (left right : ClosedCutTree) :
    splitCount (.split axis cut left right) = 1 + splitCount left + splitCount right := by
  conv_lhs => unfold splitCount; rw [WellFounded.fix_eq]
  rfl

/-- The actual recursor retains all leaves, including empty or zero-width
children; no positive-width heap filter is applied to this list. -/
theorem closedLeaves_length (tree : ClosedCutTree) (s : Set Point) :
    (closedLeaves tree s).length = splitCount tree + 1 := by
  induction tree generalizing s with
  | leaf => simp [closedLeaves, splitCount_leaf]
  | split axis cut left right ihL ihR =>
      change (closedLeaves left
          (s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}) ++
        closedLeaves right
          (s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis})).length =
        splitCount (ClosedCutTree.split axis cut left right) + 1
      rw [List.length_append, ihL, ihR, splitCount_split]
      omega

/-- Every point of the parent belongs to some actual closed leaf, and every
actual closed leaf lies in the parent. Shared cut faces may belong to both
children; the statement deliberately retains that multiplicity. -/
theorem mem_iff_exists_closedLeaf (tree : ClosedCutTree) :
    ∀ (s : Set Point) (t : Point),
      t ∈ s ↔ ∃ c ∈ closedLeaves tree s, t ∈ c := by
  induction tree with
  | leaf =>
      intro s t
      simp [closedLeaves]
  | split axis cut left right ihL ihR =>
      intro s t
      let sL : Set Point :=
        s ∩ {u : Point | u axis ≤ (cut : ℝ) / coordinateDenominator}
      let sR : Set Point :=
        s ∩ {u : Point | (cut : ℝ) / coordinateDenominator ≤ u axis}
      change t ∈ s ↔
        ∃ c ∈ closedLeaves left sL ++ closedLeaves right sR, t ∈ c
      constructor
      · intro ht
        rcases le_total (t axis) ((cut : ℝ) / coordinateDenominator) with hl | hr
        · obtain ⟨c, hc, htc⟩ := (ihL sL t).mp ⟨ht, hl⟩
          exact ⟨c, List.mem_append.mpr (Or.inl hc), htc⟩
        · obtain ⟨c, hc, htc⟩ := (ihR sR t).mp ⟨ht, hr⟩
          exact ⟨c, List.mem_append.mpr (Or.inr hc), htc⟩
      · rintro ⟨c, hc, htc⟩
        rcases List.mem_append.mp hc with hc | hc
        · exact ((ihL sL t).mpr ⟨c, hc, htc⟩).1
        · exact ((ihR sR t).mpr ⟨c, hc, htc⟩).1

/-- A charge is attached to each leaf at the corresponding source split
position. This is a shape-preserving annotation of `ClosedCutTree`, not a
replacement certificate or an independently generated cell stream. -/
inductive ChargedCutTree where
  | leaf (charge : ℤ) : ChargedCutTree
  | split (axis : Fin 3) (cut : ℤ)
      (left right : ChargedCutTree) : ChargedCutTree

def eraseCharges (tree : ChargedCutTree) : ClosedCutTree :=
  WellFounded.fix (C := fun _ => ClosedCutTree) (measure (sizeOf : ChargedCutTree → ℕ)).wf
    (fun t rec => by
      cases t with
      | leaf charge => exact .leaf
      | split axis cut left right =>
          exact .split axis cut
            (rec left (by simp_wf; omega)) (rec right (by simp_wf)))
    tree

theorem eraseCharges_leaf (charge : ℤ) :
    eraseCharges (.leaf charge) = ClosedCutTree.leaf := by
  conv_lhs => unfold eraseCharges; rw [WellFounded.fix_eq]

theorem eraseCharges_split (axis : Fin 3) (cut : ℤ)
    (left right : ChargedCutTree) :
    eraseCharges (.split axis cut left right) =
      .split axis cut (eraseCharges left) (eraseCharges right) := by
  conv_lhs => unfold eraseCharges; rw [WellFounded.fix_eq]
  all_goals rfl

def totalCharge (tree : ChargedCutTree) : ℤ :=
  WellFounded.fix (C := fun _ => ℤ) (measure (sizeOf : ChargedCutTree → ℕ)).wf
    (fun t rec => by
      cases t with
      | leaf charge => exact charge
      | split axis cut left right =>
          exact rec left (by simp_wf; omega) + rec right (by simp_wf))
    tree

theorem totalCharge_leaf (charge : ℤ) : totalCharge (.leaf charge) = charge := by
  conv_lhs => unfold totalCharge; rw [WellFounded.fix_eq]

theorem totalCharge_split (axis : Fin 3) (cut : ℤ)
    (left right : ChargedCutTree) :
    totalCharge (.split axis cut left right) = totalCharge left + totalCharge right := by
  conv_lhs => unfold totalCharge; rw [WellFounded.fix_eq]
  rfl

/-- Local integral bounds follow the original closed children exactly. No
whole compact-integral inequality occurs in a leaf premise. -/
noncomputable def LocalChargeBound : ChargedCutTree → Set Point → Prop :=
  ChargedCutTree.rec (motive := fun _ => Set Point → Prop)
    (fun charge s => (∫ t in s, compactKernel t) ≤ (charge : ℝ) / 2^80)
    (fun axis cut _ _ left right s =>
      left (s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}) ∧
        right (s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis}))

theorem LocalChargeBound_leaf (charge : ℤ) (s : Set Point) :
    LocalChargeBound (.leaf charge) s =
      ((∫ t in s, compactKernel t) ≤ (charge : ℝ) / 2^80) := rfl

theorem LocalChargeBound_split (axis : Fin 3) (cut : ℤ)
    (left right : ChargedCutTree) (s : Set Point) :
    LocalChargeBound (.split axis cut left right) s =
      (LocalChargeBound left (s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}) ∧
        LocalChargeBound right (s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis})) := rfl

/-- Recursive charge aggregation uses the actual closed-face-null integral
identity at every cut. No disjointness of closed children is postulated. -/
theorem integral_le_totalCharge (tree : ChargedCutTree) :
    ∀ {s : Set Point}, MeasurableSet s → s ⊆ compactRegion →
      LocalChargeBound tree s →
      (∫ t in s, compactKernel t) ≤ (totalCharge tree : ℝ) / 2^80 := by
  induction tree with
  | leaf charge =>
      intro s _ _ hlocal
      simpa only [totalCharge_leaf, LocalChargeBound_leaf] using hlocal
  | split axis cut left right ihL ihR =>
      intro s hs hsub hlocal
      let sL : Set Point :=
        s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}
      let sR : Set Point :=
        s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis}
      have hsL : MeasurableSet sL :=
        hs.inter (isClosed_le (continuous_apply axis) continuous_const).measurableSet
      have hsR : MeasurableSet sR :=
        hs.inter (isClosed_le continuous_const (continuous_apply axis)).measurableSet
      have hbL : LocalChargeBound left sL := hlocal.1
      have hbR : LocalChargeBound right sR := hlocal.2
      have hl := ihL hsL (fun t ht => hsub ht.1) hbL
      have hr := ihR hsR (fun t ht => hsub ht.1) hbR
      calc
        (∫ t in s, compactKernel t) =
            (∫ t in sL, compactKernel t) +
              (∫ t in sR, compactKernel t) :=
          compact_integral_closed_split hs hsub axis
            ((cut : ℝ) / coordinateDenominator)
        _ ≤ (totalCharge left : ℝ) / 2^80 +
              (totalCharge right : ℝ) / 2^80 := add_le_add hl hr
        _ = (totalCharge (ChargedCutTree.split axis cut left right) : ℝ) /
              2^80 := by
          simp only [totalCharge_split, Int.cast_add, add_div]

/-- The actual original compact correction inherits the recursively summed
local charges. A historical tree and its leaf charges are still required to
instantiate this theorem. -/
theorem originalCompactThirdCorrection_le_totalCharge
    (tree : ChargedCutTree)
    (hlocal : LocalChargeBound tree compactRegion) :
    _root_.ImbalancedChen.OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection ≤ (totalCharge tree : ℝ) / 2^80 := by
  change OriginalThirdCompactPartitionSourceOnly.originalCompactThirdCorrection ≤
    (totalCharge tree : ℝ) / 2^80
  rw [originalCompactThirdCorrection_eq_sum_closedLeaves (eraseCharges tree)]
  rw [← integral_eq_sum_closedLeaves (eraseCharges tree)
    measurableSet_compactRegion (fun _ ht => ht)]
  exact integral_le_totalCharge tree measurableSet_compactRegion (fun _ ht => ht) hlocal

end ImbalancedChen.P4AOriginalClosedTreeStructuralAggregationSourceOnly
