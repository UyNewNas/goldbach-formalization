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

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly

/-- Every source split contributes one more closed leaf than it removes. -/
def splitCount : ClosedCutTree → ℕ
  | .leaf => 0
  | .split _ _ left right => 1 + splitCount left + splitCount right

/-- The actual recursor retains all leaves, including empty or zero-width
children; no positive-width heap filter is applied to this list. -/
theorem closedLeaves_length (tree : ClosedCutTree) (s : Set Point) :
    (closedLeaves tree s).length = splitCount tree + 1 := by
  induction tree generalizing s with
  | leaf => simp [closedLeaves, splitCount]
  | split axis cut left right ihL ihR =>
      change (closedLeaves left
          (s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}) ++
        closedLeaves right
          (s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis})).length =
        (1 + splitCount left + splitCount right) + 1
      rw [List.length_append, ihL, ihR]
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

def eraseCharges : ChargedCutTree → ClosedCutTree
  | .leaf _ => .leaf
  | .split axis cut left right =>
      .split axis cut (eraseCharges left) (eraseCharges right)

def totalCharge : ChargedCutTree → ℤ
  | .leaf charge => charge
  | .split _ _ left right => totalCharge left + totalCharge right

/-- Local integral bounds follow the original closed children exactly. No
whole compact-integral inequality occurs in a leaf premise. -/
def LocalChargeBound : ChargedCutTree → Set Point → Prop
  | .leaf charge, s =>
      (∫ t in s, compactKernel t) ≤ (charge : ℝ) / 2^80
  | .split axis cut left right, s =>
      LocalChargeBound left
          (s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}) ∧
        LocalChargeBound right
          (s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis})

/-- Recursive charge aggregation uses the actual closed-face-null integral
identity at every cut. No disjointness of closed children is postulated. -/
theorem integral_le_totalCharge (tree : ChargedCutTree) :
    ∀ {s : Set Point}, MeasurableSet s → s ⊆ compactRegion →
      LocalChargeBound tree s →
      (∫ t in s, compactKernel t) ≤ (totalCharge tree : ℝ) / 2^80 := by
  induction tree with
  | leaf charge =>
      intro s _ _ hlocal
      exact hlocal
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
          simp only [totalCharge, Int.cast_add, add_div]

/-- The actual original compact correction inherits the recursively summed
local charges. A historical tree and its leaf charges are still required to
instantiate this theorem. -/
theorem originalCompactThirdCorrection_le_totalCharge
    (tree : ChargedCutTree)
    (hlocal : LocalChargeBound tree compactRegion) :
    originalCompactThirdCorrection ≤ (totalCharge tree : ℝ) / 2^80 := by
  rw [originalCompactThirdCorrection_eq_sum_closedLeaves (eraseCharges tree)]
  rw [← integral_eq_sum_closedLeaves (eraseCharges tree)
    measurableSet_compactRegion (fun _ ht => ht)]
  exact integral_le_totalCharge tree measurableSet_compactRegion (fun _ ht => ht) hlocal

end
end ImbalancedChen.P4AOriginalClosedTreeStructuralAggregationSourceOnly
