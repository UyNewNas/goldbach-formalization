/-!
SOURCE ONLY / UNCOMPILED.

A deliberately elementary whole-box upper rule for the original compact
third kernel. It does not repeat the reciprocal-density moments, Jensen,
chord integration, or the OriginalNode blocks. The rule integrates a constant
rational majorant after proving the old/new actual lower-factor arguments
are enclosed by literal rational node queries. A positive rational denominator
guard and the exact Cartesian volume give a rational upper bound.

All node values come from original_compact_query_112bit_encloses. This remains
a source dependency, not a newly asserted validation of the original node table.
The closed split-tree adapter proves leaf measurability and containment; its
remaining concrete inputs are finite rational guard checks and box containment.
-/
import ImbalancedChen.P2ThirdTailCertificateTruncation
import ImbalancedChen.ActualThirdOriginalRationalQuery
import ImbalancedChen.ActualThirdOriginalBoxMoments
import Mathlib.Data.List.Forall2

set_option Elab.async false

namespace ImbalancedChen.P2ThirdCompactCertifiedBoxIntegral

noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
open OriginalU2CoupledRecurrenceSourceOnly

abbrev Point := Fin 3 → ℝ
abbrev RationalPoint := Fin 3 → ℚ

def realPoint (a : RationalPoint) : Point := fun i => (a i : ℝ)

def queryLower (q : ℚ) : ℚ :=
  (originalQueryLo112 q : ℚ) / (originalWeightP : ℚ)

def queryUpper (q : ℚ) : ℚ :=
  (originalQueryHi112 q : ℚ) / (originalWeightP : ℚ)

/-- Actual lower-factor node bounds, supplied by the existing literal query
soundness theorem. No node enclosure is a premise of this module. -/
theorem query_encloses {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    (queryLower q : ℝ) ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (queryUpper q : ℝ) := by
  simpa only [queryLower, queryUpper, Rat.cast_div, Rat.cast_intCast, nodeValue]
    using original_compact_query_112bit_encloses hq2 hq12

/-- Pure rational certificate data. The box may overhang the clipped ordered
leaf; containment in this box is proved separately from the guard check. -/
structure BoxGuard where
  lo : RationalPoint
  hi : RationalPoint
  oldNode : ℚ
  newNode : ℚ
  denominator : ℚ
  coarseOld : Bool

def BoxGuard.box (c : BoxGuard) : Set Point := Icc (realPoint c.lo) (realPoint c.hi)

/-- Every condition is finite rational arithmetic. The new-node equality=2
is the exact zero-clamp option, and needs no spurious argument>=2 guard. -/
def BoxGuard.Valid (c : BoxGuard) : Prop :=
  (∀ i, 0 < c.lo i ∧ c.lo i ≤ c.hi i) ∧
  2 ≤ c.oldNode ∧ c.oldNode ≤ 12 ∧
  2 ≤ c.newNode ∧ c.newNode ≤ 12 ∧
  0 < c.denominator ∧
  c.denominator ≤ c.lo 0 * c.lo 1 * (c.lo 2)^2 ∧
  (c.coarseOld = true ∨
    (299 / 500 : ℚ) - c.lo 0 - c.lo 1 ≤ (c.oldNode + 1) * c.lo 2) ∧
  (c.newNode = 2 ∨
    (c.newNode + 1) * c.hi 2 ≤
      VariableEnvelope.qVLo (c.lo 0) (c.hi 0) - c.hi 0 - c.hi 1)

def BoxGuard.check (c : BoxGuard) : Bool := decide c.Valid

theorem BoxGuard.check_sound {c : BoxGuard} (hc : c.check = true) : c.Valid :=
  of_decide_eq_true hc

/-- The actual coarse bound f<=1/2 is used outside the sharp query route. -/
def BoxGuard.oldUpper (c : BoxGuard) : ℚ :=
  if c.coarseOld then 1 / 2 else queryUpper c.oldNode

def BoxGuard.numeratorUpper (c : BoxGuard) : ℚ :=
  max 0 (c.oldUpper - queryLower c.newNode)

def BoxGuard.kernelUpper (c : BoxGuard) : ℚ :=
  4 * c.numeratorUpper / c.denominator

def BoxGuard.integralUpper (c : BoxGuard) : ℚ :=
  c.kernelUpper * (c.hi 0 - c.lo 0) * (c.hi 1 - c.lo 1) * (c.hi 2 - c.lo 2)

theorem BoxGuard.kernelUpper_nonneg {c : BoxGuard} (hc : c.Valid) :
    0 ≤ c.kernelUpper := by
  have hd : 0 < c.denominator := hc.2.2.2.2.2.1
  unfold BoxGuard.kernelUpper BoxGuard.numeratorUpper
  exact div_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) hd.le

/-- This fallback is derived from the actual upper factor and its proved
antitonicity, so boxes with old argument>12 need no fictitious table query. -/
theorem actual_lower_le_half (s : ℝ) : actualExtendedThirdLowerFactor s ≤ 1 / 2 := by
  have hs : 2 ≤ max (2 : ℝ) s := le_max_left 2 s
  have h := (lower_le_upper hs).trans (upper_le_half hs)
  simpa only [lower, actualExtendedThirdLowerFactor] using h

/-- The fallback gives a valid certificate for every positive rational box
with a checked positive denominator floor, regardless of argument sizes. -/
def coarseGuard (a b : RationalPoint) (d : ℚ) : BoxGuard :=
  ⟨a, b, 2, 2, d, true⟩

theorem coarseGuard_valid (a b : RationalPoint) (d : ℚ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i)
    (hd : 0 < d) (hden : d ≤ a 0 * a 1 * (a 2)^2) :
    (coarseGuard a b d).Valid := by
  exact ⟨(fun i => ⟨ha i, hab i⟩), by norm_num, by norm_num,
    by norm_num, by norm_num, hd, hden, Or.inl rfl, Or.inl rfl⟩

/-- The argument guards are proved throughout the entire Cartesian box,
using the actual literal baseline v and its proved rational interval lower bound. -/
theorem BoxGuard.argument_bounds {c : BoxGuard} (hc : c.Valid)
    {t : Point} (ht : t ∈ c.box) :
    (c.coarseOld = true ∨
      (thirdPrefixTheta - t 0 - t 1 - t 2) / t 2 ≤ (c.oldNode : ℝ)) ∧
      (c.newNode = 2 ∨ (c.newNode : ℝ) ≤
        (actualExtendedThirdIdealCap (t 0) (t 1) (t 2) - t 0 - t 1 - t 2) / t 2) := by
  rcases hc with ⟨hcoord, ho2, _ho12, hn2, _hn12, _hd, _hden, hold, hnew⟩
  have ha (i : Fin 3) : 0 < (c.lo i : ℝ) := by exact_mod_cast (hcoord i).1
  have hz : 0 < t 2 := (ha 2).trans_le (ht.1 2)
  constructor
  · rcases hold with hcoarse | hguard
    · exact Or.inl hcoarse
    · right
      have ho : (0 : ℝ) ≤ (c.oldNode : ℝ) + 1 := by
        have : (2 : ℝ) ≤ (c.oldNode : ℝ) := by exact_mod_cast ho2
        linarith
      have hOldGuard : thirdPrefixTheta - (c.lo 0 : ℝ) - (c.lo 1 : ℝ) ≤
          ((c.oldNode : ℝ) + 1) * (c.lo 2 : ℝ) := by
        norm_num only [thirdPrefixTheta]
        exact_mod_cast hguard
      have hOldMul := mul_le_mul_of_nonneg_left (ht.1 2) ho
      apply (div_le_iff₀ hz).2
      nlinarith only [hOldGuard, hOldMul, ht.1 0, ht.1 1]
  · rcases hnew with hclamp | hguard
    · exact Or.inl hclamp
    · right
      have hn : (0 : ℝ) ≤ (c.newNode : ℝ) + 1 := by
        have : (2 : ℝ) ≤ (c.newNode : ℝ) := by exact_mod_cast hn2
        linarith
      have hNewGuard : ((c.newNode : ℝ) + 1) * (c.hi 2 : ℝ) ≤
          (VariableEnvelope.qVLo (c.lo 0) (c.hi 0) : ℝ) -
            (c.hi 0 : ℝ) - (c.hi 1 : ℝ) := by exact_mod_cast hguard
      have hNewMul := mul_le_mul_of_nonneg_left (ht.2 2) hn
      have hV := VariableEnvelope.qVLo_le_v (ht.1 0) (ht.2 0)
      have hCap := OriginalThirdIdealRhoMarginSourceOnly.v_le_literal_ideal
        (t 0) (t 1) (t 2)
      apply (le_div_iff₀ hz).2
      nlinarith only [hNewGuard, hNewMul, hV, hCap, ht.2 0, ht.2 1]

/-- Positive rational denominator guards are propagated monotonically through
all four coordinate factors of x*y*z^2. -/
theorem BoxGuard.denominator_le {c : BoxGuard} (hc : c.Valid)
    {t : Point} (ht : t ∈ c.box) :
    (0 : ℝ) < (c.denominator : ℝ) ∧
      (c.denominator : ℝ) ≤ t 0 * t 1 * (t 2)^2 := by
  rcases hc with ⟨hcoord, _ho2, _ho12, _hn2, _hn12, hd, hden, _hold, _hnew⟩
  have ha (i : Fin 3) : 0 < (c.lo i : ℝ) := by exact_mod_cast (hcoord i).1
  have hp (i : Fin 3) : 0 < t i := (ha i).trans_le (ht.1 i)
  have hxy : (c.lo 0 : ℝ) * (c.lo 1 : ℝ) ≤ t 0 * t 1 :=
    mul_le_mul (ht.1 0) (ht.1 1) (ha 1).le (hp 0).le
  have hsq : (c.lo 2 : ℝ)^2 ≤ (t 2)^2 :=
    (sq_le_sq₀ (ha 2).le (hp 2).le).2 (ht.1 2)
  have hprod := mul_le_mul hxy hsq (sq_nonneg (c.lo 2 : ℝ))
    (mul_nonneg (hp 0).le (hp 1).le)
  constructor
  · exact_mod_cast hd
  · have hg : (c.denominator : ℝ) ≤ (c.lo 0 : ℝ) * (c.lo 1 : ℝ) *
        (c.lo 2 : ℝ)^2 := by exact_mod_cast hden
    exact hg.trans hprod

/-- Literal actual old/new lower-factor bounds imply the full normalized
kernel majorant. The numerator max handles outward-rounding sign slack. -/
theorem BoxGuard.actual_kernel_le {c : BoxGuard} (hc : c.Valid)
    {t : Point} (ht : t ∈ c.box) :
    actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2) ≤ (c.kernelUpper : ℝ) := by
  rcases hc with ⟨hcoord, ho2, ho12, hn2, hn12, hd, hden, hold, hnew⟩
  have hv : c.Valid := ⟨hcoord, ho2, ho12, hn2, hn12, hd, hden, hold, hnew⟩
  have hargs := BoxGuard.argument_bounds hv ht
  have hOld : actualExtendedThirdLowerFactor
      ((thirdPrefixTheta - t 0 - t 1 - t 2) / t 2) ≤ (c.oldUpper : ℝ) := by
    by_cases hcoarse : c.coarseOld = true
    · simpa [BoxGuard.oldUpper, hcoarse] using
        actual_lower_le_half ((thirdPrefixTheta - t 0 - t 1 - t 2) / t 2)
    · have harg := hargs.1.resolve_left hcoarse
      have hfalse : c.coarseOld = false := by
        cases heq : c.coarseOld <;> simp_all
      simpa [BoxGuard.oldUpper, hfalse] using
        ((monotone_actualExtendedThirdLowerFactor harg).trans
          (query_encloses ho2 ho12).2)
  have hNew : (queryLower c.newNode : ℝ) ≤ actualExtendedThirdLowerFactor
      ((actualExtendedThirdIdealCap (t 0) (t 1) (t 2) - t 0 - t 1 - t 2) / t 2) := by
    rcases hargs.2 with hclamp | harg
    · have hnode := (query_encloses hn2 hn12).1
      have hzero : actualExtendedThirdLowerFactor (c.newNode : ℝ) = 0 := by
        simpa only [hclamp, Rat.cast_ofNat] using
          (actualExtendedThirdLowerFactor_of_le_two (s := 2) le_rfl)
      rw [hzero] at hnode
      exact hnode.trans (actualExtendedThirdLowerFactor_nonneg _)
    · exact (query_encloses hn2 hn12).1.trans
        (monotone_actualExtendedThirdLowerFactor harg)
  have hmaxQ : c.oldUpper - queryLower c.newNode ≤ c.numeratorUpper :=
    le_max_right _ _
  have hmax : (c.oldUpper : ℝ) - (queryLower c.newNode : ℝ) ≤
      (c.numeratorUpper : ℝ) := by exact_mod_cast hmaxQ
  have hdiff : actualExtendedThirdLowerFactor
        ((thirdPrefixTheta - t 0 - t 1 - t 2) / t 2) -
      actualExtendedThirdLowerFactor
        ((actualExtendedThirdIdealCap (t 0) (t 1) (t 2) - t 0 - t 1 - t 2) / t 2) ≤
        (c.numeratorUpper : ℝ) := by linarith only [hOld, hNew, hmax]
  have hNum : (0 : ℝ) ≤ (c.numeratorUpper : ℝ) := by
    exact_mod_cast (le_max_left (0 : ℚ) (c.oldUpper - queryLower c.newNode))
  have hDen := BoxGuard.denominator_le hv ht
  simp only [actualExtendedThirdOrderedKernel, mul_zero, sub_zero]
  change 4 * (actualExtendedThirdLowerFactor
      ((thirdPrefixTheta - t 0 - t 1 - t 2) / t 2) -
      actualExtendedThirdLowerFactor
      ((actualExtendedThirdIdealCap (t 0) (t 1) (t 2) - t 0 - t 1 - t 2) / t 2)) /
      (t 0 * t 1 * (t 2)^2) ≤ (c.kernelUpper : ℝ)
  calc
    _ ≤ 4 * (c.numeratorUpper : ℝ) / (t 0 * t 1 * (t 2)^2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by norm_num))
        (hDen.1.le.trans hDen.2)
    _ ≤ 4 * (c.numeratorUpper : ℝ) / (c.denominator : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hNum) hDen.1 hDen.2
    _ = _ := by simp only [BoxGuard.kernelUpper, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]

/-- Integrate a whole-box rational majorant over the actual clipped leaf.
The clipped leaf need not be a rectangle or have a known exact volume. -/
theorem BoxGuard.integral_leaf_le {c : BoxGuard} (hc : c.check = true)
    {leaf : Set Point} (hleaf : MeasurableSet leaf)
    (hcompact : leaf ⊆ OriginalThirdCompactPartitionSourceOnly.compactRegion)
    (hbox : leaf ⊆ c.box) :
    (∫ t in leaf, OriginalThirdCompactPartitionSourceOnly.compactKernel t) ≤
      (c.integralUpper : ℝ) := by
  have hv := BoxGuard.check_sound hc
  have hcoord := hv.1
  have hab : realPoint c.lo ≤ realPoint c.hi := by
    intro i
    exact_mod_cast (hcoord i).2
  have hK : (0 : ℝ) ≤ (c.kernelUpper : ℝ) := by
    exact_mod_cast BoxGuard.kernelUpper_nonneg hv
  have hfi : Integrable (leaf.indicator OriginalThirdCompactPartitionSourceOnly.compactKernel) :=
    (integrable_indicator_iff hleaf).2
      (OriginalThirdCompactPartitionSourceOnly.integrableOn_compactKernel.mono_set hcompact)
  have hconst : IntegrableOn (fun _ : Point => (c.kernelUpper : ℝ)) c.box :=
    (continuous_const.continuousOn).integrableOn_compact isCompact_Icc
  have hgi : Integrable (c.box.indicator (fun _ : Point => (c.kernelUpper : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).2 hconst
  have hdom : leaf.indicator OriginalThirdCompactPartitionSourceOnly.compactKernel ≤
      c.box.indicator (fun _ : Point => (c.kernelUpper : ℝ)) := by
    intro t
    by_cases ht : t ∈ leaf
    · rw [indicator_of_mem ht, indicator_of_mem (hbox ht)]
      exact BoxGuard.actual_kernel_le hv (hbox ht)
    · rw [indicator_of_notMem ht]
      by_cases hb : t ∈ c.box
      · rw [indicator_of_mem hb]
        exact hK
      · simp only [indicator_of_notMem hb, le_refl]
  have hi := integral_mono hfi hgi hdom
  rw [integral_indicator hleaf, integral_indicator measurableSet_Icc, setIntegral_const] at hi
  calc
    _ ≤ (volume c.box).toReal * (c.kernelUpper : ℝ) := by
      simpa only [Measure.real, smul_eq_mul] using hi
    _ = (c.integralUpper : ℝ) := by
      rw [show (volume c.box).toReal =
        ∏ i, (realPoint c.hi i - realPoint c.lo i) from Real.volume_Icc_pi_toReal hab]
      simp only [Fin.prod_univ_three, realPoint, BoxGuard.integralUpper,
        Rat.cast_mul, Rat.cast_sub]
      ring

/-- Whole-box specialization when the generator proves that the ordinary
Cartesian box lies inside the original compact manuscript domain. -/
theorem BoxGuard.integral_box_le {c : BoxGuard} (hc : c.check = true)
    (hcompact : c.box ⊆ OriginalThirdCompactPartitionSourceOnly.compactRegion) :
    (∫ t in c.box, actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) ≤
      (c.integralUpper : ℝ) := by
  exact BoxGuard.integral_leaf_le hc measurableSet_Icc hcompact (fun _ ht => ht)

/-- Every actual tree leaf is measurable and retains its original-domain
containment, including arbitrary closed coordinate cuts and empty children. -/
theorem closedLeaves_geometry
    (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree)
    {s : Set Point} (hs : MeasurableSet s) :
    ∀ leaf ∈ OriginalThirdCompactPartitionSourceOnly.closedLeaves tree s,
      MeasurableSet leaf ∧ leaf ⊆ s := by
  induction tree generalizing s with
  | leaf =>
      intro leaf hleaf
      change leaf ∈ [s] at hleaf
      have heq : leaf = s := List.mem_singleton.mp hleaf
      subst leaf
      exact ⟨hs, Subset.rfl⟩
  | split j m left right ihL ihR =>
      intro leaf hleaf
      let q : ℝ := (m : ℝ) / OriginalThirdCompactPartitionSourceOnly.coordinateDenominator
      have hL : MeasurableSet (s ∩ {t : Point | t j ≤ q}) :=
        hs.inter (isClosed_le (continuous_apply j) continuous_const).measurableSet
      have hR : MeasurableSet (s ∩ {t : Point | q ≤ t j}) :=
        hs.inter (isClosed_le continuous_const (continuous_apply j)).measurableSet
      change leaf ∈ OriginalThirdCompactPartitionSourceOnly.closedLeaves left
          (s ∩ {t : Point | t j ≤ q}) ++
        OriginalThirdCompactPartitionSourceOnly.closedLeaves right
          (s ∩ {t : Point | q ≤ t j}) at hleaf
      rcases List.mem_append.mp hleaf with hl | hr
      · obtain ⟨hm, hsub⟩ := ihL hL leaf hl
        exact ⟨hm, fun t ht => (hsub ht).1⟩
      · obtain ⟨hm, hsub⟩ := ihR hR leaf hr
        exact ⟨hm, fun t ht => (hsub ht).1⟩

/-- A list of checkable rational box guards discharges the per-leaf integral
premises of the complete-third certificate adapter. No leaf integral bound
is assumed. The remaining leaf inputs are only geometric box containment. -/
theorem fullIntegral_le_checked_boxes
    (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree)
    (certificates : List BoxGuard)
    (hcert : List.Forall₂
      (fun leaf c => c.check = true ∧ leaf ⊆ c.box)
      (OriginalThirdCompactPartitionSourceOnly.closedLeaves tree
        OriginalThirdCompactPartitionSourceOnly.compactRegion) certificates) :
    actualExtendedThirdIdealFunctional ≤
      ((certificates.map BoxGuard.integralUpper).map (fun q : ℚ => (q : ℝ))).sum +
        OriginalThirdTailActualIdealSourceOnly.Tnew := by
  have hgeom := closedLeaves_geometry tree
    OriginalThirdCompactPartitionSourceOnly.measurableSet_compactRegion
  have hboth : List.Forall₂
      (fun leaf c => (MeasurableSet leaf ∧
          leaf ⊆ OriginalThirdCompactPartitionSourceOnly.compactRegion) ∧
        c.check = true ∧ leaf ⊆ c.box)
      (OriginalThirdCompactPartitionSourceOnly.closedLeaves tree
        OriginalThirdCompactPartitionSourceOnly.compactRegion) certificates :=
    (List.forall₂_and_left _ _).2 ⟨hgeom, hcert⟩
  apply P2ThirdTailCertificateTruncation.fullIntegral_le_closedTree_certificate
    tree (certificates.map BoxGuard.integralUpper)
  rw [List.forall₂_map_right_iff]
  exact hboth.imp fun leaf c h =>
    BoxGuard.integral_leaf_le h.2.1 h.1.1 h.1.2 h.2.2

end
end ImbalancedChen.P2ThirdCompactCertifiedBoxIntegral
