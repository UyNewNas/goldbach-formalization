import ImbalancedChen.P2OriginalCompactQ80Arithmetic
import ImbalancedChen.P4AActualLowerIncrementGapBound

/-!
SOURCE ONLY / UNCOMPILED / COMPLETE ENCLOSER TARGET OPEN.

All four actual Q80 pre-Jensen upper candidates are proved directly from the
max12 table, original32-term logs and actual lower-factor inequalities. The
outside/full-cap/zero-loss exits and nonsymmetric boundary enclosure are
proved for the actual source integral. Final inside/Jensen and symmetric
half-mass composition is in the separate CompleteSoundness module; this file
does not assume a comparison to any original stored charge.
-/
namespace ImbalancedChen.P2OriginalCompactQ80LeafSourceOnly

noncomputable section
open Set MeasureTheory
open Certificates.P2HistoricQ80DefectLookup
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactBoundaryCapFloorSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P2OriginalAdaptiveSourceSplitSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdP4AOriginalClippedGapSourceOnly
open OriginalThirdP4AOrdinaryRawFallbackAllOldSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdP4AActualLowerIncrementGapBoundSourceOnly

/-- Only original coordinate constraints. No assertion, cap inequality,
table result, mean estimate or desired integral is stored as a field. -/
structure Geometry (box : RawBox) : Prop where
  lower : ∀ i, cutoffInteger ≤ box.1 i
  upper : ∀ i, box.2 i ≤ rhoInteger
  width : ∀ i, box.1 i < box.2 i
  muCut : box.2 0 ≤ muInteger ∨ muInteger ≤ box.1 0

theorem geometry_recordAt (i : Fin 21) : Geometry (recordAt i) := by
  fin_cases i <;> constructor <;> try (intro j; fin_cases j) <;>
    norm_num [recordAt,records,H,M,R,cutoffInteger,rhoInteger,muInteger]

theorem Geometry.of_subbox {parent child : RawBox} (g : Geometry parent)
    (hl : parent.1 ≤ child.1) (hu : child.2 ≤ parent.2)
    (hw : ∀ i, child.1 i < child.2 i) : Geometry child := by
  refine ⟨fun i => (g.lower i).trans (hl i),
    fun i => (hu i).trans (g.upper i),hw,?_⟩
  rcases g.muCut with h | h
  · exact Or.inl ((hu 0).trans h)
  · exact Or.inr (h.trans (hl 0))

theorem geometry_sourceLeft {box : RawBox} (g : Geometry box)
    (hw : box.1 (originalAxis box)+2 ≤ box.2 (originalAxis box)) :
    Geometry (sourceLeft box) := by
  obtain ⟨hl,hu⟩ := originalMidpoint_interior box hw
  apply g.of_subbox
  · exact le_rfl
  · intro i
    by_cases he : i = originalAxis box
    · subst i
      simpa [sourceLeft] using hu.le
    · simp [sourceLeft,Function.update_of_ne he]
  · intro i
    by_cases he : i = originalAxis box
    · subst i
      simpa [sourceLeft] using hl
    · simpa [sourceLeft,Function.update_of_ne he] using g.width i

theorem geometry_sourceRight {box : RawBox} (g : Geometry box)
    (hw : box.1 (originalAxis box)+2 ≤ box.2 (originalAxis box)) :
    Geometry (sourceRight box) := by
  obtain ⟨hl,hu⟩ := originalMidpoint_interior box hw
  apply g.of_subbox
  · intro i
    by_cases he : i = originalAxis box
    · subst i
      simpa [sourceRight] using hl.le
    · simp [sourceRight,Function.update_of_ne he]
  · exact le_rfl
  · intro i
    by_cases he : i = originalAxis box
    · subst i
      simpa [sourceRight] using hu
    · simpa [sourceRight,Function.update_of_ne he] using g.width i

theorem decode_binding (v : Fin 3 → ℤ) (i : Fin 3) :
    decodeCoordinates v i = (v i : ℝ)/(denominator : ℝ) := by
  norm_num [decodeCoordinates,coordinateDenominator,denominator]

theorem Geometry.raw_positive {box : RawBox} (g : Geometry box) (i : Fin 3) :
    0 < box.1 i := (by norm_num [cutoffInteger] : (0 : ℤ)<cutoffInteger).trans_le (g.lower i)

theorem Geometry.positive {box : RawBox} (g : Geometry box) (i : Fin 3) :
    0 < decodeCoordinates box.1 i := by
  rw [decode_binding]
  exact div_pos (by exact_mod_cast g.raw_positive i) (by norm_num [denominator])

theorem Geometry.real_width {box : RawBox} (g : Geometry box) (i : Fin 3) :
    decodeCoordinates box.1 i < decodeCoordinates box.2 i := by
  rw [decode_binding,decode_binding]
  exact (div_lt_div_iff_of_pos_right (by norm_num [denominator] : (0 : ℝ)<denominator)).2
    (by exact_mod_cast g.width i)

/-- Literal cap-floor operand identity; in particular xyz precedes xz,yz,
and each rising/falling endpoint is floor-rounded before min/max. -/
theorem phiRange_lower_eq_author (box : RawBox) :
    (phiRange box).lo = authorCapLower box.1 box.2 := by
  simp [phiRange,authorCapLower,authorBelowCapLower,authorSums,sumRanges,
    vLower,sourceVLower,rawSum,literalTentX,literalTentY,literalTentZ,
    denominator,thetaInteger,muInteger]

theorem phiRange_lower_le_theta (box : RawBox) : (phiRange box).lo ≤ thetaInteger := by
  rw [phiRange_lower_eq_author]
  exact authorCapLower_le_theta box.1 box.2

/-- The original assert cap_lo-x1-y1>0 holds on every such source descendant;
it is not a separately accepted numerical leaf guard. -/
theorem Geometry.residual {box : RawBox} (g : Geometry box) :
    box.2 0+box.2 1 < (phiRange box).lo := by
  rw [phiRange_lower_eq_author]
  exact authorCapLower_residual_of_original_cube box.1 box.2 (g.lower 0) g.upper

theorem cap_floor_on_actual_intersection (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    ((phiRange box).lo : ℝ)/(denominator : ℝ) ≤
      actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
  rw [phiRange_lower_eq_author]
  exact author_boundary_cap_floor box.1 box.2
    (decodeCoordinates box.1) (decodeCoordinates box.2)
    (decode_binding box.1) (decode_binding box.2)
    (fun i => (g.width i).le) g.muCut ht

/-- Closed ordering and old-cube constraints imply the three exact integer
non-outside inequalities, including points on every boundary face. -/
theorem raw_constraints_of_mem (box : RawBox) {t : Point} (ht : t ∈ rootCell box) :
    box.1 1 ≤ box.2 0 ∧ box.1 2 ≤ box.2 1 ∧
      box.1 0+box.1 1+3*box.1 2 ≤ thetaInteger := by
  have hD : (0 : ℝ) < (denominator : ℝ) := by norm_num [denominator]
  have hxy : t 1 ≤ t 0 := ht.1.1.1.2.2.2.1
  have hyz : t 2 ≤ t 1 := ht.1.1.1.2.2.1
  have hcube : t 0+t 1+3*t 2 ≤ thirdPrefixTheta := by
    simpa only [mul_zero,sub_zero] using ht.1.1.2
  have hxy' := (ht.2.1 1).trans (hxy.trans (ht.2.2 0))
  have hyz' := (ht.2.1 2).trans (hyz.trans (ht.2.2 1))
  rw [decode_binding,decode_binding] at hxy' hyz'
  refine ⟨?_,?_,?_⟩
  · exact_mod_cast (div_le_div_iff_of_pos_right hD).1 hxy'
  · exact_mod_cast (div_le_div_iff_of_pos_right hD).1 hyz'
  · have hsum : decodeCoordinates box.1 0+decodeCoordinates box.1 1+
        3*decodeCoordinates box.1 2 ≤ thirdPrefixTheta := by
      linarith only [hcube,ht.2.1 0,ht.2.1 1,ht.2.1 2]
    have htD : thirdPrefixTheta = (thetaInteger : ℝ)/(denominator : ℝ) := by
      norm_num [thirdPrefixTheta,thetaInteger,denominator]
    simp only [decode_binding] at hsum
    rw [htD] at hsum
    have he : (box.1 0 : ℝ)/(denominator : ℝ)+(box.1 1 : ℝ)/(denominator : ℝ)+
        3*((box.1 2 : ℝ)/(denominator : ℝ)) =
        ((box.1 0+box.1 1+3*box.1 2 : ℤ) : ℝ)/(denominator : ℝ) := by
      push_cast
      ring
    rw [he] at hsum
    exact_mod_cast (div_le_div_iff_of_pos_right hD).1 hsum

theorem outside_rootCell_empty (box : RawBox) (ho : outside box) : rootCell box = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨hxy,hyz,hcube⟩ := raw_constraints_of_mem box ht
  unfold outside at ho
  omega

theorem outside_actual_integral_zero (box : RawBox) (ho : outside box) :
    (∫ t in rootCell box,compactKernel t) = 0 := by
  rw [outside_rootCell_empty box ho]
  simp

/-- This exit is an exact integral equality, not an omitted terminal leaf. -/
theorem outside_enclose_contains_integral (box : RawBox) (ho : outside box) :
    val (enclose box).lower ≤ (∫ t in rootCell box,compactKernel t) ∧
      (∫ t in rootCell box,compactKernel t) ≤ val (enclose box).upper := by
  rw [enclose_outside box ho,outside_actual_integral_zero box ho]
  simp [val]

theorem fullCap_kernel_zero (box : RawBox) (g : Geometry box)
    (hc : thetaInteger ≤ (phiRange box).lo) {t : Point} (ht : t ∈ rootCell box) :
    compactKernel t = 0 := by
  have hf := cap_floor_on_actual_intersection box g ht
  have hD : (0 : ℝ) ≤ (denominator : ℝ) := by norm_num [denominator]
  have htheta : (thetaInteger : ℝ)/(denominator : ℝ) = thirdPrefixTheta := by
    norm_num [thetaInteger,denominator,thirdPrefixTheta]
  have hlow : thirdPrefixTheta ≤ actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
    rw [←htheta]
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) hD).trans hf
  have hhigh : actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) ≤ thirdPrefixTheta := by
    unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
    simp only [mul_zero,sub_zero]
    exact min_le_left _ _
  have he : actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) = thirdPrefixTheta :=
    le_antisymm hhigh hlow
  rw [compactKernel_eq_weighted_gap]
  simp [newArgument,actualOldArgument,he]

theorem fullCap_actual_integral_zero (box : RawBox) (g : Geometry box)
    (hc : thetaInteger ≤ (phiRange box).lo) :
    (∫ t in rootCell box,compactKernel t) = 0 := by
  have he : (∫ t in rootCell box,compactKernel t) = ∫ _t in rootCell box,(0 : ℝ) := by
    apply setIntegral_congr_fun (measurableSet_compactRegion.inter measurableSet_Icc)
    intro t ht
    exact fullCap_kernel_zero box g hc ht
  simpa using he

theorem fullCap_enclose_contains_integral (box : RawBox) (g : Geometry box)
    (hc : thetaInteger ≤ (phiRange box).lo) :
    val (enclose box).lower ≤ (∫ t in rootCell box,compactKernel t) ∧
      (∫ t in rootCell box,compactKernel t) ≤ val (enclose box).upper := by
  rw [enclose_fullCap box hc,fullCap_actual_integral_zero box g hc]
  simp [val]

/-- This is EXACTLY the source's paired_hi-paired_lo candidate. It is not
declared to equal the smaller final all-candidate minimum. -/
def pairedUpper (box : RawBox) : ℤ :=
  let ca := (phiRange box).lo
  max 0 ((point (clippedUpperNumerator box.1 box.2 ca) (box.2 2*box.1 2)).hi-
    (point (clippedStart box.2 ca) (box.2 2)).lo)

theorem pairedUpper_source_formula (box : RawBox) :
    pairedUpper box =
      let olo := (phiRange box).lo-box.2 0-box.2 1-box.2 2
      let sa := max (2*box.2 2) olo
      max 0 ((point (sa*box.1 2+(thetaInteger-(phiRange box).lo)*box.2 2)
        (box.2 2*box.1 2)).hi-(point sa (box.2 2)).lo) := rfl

theorem source_upperBeforeJensen_le_paired (box : RawBox) :
    upperBeforeJensen box ≤ pairedUpper box := by
  rw [pairedUpper_source_formula]
  unfold upperBeforeJensen
  split_ifs <;> omega

theorem pairedUpper_nonneg (box : RawBox) : 0 ≤ val (pairedUpper box) := by
  rw [pairedUpper,val_max,val_zero]
  exact le_max_left _ _

theorem pairedUpper_pointwise (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ≤ val (pairedUpper box) := by
  let ca := (phiRange box).lo
  have hz0 := g.raw_positive 2
  have hz1 := hz0.trans (g.width 2)
  have hz0R : (0 : ℝ) < box.1 2 := by exact_mod_cast hz0
  have hc : ca ≤ thetaInteger := phiRange_lower_le_theta box
  have hcap := cap_floor_on_actual_intersection box g ht
  have hd : (0 : ℝ) ≤ ((thetaInteger-ca : ℤ) : ℝ)/(box.1 2 : ℝ) :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hc) hz0R.le
  have hold := old_argument_lower_of_cap_floor box.1 box.2 ca
    (decodeCoordinates box.1) (decodeCoordinates box.2)
    (decode_binding box.1) (decode_binding box.2) g.positive g.real_width
    g.residual ht.2 hcap
  have hgap := argument_gap_le_original_delta box.1 box.2 ca
    (decodeCoordinates box.1) (decodeCoordinates box.2)
    (decode_binding box.1) g.positive hc ht.2 hcap
  have hs := shifted_gap (t := newArgument t) hold hd (by linarith only [hgap])
  have hargs := clipped_query_arguments box.1 box.2 ca hz0 hz1
  have hqh := ((contains_iff _ _).1 (point_contains_actual
    (clippedUpperNumerator box.1 box.2 ca) (box.2 2*box.1 2) (mul_pos hz1 hz0))).2
  have hql := ((contains_iff _ _).1
    (point_contains_actual (clippedStart box.2 ca) (box.2 2) hz1)).1
  rw [hargs.2,hargs.1] at hqh
  rw [hargs.1] at hql
  rw [pairedUpper,val_max,val_zero,val_sub]
  exact (hs.trans (sub_le_sub hqh hql)).trans (le_max_right _ _)

def oldFloorNumerator (box : RawBox) : ℤ :=
  (phiRange box).lo-box.2 0-box.2 1-box.2 2

def rawUpper (box : RawBox) : ℤ :=
  max 0 ((point (thetaInteger-box.1 0-box.1 1-box.1 2) (box.1 2)).hi-
    (point (oldFloorNumerator box) (box.2 2)).lo)

def secondDecayUpper (box : RawBox) : ℤ :=
  up (dUpper (oldFloorNumerator box-box.2 2) (box.2 2)*
    (thetaInteger-(phiRange box).lo)*box.2 2) (box.1 2*oldFloorNumerator box)

theorem old_argument_ge_source_floor (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    (oldFloorNumerator box : ℝ)/(box.2 2 : ℝ) ≤ actualOldArgument t :=
  old_argument_lower_of_cap_floor box.1 box.2 (phiRange box).lo
    (decodeCoordinates box.1) (decodeCoordinates box.2)
    (decode_binding box.1) (decode_binding box.2) g.positive g.real_width
    g.residual ht.2 (cap_floor_on_actual_intersection box g ht)

theorem actual_old_le_new (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) : actualOldArgument t ≤ newArgument t := by
  have hz : 0 < t 2 := (g.positive 2).trans_le (ht.2.1 2)
  have hc : actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) ≤ thirdPrefixTheta := by
    unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
    simp only [mul_zero,sub_zero]
    exact min_le_left _ _
  exact (div_le_div_iff_of_pos_right hz).2 (by
    change actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1-t 2 ≤
      thirdPrefixTheta-t 0-t 1-t 2
    linarith only [hc])

theorem actual_gap_nonnegative (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    0 ≤ actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) :=
  sub_nonneg.mpr (monotone_actualExtendedThirdLowerFactor (actual_old_le_new box g ht))

theorem new_argument_le_source_upper (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    newArgument t ≤ ((thetaInteger-box.1 0-box.1 1-box.1 2 : ℤ) : ℝ)/(box.1 2 : ℝ) := by
  have hD : (0 : ℝ) < (denominator : ℝ) := by norm_num [denominator]
  have hz : 0 < t 2 := (g.positive 2).trans_le (ht.2.1 2)
  have hz0 : (0 : ℝ) < box.1 2 := by exact_mod_cast g.raw_positive 2
  have htheta : (thetaInteger : ℝ)/(denominator : ℝ) = thirdPrefixTheta := by
    norm_num [thetaInteger,denominator,thirdPrefixTheta]
  have hN : 0 ≤ ((thetaInteger-box.1 0-box.1 1 : ℤ) : ℝ)/(denominator : ℝ) := by
    have hc := phiRange_lower_le_theta box
    have hr := g.residual
    have hx := g.width 0
    have hy := g.width 1
    exact div_nonneg (by exact_mod_cast (show (0 : ℤ)≤thetaInteger-box.1 0-box.1 1 by omega)) hD.le
  have hnum : thirdPrefixTheta-t 0-t 1 ≤
      ((thetaInteger-box.1 0-box.1 1 : ℤ) : ℝ)/(denominator : ℝ) := by
    have hx := ht.2.1 0
    have hy := ht.2.1 1
    rw [decode_binding] at hx hy
    simp only [Int.cast_sub,sub_div,htheta]
    linarith only [hx,hy]
  have hq := (div_le_div_of_nonneg_right hnum hz.le).trans
    (div_le_div_of_nonneg_left hN (g.positive 2) (ht.2.1 2))
  have heL : newArgument t = (thirdPrefixTheta-t 0-t 1)/t 2-1 := by
    unfold newArgument
    field_simp [hz.ne']
    ring
  have heR : (((thetaInteger-box.1 0-box.1 1 : ℤ) : ℝ)/(denominator : ℝ))/
      decodeCoordinates box.1 2-1 =
      ((thetaInteger-box.1 0-box.1 1-box.1 2 : ℤ) : ℝ)/(box.1 2 : ℝ) := by
    rw [decode_binding]
    push_cast
    field_simp [hD.ne',hz0.ne']
    ring
  rw [heL,←heR]
  exact sub_le_sub_right hq 1

theorem rawUpper_pointwise (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ≤ val (rawUpper box) := by
  have hn := ((contains_iff _ _).1 (point_contains_actual
    (thetaInteger-box.1 0-box.1 1-box.1 2) (box.1 2) (g.raw_positive 2))).2
  have ho := ((contains_iff _ _).1 (point_contains_actual
    (oldFloorNumerator box) (box.2 2) ((g.raw_positive 2).trans (g.width 2)))).1
  have hn' := (monotone_actualExtendedThirdLowerFactor (new_argument_le_source_upper box g ht)).trans hn
  have ho' := ho.trans (monotone_actualExtendedThirdLowerFactor (old_argument_ge_source_floor box g ht))
  rw [rawUpper,val_max,val_zero,val_sub]
  exact (sub_le_sub hn' ho').trans (le_max_right _ _)

theorem firstDecay_pointwise (box : RawBox) (g : Geometry box)
    (hgate : 3*box.2 2 ≤ oldFloorNumerator box)
    {t : Point} (ht : t ∈ rootCell box) :
    actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ≤
        val (dUpper (oldFloorNumerator box) (box.2 2)) := by
  have hz := (g.raw_positive 2).trans (g.width 2)
  have hzR : (0 : ℝ) < box.2 2 := by exact_mod_cast hz
  have hs3 : (3 : ℝ) ≤ (oldFloorNumerator box : ℝ)/(box.2 2 : ℝ) :=
    (le_div_iff₀ hzR).2 (by exact_mod_cast hgate)
  have hs2 : (2 : ℝ) ≤ (oldFloorNumerator box : ℝ)/(box.2 2 : ℝ) := by linarith
  have ho := old_argument_ge_source_floor box g ht
  have hn := actual_old_le_new box g ht
  have hnew2 := hs2.trans (ho.trans hn)
  have hnew : actualExtendedThirdLowerFactor (newArgument t) ≤
      upper ((oldFloorNumerator box : ℝ)/(box.2 2 : ℝ)) := by
    rw [←lower_eq_actual hnew2]
    exact (lower_le_upper hnew2).trans (upper_antitone hs2 hnew2 (ho.trans hn))
  have hold : lower ((oldFloorNumerator box : ℝ)/(box.2 2 : ℝ)) ≤
      actualExtendedThirdLowerFactor (actualOldArgument t) := by
    rw [lower_eq_actual hs2]
    exact monotone_actualExtendedThirdLowerFactor ho
  exact (sub_le_sub hnew hold).trans (dUpper_bounds_actual_gap _ _ hz hgate)

/-- The complete original derivative-decay operation, at its literal
four-threshold gate and with its final ceiling outside all three products. -/
theorem secondDecay_pointwise (box : RawBox) (g : Geometry box)
    (hgate : 4*box.2 2 ≤ oldFloorNumerator box)
    {t : Point} (ht : t ∈ rootCell box) :
    actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ≤ val (secondDecayUpper box) := by
  let ao := oldFloorNumerator box
  let ca := (phiRange box).lo
  have hz0 := g.raw_positive 2
  have hz1 := hz0.trans (g.width 2)
  have hz0R : (0 : ℝ) < box.1 2 := by exact_mod_cast hz0
  have hz1R : (0 : ℝ) < box.2 2 := by exact_mod_cast hz1
  have hao : 0 < ao := by dsimp [ao]; omega
  have hold := old_argument_ge_source_floor box g ht
  have hnew := actual_old_le_new box g ht
  have hdelta := argument_gap_le_original_delta box.1 box.2 ca
    (decodeCoordinates box.1) (decodeCoordinates box.2) (decode_binding box.1)
    g.positive (phiRange_lower_le_theta box) ht.2 (cap_floor_on_actual_intersection box g ht)
  have hanchor := dUpper_bounds_actual_gap (ao-box.2 2) (box.2 2) hz1 (by dsimp [ao]; omega)
  have hanchor' : canonicalFactorGap (((ao : ℝ)-(box.2 2 : ℝ))/(box.2 2 : ℝ)) ≤
      val (dUpper (ao-box.2 2) (box.2 2)) := by
    simpa only [canonicalFactorGap,Int.cast_sub] using hanchor
  have hi := actualLowerFactor_increment_le_original_second_decay_anchor
    hz0R hz1R (by exact_mod_cast hgate) hold hnew hdelta hanchor'
  have hround := ceiling_rounds_up
    (dUpper (ao-box.2 2) (box.2 2)*(thetaInteger-ca)*box.2 2)
    (box.1 2*ao) (mul_pos hz0 hao)
  have he : val (dUpper (ao-box.2 2) (box.2 2))*
      ((thetaInteger-ca : ℤ) : ℝ)*(box.2 2 : ℝ)/((box.1 2 : ℝ)*(ao : ℝ)) =
      val (dUpper (ao-box.2 2) (box.2 2)*(thetaInteger-ca)*box.2 2)/
        ((box.1 2*ao : ℤ) : ℝ) := by
    rw [val_mul_int,val_mul_int]
    push_cast
    ring
  exact hi.trans (he.le.trans hround)

theorem upperBeforeJensen_pointwise (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ≤ val (upperBeforeJensen box) := by
  have hraw := rawUpper_pointwise box g ht
  have hpair := pairedUpper_pointwise box g ht
  have hmin {a b : ℤ} {x : ℝ} (ha : x ≤ val a) (hb : x ≤ val b) : x ≤ val (min a b) := by
    rcases le_total a b with h | h
    · simpa only [min_eq_left h] using ha
    · simpa only [min_eq_right h] using hb
  have hbase := hmin hraw hpair
  change _ ≤ val
    (if 4*box.2 2 ≤ oldFloorNumerator box then
      min (if 3*box.2 2 ≤ oldFloorNumerator box then
        min (min (rawUpper box) (pairedUpper box)) (dUpper (oldFloorNumerator box) (box.2 2))
        else min (rawUpper box) (pairedUpper box)) (secondDecayUpper box)
    else if 3*box.2 2 ≤ oldFloorNumerator box then
      min (min (rawUpper box) (pairedUpper box)) (dUpper (oldFloorNumerator box) (box.2 2))
      else min (rawUpper box) (pairedUpper box))
  by_cases h4 : 4*box.2 2 ≤ oldFloorNumerator box
  · rw [if_pos h4]
    by_cases h3 : 3*box.2 2 ≤ oldFloorNumerator box
    · rw [if_pos h3]
      exact hmin (hmin hbase (firstDecay_pointwise box g h3 ht)) (secondDecay_pointwise box g h4 ht)
    · rw [if_neg h3]
      exact hmin hbase (secondDecay_pointwise box g h4 ht)
  · rw [if_neg h4]
    by_cases h3 : 3*box.2 2 ≤ oldFloorNumerator box
    · rw [if_pos h3]
      exact hmin hbase (firstDecay_pointwise box g h3 ht)
    · rw [if_neg h3]
      exact hbase

theorem zeroLoss_actual_integral_zero (box : RawBox) (g : Geometry box)
    (hz : upperBeforeJensen box = 0) : (∫ t in rootCell box,compactKernel t) = 0 := by
  have he : (∫ t in rootCell box,compactKernel t) = ∫ _t in rootCell box,(0 : ℝ) := by
    apply setIntegral_congr_fun (measurableSet_compactRegion.inter measurableSet_Icc)
    intro t ht
    have hupper := upperBeforeJensen_pointwise box g ht
    rw [hz,val_zero] at hupper
    have hgap := le_antisymm hupper (actual_gap_nonnegative box g ht)
    rw [compactKernel_eq_weighted_gap,hgap]
    ring
  simpa using he

theorem zeroLoss_enclose_contains_integral (box : RawBox) (g : Geometry box)
    (hz : upperBeforeJensen box = 0) :
    val (enclose box).lower ≤ (∫ t in rootCell box,compactKernel t) ∧
      (∫ t in rootCell box,compactKernel t) ≤ val (enclose box).upper := by
  rw [enclose_zeroLoss box hz,zeroLoss_actual_integral_zero box g hz]
  simp [val]

private theorem boxWeight_nonneg (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) :
    0 ≤ boxWeight t := by
  have hx := (g.positive 0).trans_le (ht.1 0)
  have hy := (g.positive 1).trans_le (ht.1 1)
  have hz := (g.positive 2).trans_le (ht.1 2)
  unfold boxWeight
  positivity

private theorem boxWeight_continuousOn (box : RawBox) (g : Geometry box) :
    ContinuousOn boxWeight (Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) := by
  have hcoord (i : Fin 3) : ContinuousOn (fun t : Point => t i)
      (Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) :=
    (continuous_apply i).continuousOn
  have hn (i : Fin 3) (t : Point)
      (ht : t ∈ Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) : t i ≠ 0 :=
    ((g.positive i).trans_le (ht.1 i)).ne'
  exact ((continuousOn_const.div (hcoord 0) (hn 0)).mul
    (continuousOn_const.div (hcoord 1) (hn 1))).mul
    (continuousOn_const.div ((hcoord 2).pow 2) (fun t ht => pow_ne_zero 2 (hn 2 t ht)))

theorem pairedUpper_integral (box : RawBox) (g : Geometry box) :
    (∫ t in rootCell box,compactKernel t) ≤
      4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2)*val (pairedUpper box) := by
  let f : Point → ℝ := fun t => 4*(boxWeight t*val (pairedUpper box))
  have hc : ContinuousOn f (Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) :=
    continuousOn_const.mul ((boxWeight_continuousOn box g).mul continuousOn_const)
  have hf := hc.integrableOn_compact isCompact_Icc
  have hk : IntegrableOn compactKernel (rootCell box) :=
    integrableOn_compactKernel.mono_set inter_subset_left
  have hmono : (∫ t in rootCell box,compactKernel t) ≤ ∫ t in rootCell box,f t := by
    apply integral_mono_ae hk (hf.mono_set inter_subset_right)
    filter_upwards [ae_restrict_mem
      (measurableSet_compactRegion.inter measurableSet_Icc)] with t ht
    rw [compactKernel_eq_weighted_gap]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pairedUpper_pointwise box g ht)
        (boxWeight_nonneg box g ht.2)) (by norm_num)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (decodeCoordinates box.1) (decodeCoordinates box.2))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (by norm_num)
      (mul_nonneg (boxWeight_nonneg box g ht) (pairedUpper_nonneg box))
  have hlarge := setIntegral_mono_set hf hnonneg
    (Filter.Eventually.of_forall (fun t (ht : t ∈ rootCell box) => ht.2))
  have hfull : (∫ t in Icc (decodeCoordinates box.1) (decodeCoordinates box.2),f t) =
      4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2)*val (pairedUpper box) := by
    have he : f = fun t => (4*val (pairedUpper box))*boxWeight t := by
      funext t
      dsimp [f]
      ring
    rw [he,integral_const_mul,integral_boxWeight _ _ g.positive (fun i => (g.real_width i).le)]
    ring
  exact hmono.trans (hlarge.trans_eq hfull)

theorem densityMass_contains_boxMass (box : RawBox) (g : Geometry box) :
    (densityMass box).Contains (4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2)) := by
  have h := densityMass_contains box g.raw_positive (fun i => (g.width i).le)
  have hD : (denominator : ℝ) ≠ 0 := by norm_num [denominator]
  have hn (i : Fin 3) : (box.1 i : ℝ) ≠ 0 := by exact_mod_cast (g.raw_positive i).ne'
  have hnh (i : Fin 3) : (box.2 i : ℝ) ≠ 0 := by
    exact_mod_cast ((g.raw_positive i).trans (g.width i)).ne'
  have hr (i : Fin 3) : decodeCoordinates box.2 i/decodeCoordinates box.1 i =
      (box.2 i : ℝ)/(box.1 i : ℝ) := by
    rw [decode_binding,decode_binding]
    field_simp [hD,hn i]
  have hz : (((4*denominator*(box.2 2-box.1 2) : ℤ) : ℝ)/
      ((box.1 2*box.2 2 : ℤ) : ℝ)) =
      4*(decodeCoordinates box.2 2-decodeCoordinates box.1 2)/
        (decodeCoordinates box.1 2*decodeCoordinates box.2 2) := by
    rw [decode_binding,decode_binding]
    push_cast
    field_simp [hD,hn 2,hnh 2]
    ring
  have he : Real.log ((box.2 0 : ℝ)/(box.1 0 : ℝ))*
      Real.log ((box.2 1 : ℝ)/(box.1 1 : ℝ))*
      ((4*denominator*(box.2 2-box.1 2) : ℤ) : ℝ)/((box.1 2*box.2 2 : ℤ) : ℝ) =
      4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2) := by
    rw [mul_div_assoc,hz]
    unfold boxMass zMass
    rw [hr 0,hr 1]
    ring
  rwa [he] at h

/-- A proved ORIGINAL Q80 candidate, not the full enclosure result. -/
def pairedFullCost (box : RawBox) : ℤ := up (pairedUpper box*(densityMass box).hi) scale

theorem original_Q80_paired_full_cost (box : RawBox) (g : Geometry box) :
    (∫ t in rootCell box,compactKernel t) ≤ val (pairedFullCost box) := by
  have hm := ((contains_iff _ _).1 (densityMass_contains_boxMass box g)).2
  calc
    (∫ t in rootCell box,compactKernel t) ≤
        4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2)*val (pairedUpper box) :=
      pairedUpper_integral box g
    _ ≤ val (densityMass box).hi*val (pairedUpper box) :=
      mul_le_mul_of_nonneg_right hm (pairedUpper_nonneg box)
    _ = val (pairedUpper box)*val (densityMass box).hi := by ring
    _ ≤ val (pairedFullCost box) := ceiling_product _ _

theorem secondDecay_nonnegative (box : RawBox) (g : Geometry box)
    (hgate : 4*box.2 2 ≤ oldFloorNumerator box) : 0 ≤ secondDecayUpper box := by
  have hz0 := g.raw_positive 2
  have hz1 := hz0.trans (g.width 2)
  have hao : 0 < oldFloorNumerator box := by omega
  have hd := dUpper_nonnegative (oldFloorNumerator box-box.2 2) (box.2 2) hz1 (by omega)
  have hc : 0 ≤ thetaInteger-(phiRange box).lo := sub_nonneg.mpr (phiRange_lower_le_theta box)
  exact Certificates.P2HistoricLogPointInterpreter.ceilDiv_nonnegative
    (mul_nonneg (mul_nonneg hd hc) hz1.le) (mul_pos hz0 hao)

theorem upperBeforeJensen_nonnegative (box : RawBox) (g : Geometry box) :
    0 ≤ val (upperBeforeJensen box) := by
  have hz1 := (g.raw_positive 2).trans (g.width 2)
  have hraw : 0 ≤ rawUpper box := le_max_left _ _
  have hpair : 0 ≤ pairedUpper box := le_max_left _ _
  have hbase : 0 ≤ min (rawUpper box) (pairedUpper box) := le_min hraw hpair
  have hi : 0 ≤ upperBeforeJensen box := by
    change 0 ≤
      (if 4*box.2 2 ≤ oldFloorNumerator box then
        min (if 3*box.2 2 ≤ oldFloorNumerator box then
          min (min (rawUpper box) (pairedUpper box)) (dUpper (oldFloorNumerator box) (box.2 2))
          else min (rawUpper box) (pairedUpper box)) (secondDecayUpper box)
      else if 3*box.2 2 ≤ oldFloorNumerator box then
        min (min (rawUpper box) (pairedUpper box)) (dUpper (oldFloorNumerator box) (box.2 2))
        else min (rawUpper box) (pairedUpper box))
    by_cases h4 : 4*box.2 2 ≤ oldFloorNumerator box
    · rw [if_pos h4]
      by_cases h3 : 3*box.2 2 ≤ oldFloorNumerator box
      · rw [if_pos h3]
        exact le_min (le_min hbase (dUpper_nonnegative _ _ hz1 h3))
          (secondDecay_nonnegative box g h4)
      · rw [if_neg h3]
        exact le_min hbase (secondDecay_nonnegative box g h4)
    · rw [if_neg h4]
      by_cases h3 : 3*box.2 2 ≤ oldFloorNumerator box
      · rw [if_pos h3]
        exact le_min hbase (dUpper_nonnegative _ _ hz1 h3)
      · rw [if_neg h3]
        exact hbase
  simpa only [val_zero] using val_mono hi

theorem actual_integral_nonnegative (box : RawBox) (g : Geometry box) :
    0 ≤ ∫ t in rootCell box,compactKernel t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem
    (measurableSet_compactRegion.inter measurableSet_Icc)] with t ht
  rw [compactKernel_eq_weighted_gap]
  exact mul_nonneg (by norm_num)
    (mul_nonneg (boxWeight_nonneg box g ht.2) (actual_gap_nonnegative box g ht))

def beforeJensenFullCost (box : RawBox) : ℤ :=
  up (upperBeforeJensen box*(densityMass box).hi) scale

theorem beforeJensen_integral (box : RawBox) (g : Geometry box) :
    (∫ t in rootCell box,compactKernel t) ≤ val (beforeJensenFullCost box) := by
  let f : Point → ℝ := fun t => 4*(boxWeight t*val (upperBeforeJensen box))
  have hc : ContinuousOn f (Icc (decodeCoordinates box.1) (decodeCoordinates box.2)) :=
    continuousOn_const.mul ((boxWeight_continuousOn box g).mul continuousOn_const)
  have hf := hc.integrableOn_compact isCompact_Icc
  have hk : IntegrableOn compactKernel (rootCell box) :=
    integrableOn_compactKernel.mono_set inter_subset_left
  have hmono : (∫ t in rootCell box,compactKernel t) ≤ ∫ t in rootCell box,f t := by
    apply integral_mono_ae hk (hf.mono_set inter_subset_right)
    filter_upwards [ae_restrict_mem
      (measurableSet_compactRegion.inter measurableSet_Icc)] with t ht
    rw [compactKernel_eq_weighted_gap]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (upperBeforeJensen_pointwise box g ht)
        (boxWeight_nonneg box g ht.2)) (by norm_num)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (decodeCoordinates box.1) (decodeCoordinates box.2))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (by norm_num)
      (mul_nonneg (boxWeight_nonneg box g ht) (upperBeforeJensen_nonnegative box g))
  have hlarge := setIntegral_mono_set hf hnonneg
    (Filter.Eventually.of_forall (fun t (ht : t ∈ rootCell box) => ht.2))
  have hfull : (∫ t in Icc (decodeCoordinates box.1) (decodeCoordinates box.2),f t) =
      4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2)*val (upperBeforeJensen box) := by
    have he : f = fun t => (4*val (upperBeforeJensen box))*boxWeight t := by
      funext t
      dsimp [f]
      ring
    rw [he,integral_const_mul,integral_boxWeight _ _ g.positive (fun i => (g.real_width i).le)]
    ring
  have hm := ((contains_iff _ _).1 (densityMass_contains_boxMass box g)).2
  calc
    (∫ t in rootCell box,compactKernel t) ≤
        4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2)*val (upperBeforeJensen box) :=
      hmono.trans (hlarge.trans_eq hfull)
    _ ≤ val (densityMass box).hi*val (upperBeforeJensen box) :=
      mul_le_mul_of_nonneg_right hm (upperBeforeJensen_nonnegative box g)
    _ = val (upperBeforeJensen box)*val (densityMass box).hi := by ring
    _ ≤ val (beforeJensenFullCost box) := ceiling_product _ _

/-- A complete ORIGINAL branch theorem, using the actual `enclose` result.
All original raw, paired, first-decay and second-decay minima remain active.
The two remaining hypotheses are literal source branch tests, not estimates.
Jensen and symmetric-half cases remain distinct open cases of the full task. -/
theorem boundary_nonsymmetric_enclose_contains_integral (box : RawBox) (g : Geometry box)
    (hi : ¬ inside box) (hs : ¬ symmetricHalf box) :
    val (enclose box).lower ≤ (∫ t in rootCell box,compactKernel t) ∧
      (∫ t in rootCell box,compactKernel t) ≤ val (enclose box).upper := by
  by_cases ho : outside box
  · exact outside_enclose_contains_integral box ho
  by_cases hc : thetaInteger ≤ (phiRange box).lo
  · exact fullCap_enclose_contains_integral box g hc
  by_cases hz : upperBeforeJensen box = 0
  · exact zeroLoss_enclose_contains_integral box g hz
  have he : enclose box = ⟨0,beforeJensenFullCost box⟩ := by
    simp [enclose,enclosureResult,ho,hc,hz,lowerDifference,hi,
      upperDifference,chargedMass,hs,beforeJensenFullCost]
  rw [he]
  exact ⟨by simpa only [val_zero] using actual_integral_nonnegative box g,
    beforeJensen_integral box g⟩

end
end ImbalancedChen.P2OriginalCompactQ80LeafSourceOnly
