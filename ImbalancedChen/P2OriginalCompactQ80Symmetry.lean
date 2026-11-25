import ImbalancedChen.P2OriginalCompactQ80Leaf
import ImbalancedChen.ActualThirdOriginalSymmetricJensenLeaf

/-!
SOURCE ONLY / UNCOMPILED / NO FINITE GUARD EVALUATED.

The source halves the reciprocal-density envelope, not the asymmetric literal
cap/history kernel.  The charged set is the ordered half of an equal-interval
square even at boundary cells.  At an inside cell it is exactly rootCell.
All integer floors and ceilings below are the literal Q80 operations.
-/
namespace ImbalancedChen.P2OriginalCompactQ80SymmetrySourceOnly

noncomputable section
open Set MeasureTheory
open Certificates.P2HistoricQ80DefectLookup
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSwapAuditSourceOnly
open OriginalThirdOldChordMeanSourceOnly
open OriginalThirdP4AOriginalClippedGapSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly

def rectangle (box : RawBox) : Set Point :=
  Icc (decodeCoordinates box.1) (decodeCoordinates box.2)

def chargeDomain (box : RawBox) : Set Point :=
  if symmetricHalf box then rectangle box ∩ {t | t 1 ≤ t 0} else rectangle box

def realChargedMass (box : RawBox) : ℝ :=
  if symmetricHalf box then
    (4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2))/2
  else 4*boxMass (decodeCoordinates box.1) (decodeCoordinates box.2)

theorem measurableSet_chargeDomain (box : RawBox) : MeasurableSet (chargeDomain box) := by
  unfold chargeDomain
  split_ifs
  · exact measurableSet_Icc.inter
      (isClosed_le (continuous_apply 1) (continuous_apply 0)).measurableSet
  · exact measurableSet_Icc

theorem chargeDomain_subset_rectangle (box : RawBox) :
    chargeDomain box ⊆ rectangle box := by
  unfold chargeDomain
  split_ifs
  · exact inter_subset_left
  · exact Subset.rfl

theorem rootCell_subset_chargeDomain (box : RawBox) : rootCell box ⊆ chargeDomain box := by
  intro t ht
  unfold chargeDomain
  split_ifs
  · exact ⟨ht.2,ht.1.1.1.2.2.2.1⟩
  · exact ht.2

theorem decode_le_decode {v w : Fin 3 → ℤ} {i j : Fin 3}
    (h : v i ≤ w j) : decodeCoordinates v i ≤ decodeCoordinates w j := by
  rw [decode_binding,decode_binding]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h)
    (by norm_num [denominator])

theorem source_lower_cutoff (box : RawBox) (g : Geometry box) (i : Fin 3) :
    (1/100 : ℝ) ≤ decodeCoordinates box.1 i := by
  have h := decode_le_decode (v := fun _ => cutoffInteger) (w := box.1)
    (i := i) (j := i) (g.lower i)
  have he : decodeCoordinates (fun _ => cutoffInteger) i = (1/100 : ℝ) := by
    norm_num [decode_binding,cutoffInteger,denominator]
  simpa only [he] using h

theorem source_upper_rho (box : RawBox) (g : Geometry box) (i : Fin 3) :
    decodeCoordinates box.2 i ≤ thirdPrefixRho := by
  have h := decode_le_decode (v := box.2) (w := fun _ => rhoInteger)
    (i := i) (j := i) (g.upper i)
  have he : decodeCoordinates (fun _ => rhoInteger) i = thirdPrefixRho := by
    norm_num [decode_binding,rhoInteger,denominator,thirdPrefixRho]
  simpa only [he] using h

theorem source_inside_sum (box : RawBox) (hi : inside box) :
    decodeCoordinates box.2 0+decodeCoordinates box.2 1+
      3*decodeCoordinates box.2 2 ≤ thirdPrefixTheta := by
  have h : ((box.2 0+box.2 1+3*box.2 2 : ℤ) : ℝ) ≤ (thetaInteger : ℝ) :=
    by exact_mod_cast hi.2.2
  have hh := div_le_div_of_nonneg_right h
    (by norm_num [denominator] : (0 : ℝ) ≤ denominator)
  have he : (thetaInteger : ℝ)/(denominator : ℝ) = thirdPrefixTheta := by
    norm_num [thirdPrefixTheta,thetaInteger,denominator]
  rw [he] at hh
  simpa only [decode_binding,Int.cast_add,Int.cast_mul,Int.cast_ofNat,
    add_div,mul_div_assoc] using hh

theorem source_symmetric_coordinates (box : RawBox) (hs : symmetricHalf box) :
    decodeCoordinates box.1 0 = decodeCoordinates box.1 1 ∧
      decodeCoordinates box.2 0 = decodeCoordinates box.2 1 := by
  constructor <;> simp only [decode_binding,hs.1,hs.2.1]

theorem source_rectangle_eq_symmetricBox (box : RawBox) (hs : symmetricHalf box) :
    rectangle box = symmetricBox (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
      (decodeCoordinates box.1 2) (decodeCoordinates box.2 2) := by
  obtain ⟨hl,hu⟩ := source_symmetric_coordinates box hs
  ext t
  constructor
  · intro ht
    exact ⟨⟨ht.1 0,ht.2 0⟩,⟨by simpa only [hl] using ht.1 1,
      by simpa only [hu] using ht.2 1⟩,⟨ht.1 2,ht.2 2⟩⟩
  · rintro ⟨hx,hy,hz⟩
    constructor <;> intro i <;> fin_cases i
    · exact hx.1
    · simpa only [hl] using hy.1
    · exact hz.1
    · exact hx.2
    · simpa only [hu] using hy.2
    · exact hz.2

theorem source_symmetricFullBox (box : RawBox) (g : Geometry box)
    (hi : inside box) (hs : symmetricHalf box) :
    SymmetricFullBox (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
      (decodeCoordinates box.1 2) (decodeCoordinates box.2 2) := by
  refine ⟨g.real_width 0,g.real_width 2,source_lower_cutoff box g 2,?_,
    source_upper_rho box g 0,?_,?_⟩
  · exact (decode_le_decode (v := box.2) (w := box.1) (i := 2) (j := 1) hs.2.2).trans_eq
      (source_symmetric_coordinates box hs).1.symm
  · have h := source_inside_sum box hi
    rw [← (source_symmetric_coordinates box hs).2] at h
    linarith
  · rcases g.muCut with h | h
    · left
      have hh := decode_le_decode (v := box.2) (w := fun _ => muInteger) (i := 0) (j := 0) h
      have he : decodeCoordinates (fun _ => muInteger) 0 = VariableEnvelope.mu := by
        norm_num [decode_binding,muInteger,denominator,VariableEnvelope.mu]
      simpa only [he] using hh
    · right
      have hh := decode_le_decode (v := fun _ => muInteger) (w := box.1) (i := 0) (j := 0) h
      have he : decodeCoordinates (fun _ => muInteger) 0 = VariableEnvelope.mu := by
        norm_num [decode_binding,muInteger,denominator,VariableEnvelope.mu]
      simpa only [he] using hh

/-- Equal endpoints in the order tests are retained. No strict separation of
the x/y or y/z intervals is needed. -/
theorem chargeDomain_eq_rootCell_of_inside (box : RawBox) (g : Geometry box)
    (hi : inside box) : chargeDomain box = rootCell box := by
  apply Subset.antisymm ?_ (rootCell_subset_chargeDomain box)
  by_cases hs : symmetricHalf box
  · have hg := source_symmetricFullBox box g hi hs
    intro t ht
    have ht' : t ∈ orderedHalf (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
        (decodeCoordinates box.1 2) (decodeCoordinates box.2 2) := by
      simpa only [chargeDomain,if_pos hs,source_rectangle_eq_symmetricBox box hs,
        orderedHalf] using ht
    exact ⟨orderedHalf_subset_compact _ _ _ _ hg ht',
      chargeDomain_subset_rectangle box ht⟩
  · have hxy : box.2 1 ≤ box.1 0 := hi.1.resolve_right hs
    have hsub := ordinary_full_box_subset_compact
      (decodeCoordinates box.1) (decodeCoordinates box.2) g.positive
      (source_lower_cutoff box g 2)
      (decode_le_decode (v := box.2) (w := box.1) (i := 1) (j := 0) hxy)
      (decode_le_decode (v := box.2) (w := box.1) (i := 2) (j := 1) hi.2.1)
      (source_upper_rho box g 0) (source_inside_sum box hi)
    intro t ht
    exact ⟨hsub (chargeDomain_subset_rectangle box ht),chargeDomain_subset_rectangle box ht⟩

/-- Analytic half mass with WEAK side lengths, hence including zero-width
rectangles and all closed faces. The change of variables is volume preserving. -/
theorem integral_density_orderedHalf {a b c d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) :
    (∫ t in orderedHalf a b c d,4*boxWeight t) = prismMass a b c d := by
  have hp : MeasurePreserving finPrismEquiv.symm volume volume :=
    finPrismEquiv_volume_preserving.symm finPrismEquiv
  have h := hp.setIntegral_preimage_emb finPrismEquiv.symm.measurableEmbedding
    (fun t => 4*boxWeight t) (orderedHalf a b c d)
  rw [prism_preimage_orderedHalf] at h
  have he (p : PrismPoint) : 4*boxWeight (finPrismEquiv.symm p) = prismWeight p := by
    rw [finPrismEquiv_symm_apply]
    dsimp [boxWeight,prismPoint,prismWeight,xyWeight]
    ring
  simp only [he] at h
  exact h.symm.trans (integral_prismWeight ha hab hc hcd)

/-- Only the density, which is symmetric, is halved. This formula holds for
boundary boxes too: no raw-domain fullness or actual-kernel symmetry is used. -/
theorem integral_chargeDomain_density (box : RawBox) (g : Geometry box) :
    (∫ t in chargeDomain box,4*boxWeight t) = realChargedMass box := by
  by_cases hs : symmetricHalf box
  · rw [chargeDomain,if_pos hs,source_rectangle_eq_symmetricBox box hs]
    change (∫ t in orderedHalf _ _ _ _,4*boxWeight t) = _
    rw [integral_density_orderedHalf (g.positive 0) (g.real_width 0).le
      (g.positive 2) (g.real_width 2).le]
    obtain ⟨hl,hu⟩ := source_symmetric_coordinates box hs
    simp only [realChargedMass,if_pos hs,boxMass,prismMass,triangleMass,← hl,← hu]
    ring
  · rw [chargeDomain,if_neg hs,realChargedMass,if_neg hs,rectangle,integral_const_mul,
      integral_boxWeight _ _ g.positive (fun i => (g.real_width i).le)]

theorem realChargedMass_pos (box : RawBox) (g : Geometry box) :
    0 < realChargedMass box := by
  have hm := boxMass_pos _ _ g.positive g.real_width
  unfold realChargedMass
  split_ifs <;> positivity

theorem boxWeight_nonnegative (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rectangle box) : 0 ≤ boxWeight t := by
  have hx := (g.positive 0).trans_le (ht.1 0)
  have hy := (g.positive 1).trans_le (ht.1 1)
  have hz := (g.positive 2).trans_le (ht.1 2)
  unfold boxWeight
  positivity

theorem density_integrable_rectangle (box : RawBox) (g : Geometry box) :
    IntegrableOn (fun t => 4*boxWeight t) (rectangle box) := by
  have hc (i : Fin 3) : ContinuousOn (fun t : Point => t i) (rectangle box) :=
    (continuous_apply i).continuousOn
  have hn (i : Fin 3) (t : Point) (ht : t ∈ rectangle box) : t i ≠ 0 :=
    ((g.positive i).trans_le (ht.1 i)).ne'
  have hw : ContinuousOn boxWeight (rectangle box) :=
    ((continuousOn_const.div (hc 0) (hn 0)).mul
      (continuousOn_const.div (hc 1) (hn 1))).mul
      (continuousOn_const.div ((hc 2).pow 2) (fun t ht => pow_ne_zero 2 (hn 2 t ht)))
  exact (continuousOn_const.mul hw).integrableOn_compact isCompact_Icc

/-- Boundary clipping can only decrease the nonnegative constant density
envelope. Its actual cap/history function is allowed to be asymmetric. -/
theorem integral_upper_of_pointwise (box : RawBox) (g : Geometry box) (u : ℝ)
    (hu : 0 ≤ u)
    (hgap : ∀ t ∈ rootCell box,
      actualExtendedThirdLowerFactor (newArgument t)-
        actualExtendedThirdLowerFactor (actualOldArgument t) ≤ u) :
    (∫ t in rootCell box,compactKernel t) ≤ u*realChargedMass box := by
  have hf : IntegrableOn (fun t => (4*boxWeight t)*u) (chargeDomain box) :=
    ((density_integrable_rectangle box g).mono_set (chargeDomain_subset_rectangle box)).mul_const u
  have hk : IntegrableOn compactKernel (rootCell box) :=
    integrableOn_compactKernel.mono_set inter_subset_left
  have hmono : (∫ t in rootCell box,compactKernel t) ≤
      ∫ t in rootCell box,(4*boxWeight t)*u := by
    apply integral_mono_ae hk (hf.mono_set (rootCell_subset_chargeDomain box))
    filter_upwards [ae_restrict_mem (measurableSet_compactRegion.inter measurableSet_Icc)] with t ht
    rw [compactKernel_eq_weighted_gap]
    have h := mul_le_mul_of_nonneg_left (hgap t ht)
      (mul_nonneg (by norm_num) (boxWeight_nonnegative box g ht.2))
    simpa only [mul_assoc] using h
  have hn : 0 ≤ᵐ[volume.restrict (chargeDomain box)] (fun t => (4*boxWeight t)*u) := by
    filter_upwards [ae_restrict_mem (measurableSet_chargeDomain box)] with t ht
    exact mul_nonneg (mul_nonneg (by norm_num)
      (boxWeight_nonnegative box g (chargeDomain_subset_rectangle box ht))) hu
  have hlarge := setIntegral_mono_set hf hn
    (Filter.Eventually.of_forall (fun t (ht : t ∈ rootCell box) => rootCell_subset_chargeDomain box ht))
  have he : (∫ t in chargeDomain box,(4*boxWeight t)*u) = u*realChargedMass box := by
    rw [integral_mul_const,integral_chargeDomain_density box g,mul_comm]
  exact hmono.trans (hlarge.trans_eq he)

theorem upperBeforeJensen_integral (box : RawBox) (g : Geometry box) :
    (∫ t in rootCell box,compactKernel t) ≤
      val (upperBeforeJensen box)*realChargedMass box :=
  integral_upper_of_pointwise box g _ (upperBeforeJensen_nonnegative box g)
    (fun _ ht => upperBeforeJensen_pointwise box g ht)

theorem integral_lower_of_pointwise (box : RawBox) (g : Geometry box)
    (hi : inside box) (l : ℝ)
    (hgap : ∀ t ∈ rootCell box, l ≤
      actualExtendedThirdLowerFactor (newArgument t)-
        actualExtendedThirdLowerFactor (actualOldArgument t)) :
    l*realChargedMass box ≤ ∫ t in rootCell box,compactKernel t := by
  have hf : IntegrableOn (fun t => (4*boxWeight t)*l) (rootCell box) :=
    ((density_integrable_rectangle box g).mono_set inter_subset_right).mul_const l
  have hk : IntegrableOn compactKernel (rootCell box) :=
    integrableOn_compactKernel.mono_set inter_subset_left
  have hm : (∫ t in rootCell box,(4*boxWeight t)*l) ≤
      ∫ t in rootCell box,compactKernel t := by
    apply integral_mono_ae hf hk
    filter_upwards [ae_restrict_mem (measurableSet_compactRegion.inter measurableSet_Icc)] with t ht
    rw [compactKernel_eq_weighted_gap]
    have h := mul_le_mul_of_nonneg_left (hgap t ht)
      (mul_nonneg (by norm_num) (boxWeight_nonnegative box g ht.2))
    simpa only [mul_assoc] using h
  rw [← chargeDomain_eq_rootCell_of_inside box g hi,integral_mul_const,
    integral_chargeDomain_density box g] at hm
  simpa only [mul_comm,chargeDomain_eq_rootCell_of_inside box g hi] using hm

/-- Exact signed floor/ceiling half. Odd endpoints are not divided in ℚ
and re-encoded: the original integer division is retained. -/
theorem half_contains (m : I80) {x : ℝ} (hm : m.Contains x) :
    (⟨m.lo/2,up m.hi 2⟩ : I80).Contains (x/2) := by
  obtain ⟨hl,hu⟩ := (contains_iff m x).1 hm
  apply (contains_iff _ _).2
  exact ⟨(floor_rounds_down m.lo 2 (by norm_num)).trans
      (div_le_div_of_nonneg_right hl (by norm_num)),
    (div_le_div_of_nonneg_right hu (by norm_num)).trans
      (ceiling_rounds_up m.hi 2 (by norm_num))⟩

theorem half_even_integer (k : ℤ) : (2*k)/2 = k ∧ up (2*k) 2 = k := by
  unfold up
  omega

theorem half_odd_integer (k : ℤ) : (2*k+1)/2 = k ∧ up (2*k+1) 2 = k+1 := by
  unfold up
  omega

theorem chargedMass_contains (box : RawBox) (g : Geometry box) :
    (chargedMass box).Contains (realChargedMass box) := by
  have h := densityMass_contains_boxMass box g
  unfold chargedMass realChargedMass
  split_ifs
  · exact half_contains _ h
  · exact h

theorem densityMass_lower_nonnegative (box : RawBox) (g : Geometry box) :
    0 ≤ (densityMass box).lo := by
  have hx := (logarithmicWidth_contains _ _ (g.raw_positive 0) (g.width 0).le).2
  have hy := (logarithmicWidth_contains _ _ (g.raw_positive 1) (g.width 1).le).2
  have hn : 0 ≤ 4*denominator*(box.2 2-box.1 2) :=
    mul_nonneg (by norm_num [denominator]) (sub_nonneg.mpr (g.width 2).le)
  have hd : 0 < box.1 2*box.2 2 :=
    mul_pos (g.raw_positive 2) ((g.raw_positive 2).trans (g.width 2))
  exact Int.ediv_nonneg
    (mul_nonneg (Int.ediv_nonneg (mul_nonneg hx hy) scale_pos.le) hn) hd.le

theorem chargedMass_lower_nonnegative (box : RawBox) (g : Geometry box) :
    0 ≤ (chargedMass box).lo := by
  unfold chargedMass
  split_ifs
  · exact Int.ediv_nonneg (densityMass_lower_nonnegative box g) (by norm_num)
  · exact densityMass_lower_nonnegative box g

theorem chargedMass_upper_nonnegative (box : RawBox) (g : Geometry box) :
    0 ≤ val (chargedMass box).hi :=
  (realChargedMass_pos box g).le.trans ((contains_iff _ _).1 (chargedMass_contains box g)).2

/-- True sorted-kernel halving on an interior square. Its symmetric extension
is explicitly distinct from compactKernel off the ordered domain. -/
theorem source_sorted_half_integral (box : RawBox) (g : Geometry box)
    (hi : inside box) (hs : symmetricHalf box) :
    (∫ t in rootCell box,compactKernel t) =
      (∫ t in rectangle box,sortedKernel t)/2 := by
  have hg := source_symmetricFullBox box g hi hs
  simpa only [rootCell,← source_rectangle_eq_symmetricBox box hs,rectangle] using
    actual_symmetric_half_integral _ _ _ _ hg

/-- Empty and null cells remain genuine zero integral terms. These lemmas
need no strict-width Geometry and make no claim about invalid Python inputs. -/
theorem integral_zero_of_rootCell_null (box : RawBox) (hnull : volume (rootCell box) = 0)
    (f : Point → ℝ) : (∫ t in rootCell box,f t) = 0 := by
  simp only [Measure.restrict_eq_zero.mpr hnull,integral_zero_measure]

theorem coordinate_wall_null (i : Fin 3) (c : ℝ) :
    volume {t : Point | t i = c} = 0 := by
  let L : Point →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i
  have hL : L ≠ 0 := by
    intro hz
    have hh := congrArg (fun J : Point →L[ℝ] ℝ => J (fun _ => 1)) hz
    norm_num [L] at hh
  simpa only [L,ContinuousLinearMap.proj_apply] using affinePrimeWall_volume_zero L hL c

theorem flat_rootCell_null (box : RawBox) (i : Fin 3) (he : box.1 i = box.2 i) :
    volume (rootCell box) = 0 := by
  apply measure_mono_null _ (coordinate_wall_null i (decodeCoordinates box.1 i))
  intro t ht
  have he' : decodeCoordinates box.1 i = decodeCoordinates box.2 i := by
    simp only [decode_binding,he]
  exact le_antisymm ((ht.2.2 i).trans_eq he'.symm) (ht.2.1 i)

theorem flat_actual_integral_zero (box : RawBox) (i : Fin 3) (he : box.1 i = box.2 i) :
    (∫ t in rootCell box,compactKernel t) = 0 :=
  integral_zero_of_rootCell_null box (flat_rootCell_null box i he) compactKernel

/-- Touching x/y intervals are not outside by the source's strict test.
Their actual ordered intersection is nevertheless a null diagonal. -/
theorem touching_xy_rootCell_null (box : RawBox) (he : box.2 0 = box.1 1) :
    volume (rootCell box) = 0 := by
  apply measure_mono_null _ xy_diagonal_volume_zero
  intro t ht
  have he' : decodeCoordinates box.2 0 = decodeCoordinates box.1 1 := by
    simp only [decode_binding,he]
  exact le_antisymm ((ht.2.2 0).trans (he'.le.trans (ht.2.1 1)))
    ht.1.1.1.2.2.2.1

theorem touching_xy_actual_integral_zero (box : RawBox) (he : box.2 0 = box.1 1) :
    (∫ t in rootCell box,compactKernel t) = 0 :=
  integral_zero_of_rootCell_null box (touching_xy_rootCell_null box he) compactKernel

theorem touching_yz_rootCell_null (box : RawBox) (he : box.2 1 = box.1 2) :
    volume (rootCell box) = 0 := by
  let L : Point →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1 -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2
  have hL : L ≠ 0 := by
    intro hz
    have hh := congrArg (fun J : Point →L[ℝ] ℝ => J ![0,1,0]) hz
    norm_num [L,Matrix.cons_val_two] at hh
  have hwall : volume {t : Point | t 1 = t 2} = 0 := by
    simpa [L,sub_eq_zero] using affinePrimeWall_volume_zero L hL 0
  apply measure_mono_null _ hwall
  intro t ht
  have he' : decodeCoordinates box.2 1 = decodeCoordinates box.1 2 := by
    simp only [decode_binding,he]
  exact le_antisymm ((ht.2.2 1).trans (he'.le.trans (ht.2.1 2)))
    ht.1.1.1.2.2.1

theorem touching_yz_actual_integral_zero (box : RawBox) (he : box.2 1 = box.1 2) :
    (∫ t in rootCell box,compactKernel t) = 0 :=
  integral_zero_of_rootCell_null box (touching_yz_rootCell_null box he) compactKernel

theorem reversed_rootCell_empty (box : RawBox) (i : Fin 3) (he : box.2 i < box.1 i) :
    rootCell box = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h : decodeCoordinates box.1 i ≤ decodeCoordinates box.2 i :=
    (ht.2.1 i).trans (ht.2.2 i)
  rw [decode_binding,decode_binding] at h
  have h' := (div_le_div_iff_of_pos_right
    (by norm_num [denominator] : (0 : ℝ) < denominator)).1 h
  have h'' : box.1 i ≤ box.2 i := by exact_mod_cast h'
  omega

end
end ImbalancedChen.P2OriginalCompactQ80SymmetrySourceOnly
