import ImbalancedChen.P2OriginalCompactQ80JensenGeometry
import ImbalancedChen.P2OriginalCompactQ80LogGuards

/-!
SOURCE ONLY / UNCOMPILED / NO FINITE GUARD EVALUATED.

The actual original selected Q80 Jensen candidate. The source selector,
log32 means, max12 lower/upper point queries, signed chord and clipping are
used unchanged. The actual ordered-square proof uses the two true ordered
minorant chords below mu and the true max-coordinate mean above mu.
No Jensen, leaf estimate, query estimate or internal positive-denominator
assertion is a hypothesis of the exported source theorem.
-/
namespace ImbalancedChen.P2OriginalCompactQ80JensenBoundsSourceOnly

noncomputable section
open Set MeasureTheory
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P2OriginalCompactQ80LogGuardsSourceOnly
open P2OriginalCompactQ80SymmetrySourceOnly
open P2OriginalCompactQ80JensenMomentsSourceOnly
open P2OriginalCompactQ80JensenSelectionSourceOnly
open P2OriginalCompactQ80JensenGeometrySourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly
open OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly

theorem source_new_upper (box : RawBox) (g : Geometry box) :
    actualExtendedThirdLowerFactor (realNewMean box) ≤
      val (point (newMean box).hi scale).hi :=
  new_query_upper box g (logarithmicWidth_lower_positive box g 0)
    (logarithmicWidth_lower_positive box g 1)

theorem source_old_chord_rounding (box : RawBox) (g : Geometry box) (hi : inside box)
    (p : SourcePlane) (hp : affineCapLower box=some p) (he : jensenEligible box p) :
    val (chordLower box p) ≤ realChord box p := by
  apply chordLower_le_realChord box p
  · exact oldMean_contains box p g (logarithmicWidth_lower_positive box g 0)
      (logarithmicWidth_lower_positive box g 1)
      (fun _ => logarithmicWidth_square_lower_positive box g 0)
  · exact source_old_strict_span box g p hp he
  · exact source_old_mean_mem_range box g hi p hp he
  · exact source_chord_denominator_guard box g p hp he

/-- All explicit source Jensen denominator assertions are derived. -/
theorem source_jensenAssertions (box : RawBox) (g : Geometry box) : jensenAssertions box := by
  cases hp : affineCapLower box with
  | none => simp [jensenAssertions,hp]
  | some p =>
      simp only [jensenAssertions,hp]
      intro he
      exact ⟨logarithmicWidth_lower_positive box g 0,
        logarithmicWidth_lower_positive box g 1,
        fun _ _ => logarithmicWidth_square_lower_positive box g 0,
        fun _ _ => source_chord_denominator_guard box g p hp he⟩

theorem source_old_low_ge_two (box : RawBox) (p : SourcePlane)
    (he : jensenEligible box p) (hh : 2 < oldHigh box p) : 2 ≤ oldLow box p := by
  by_contra hl
  exact he.2.2.2 ⟨lt_of_not_ge hl,hh⟩

theorem source_symmetric_cell (box : RawBox) (hs : symmetricHalf box) :
    rootCell box=compactRegion∩symmetricBox
      (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
      (decodeCoordinates box.1 2) (decodeCoordinates box.2 2) := by
  change compactRegion∩rectangle box=_
  rw [source_rectangle_eq_symmetricBox box hs]

theorem source_symmetric_mass (box : RawBox) (hs : symmetricHalf box) :
    prismMass (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
      (decodeCoordinates box.1 2) (decodeCoordinates box.2 2)=realChargedMass box := by
  obtain ⟨hl,hu⟩ := source_symmetric_coordinates box hs
  simp only [realChargedMass,if_pos hs,boxMass,prismMass,triangleMass,←hl,←hu]
  ring

theorem ordinary_selected_real_chord_upper (box : RawBox) (g : Geometry box)
    (hi : inside box) (hs : ¬symmetricHalf box) (p : SourcePlane)
    (hp : affineCapLower box=some p) (he : jensenEligible box p)
    (hh : 2 < oldHigh box p) :
    (∫ t in rootCell box,compactKernel t) ≤ realChargedMass box*
      max 0 (actualExtendedThirdLowerFactor (realNewMean box)-realChord box p) := by
  have hns : ¬aboveSymmetric box := fun h => hs h.2
  have hpos := (selected_coefficients box p hp).1
  have hlo : (2 : ℝ)≤(oldLow box p : ℝ) := by
    exact_mod_cast source_old_low_ge_two box p he hh
  have hspan : (oldLow box p : ℝ)<(oldHigh box p : ℝ) := by
    exact_mod_cast source_old_strict_span box g p hp he
  have hn : actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-boxEX (decodeCoordinates box.1) (decodeCoordinates box.2)-
        boxEY (decodeCoordinates box.1) (decodeCoordinates box.2))*
        boxEZInv (decodeCoordinates box.1) (decodeCoordinates box.2)-1)≤
      actualExtendedThirdLowerFactor (realNewMean box) := by
    rw [realNewMean_eq_physical box g]
  have hleaf := ordinary_full_leaf_old_chord_upper
    (decodeCoordinates box.1) (decodeCoordinates box.2) g.positive g.real_width
    (source_lower_cutoff box g 2) (decode_le_decode (hi.1.resolve_right hs))
    (decode_le_decode hi.2.1) (source_upper_rho box g 0) (source_inside_sum box hi)
    (planeA p) (planeB p) (planeC p) (planeE p)
    (oldLow box p : ℝ) (oldHigh box p : ℝ)
    (val (point (oldLow box p).num ((oldLow box p).den : ℤ)).lo)
    (val (point (oldHigh box p).num ((oldHigh box p).den : ℤ)).lo)
    (actualExtendedThirdLowerFactor (realNewMean box)) hlo hspan
    (fun t ht => planeOld_range box g p hpos he ht)
    (fun t ht => selected_old_minorant_ordinary box g hi hs p hp he ht)
    (rational_query_lower _) (rational_query_lower _) hn
  simpa only [rootCell,realChargedMass,if_neg hs,oldChordMean,realChord,
    ordinary_old_mean_eq box g p hpos hns] using hleaf

theorem symmetric_selected_real_chord_upper (box : RawBox) (g : Geometry box)
    (hi : inside box) (hs : symmetricHalf box) (p : SourcePlane)
    (hp : affineCapLower box=some p) (he : jensenEligible box p)
    (hh : 2 < oldHigh box p) :
    (∫ t in rootCell box,compactKernel t) ≤ realChargedMass box*
      max 0 (actualExtendedThirdLowerFactor (realNewMean box)-realChord box p) := by
  have hg := source_symmetricFullBox box g hi hs
  have hlo : (2 : ℝ)≤(oldLow box p : ℝ) := by
    exact_mod_cast source_old_low_ge_two box p he hh
  have hspan : (oldLow box p : ℝ)<(oldHigh box p : ℝ) := by
    exact_mod_cast source_old_strict_span box g p hp he
  let fl := val (point (oldLow box p).num ((oldLow box p).den : ℤ)).lo
  let fh := val (point (oldHigh box p).num ((oldHigh box p).den : ℤ)).lo
  have hfl : fl≤actualExtendedThirdLowerFactor (oldLow box p : ℝ) := rational_query_lower _
  have hfh : fh≤actualExtendedThirdLowerFactor (oldHigh box p : ℝ) := rational_query_lower _
  have hout : actualExtendedThirdLowerFactor (OriginalThirdSymmetricJensenSourceOnly.newMean
      (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
      (decodeCoordinates box.1 2) (decodeCoordinates box.2 2))≤
      actualExtendedThirdLowerFactor (realNewMean box) := by
    rw [source_symmetric_new_mean box g hs]
  by_cases hm : muInteger≤box.1 0
  · have habove : aboveSymmetric box := ⟨hm,hs⟩
    obtain ⟨hmean,hl,hh'⟩ := above_symmetric_mean_endpoints box g p hp habove
    have hleaf := OriginalThirdSymmetricJensenSourceOnly.original_symmetric_above_mu_leaf_upper
      hg (above_mu_real box hm) (by simpa only [hl] using hlo)
      (by simpa only [hl,hh'] using hspan)
      (by simpa only [hl] using hfl) (by simpa only [hh'] using hfh) hout
    have hc : OriginalThirdSymmetricJensenSourceOnly.symmetricChordMean
        (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
        (decodeCoordinates box.1 2) (decodeCoordinates box.2 2) fl fh=realChord box p := by
      simp only [OriginalThirdSymmetricJensenSourceOnly.symmetricChordMean,
        realChord,hmean,hl,hh',fl,fh]
    rw [←source_symmetric_cell box hs,source_symmetric_mass box hs,hc] at hleaf
    exact hleaf
  · have hns : ¬aboveSymmetric box := fun h => hm h.1
    have hmu := below_mu_of_not_above box g hm
    have hrows := affineCapLower_selected_cases box p hp
    rcases hrows with ⟨hcontra,hrow⟩ | ⟨_,hrow,hroot⟩
    · exact (hm hcontra).elim
    obtain ⟨ha,hb⟩ := source_symmetric_endpoint_functions box hs
    rcases hrow with hbase | ⟨s,k,htent,hbranch⟩
    · subst p
      obtain ⟨hl,hh'⟩ := base_endpoints box g
      have hmean := ordinary_base_mean_eq box g hns
      have hleaf := OriginalThirdP4ASymmetricBLeaf.symmetric_B_exact_leaf_upper
        hg hmu (by simpa only [hl,hb] using hlo)
        (by simpa only [hl,hb] using hfl) (by simpa only [hh',ha] using hfh) hout
      have hc : bOldChord
          (OriginalThirdP4ASymmetricTentPrerequisites.symmetricLeft
            (decodeCoordinates box.1 0) (decodeCoordinates box.1 2))
          (OriginalThirdP4ASymmetricTentPrerequisites.symmetricRight
            (decodeCoordinates box.2 0) (decodeCoordinates box.2 2)) fl fh=realChord box baseRow := by
        simp only [bOldChord,realChord,hmean,hl,hh',ha,hb,fl,fh]
      rw [←source_symmetric_cell box hs,source_symmetric_mass box hs,hc] at hleaf
      exact hleaf
    · subst p
      obtain ⟨hactive,hroot',hres⟩ := source_tent_geometry box s k hbranch hroot he
      obtain ⟨hl,hh'⟩ := source_tent_endpoints box g s k
      have hmean := ordinary_tent_mean_eq box g s k hns
      have hleaf := OriginalThirdP4ASixTentSymmetricLeaf.all_symmetric_tent_exact_leaf_upper
        s k hg hmu (by simpa only [ha,hb] using hactive)
        (by simpa only [ha,hb] using hroot') (by simpa only [hb] using hres)
        (by simpa only [hl,hb] using hlo) (by simpa only [hl,hb] using hfl)
        (by simpa only [hh',ha] using hfh) hout
      have hc : tentOldChord s k
          (OriginalThirdP4ASymmetricTentPrerequisites.symmetricLeft
            (decodeCoordinates box.1 0) (decodeCoordinates box.1 2))
          (OriginalThirdP4ASymmetricTentPrerequisites.symmetricRight
            (decodeCoordinates box.2 0) (decodeCoordinates box.2 2)) fl fh=
          realChord box (tentRow s k) := by
        simp only [tentOldChord,realChord,hmean,hl,hh',ha,hb,fl,fh]
      rw [←source_symmetric_cell box hs,source_symmetric_mass box hs,hc] at hleaf
      exact hleaf

private theorem factor_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f) :
    Integrable (fun t => actualExtendedThirdLowerFactor (f t)) μ := by
  apply Integrable.of_bound (measurable_actualExtendedThirdLowerFactor.comp hf).aestronglyMeasurable
    (1/(2*Real.exp Real.eulerMascheroniConstant))
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (actualExtendedThirdLowerFactor_nonneg _)]
    exact actualExtendedThirdLowerFactor_le_normalization _)

private theorem oldArgument_measurable : Measurable actualOldArgument := by
  have hx : Measurable (fun t : BoxPoint => t 0) := (continuous_apply 0).measurable
  have hy : Measurable (fun t : BoxPoint => t 1) := (continuous_apply 1).measurable
  have hz : Measurable (fun t : BoxPoint => t 2) := (continuous_apply 2).measurable
  exact ((((measurable_actualExtendedThirdBufferedCap 0).sub hx).sub hy).sub hz).div hz

/-- Source old_hi<=2 return: only NEW Jensen is needed; the old factor
integral is nonnegative. This also handles equality at two. -/
theorem new_only_integral_upper (box : RawBox) (g : Geometry box) (hi : inside box) :
    (∫ t in rootCell box,compactKernel t)≤
      realChargedMass box*actualExtendedThirdLowerFactor (realNewMean box) := by
  by_cases hs : symmetricHalf box
  · have hg := source_symmetricFullBox box g hi hs
    have hold : 0≤∫ p,actualExtendedThirdLowerFactor
        (OriginalThirdSymmetricJensenSourceOnly.actualPrismOld p)
        ∂prismProbability (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
          (decodeCoordinates box.1 2) (decodeCoordinates box.2 2) :=
      integral_nonneg (fun _ => actualExtendedThirdLowerFactor_nonneg _)
    have hout : actualExtendedThirdLowerFactor (OriginalThirdSymmetricJensenSourceOnly.newMean
        (decodeCoordinates box.1 0) (decodeCoordinates box.2 0)
        (decodeCoordinates box.1 2) (decodeCoordinates box.2 2))≤
        actualExtendedThirdLowerFactor (realNewMean box) := by
      rw [source_symmetric_new_mean box g hs]
    have hleaf := OriginalThirdP4ASixTentSymmetricLeaf.symmetric_leaf_upper_of_old_chord
      hg hold hout
    rw [←source_symmetric_cell box hs,source_symmetric_mass box hs] at hleaf
    simpa only [sub_zero,max_eq_right (actualExtendedThirdLowerFactor_nonneg _)] using hleaf
  · let μ := boxProbability (decodeCoordinates box.1) (decodeCoordinates box.2)
    letI : IsProbabilityMeasure μ := boxProbability_isProbability _ _ g.positive g.real_width
    have hm : Measurable (affineArgument thirdPrefixTheta (-1) (-1) (-1)) := by
      unfold affineArgument
      fun_prop
    have hn := factor_integrable μ _ hm
    have ho := factor_integrable μ actualOldArgument oldArgument_measurable
    have hroot : rootCell box=Icc (decodeCoordinates box.1) (decodeCoordinates box.2) := by
      rw [←chargeDomain_eq_rootCell_of_inside box g hi]
      simp only [chargeDomain,if_neg hs,rectangle]
    rw [hroot,integral_compactKernel_eq_box_mean _ _ g.positive g.real_width,
      realChargedMass,if_neg hs]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num)
      (boxMass_pos _ _ g.positive g.real_width).le)
    rw [integral_sub hn ho]
    have hnew := ordinary_full_box_new_Jensen _ _ g.positive g.real_width (source_inside_sum box hi)
    rw [←realNewMean_eq_physical box g] at hnew
    have hold : 0≤∫ t,actualExtendedThirdLowerFactor (actualOldArgument t)∂μ :=
      integral_nonneg (fun _ => actualExtendedThirdLowerFactor_nonneg _)
    exact (sub_le_self _ hold).trans hnew

theorem selected_rounded_integral_upper (box : RawBox) (g : Geometry box) (hi : inside box)
    (p : SourcePlane) (hp : affineCapLower box=some p) (he : jensenEligible box p)
    (hh : 2 < oldHigh box p) :
    (∫ t in rootCell box,compactKernel t) ≤
      val (max 0 ((point (newMean box).hi scale).hi-chordLower box p))*realChargedMass box := by
  have hreal : (∫ t in rootCell box,compactKernel t) ≤ realChargedMass box*
      max 0 (actualExtendedThirdLowerFactor (realNewMean box)-realChord box p) := by
    by_cases hs : symmetricHalf box
    · exact symmetric_selected_real_chord_upper box g hi hs p hp he hh
    · exact ordinary_selected_real_chord_upper box g hi hs p hp he hh
  have hround := rounded_difference_upper box p (source_new_upper box g)
    (source_old_chord_rounding box g hi p hp he)
  exact hreal.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hround (realChargedMass_pos box g).le)

/-- Complete source Jensen option bound, with no assertion, row certificate,
mean enclosure, factor query estimate or target-integral estimate premise. -/
theorem jensenDifferenceUpper_sound (box : RawBox) (g : Geometry box) (hi : inside box)
    (j : ℤ) (hj : jensenDifferenceUpper box=some j) :
    0≤val j ∧ (∫ t in rootCell box,compactKernel t)≤val j*realChargedMass box := by
  cases hp : affineCapLower box with
  | none => simp [jensenDifferenceUpper,hp] at hj
  | some p =>
      by_cases he : jensenEligible box p
      · by_cases hh : oldHigh box p≤2
        · have hj' : (point (newMean box).hi scale).hi=j := by
            simpa [jensenDifferenceUpper,hp,he,hh] using hj
          have hn : 0≤val (point (newMean box).hi scale).hi :=
            (actualExtendedThirdLowerFactor_nonneg _).trans (source_new_upper box g)
          rw [←hj']
          refine ⟨hn,?_⟩
          exact (new_only_integral_upper box g hi).trans (by
            simpa only [mul_comm] using mul_le_mul_of_nonneg_left (source_new_upper box g)
              (realChargedMass_pos box g).le)
        · have hj' : max 0 ((point (newMean box).hi scale).hi-chordLower box p)=j := by
            simpa [jensenDifferenceUpper,hp,he,hh] using hj
          rw [←hj']
          exact ⟨by rw [val_max,val_zero]; exact le_max_left _ _,
            selected_rounded_integral_upper box g hi p hp he (lt_of_not_ge hh)⟩
      · simp [jensenDifferenceUpper,hp,he] at hj

end
end ImbalancedChen.P2OriginalCompactQ80JensenBoundsSourceOnly
