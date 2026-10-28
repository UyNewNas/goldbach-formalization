import ImbalancedChen.P2Author512EnhancedDefectLogMass

/-!
SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.

The ordinary half of the actual enhanced author-512 pair_cell. The residual
is the maximum of the three legal tents, not the old high-t affine residual.
Continuous weighted integration, the existing true DDE concavity and the
literal sf/log backends prove each eligible alternative sound. The source
combines alternatives by maximum and adds its separate positive h term.
No source-output fold, mask licence, removed count or final c is assumed.
-/

namespace ImbalancedChen.P2Author512EnhancedOrdinaryIntegral

noncomputable section

open Set MeasureTheory
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricBackendTypeAdapters
open P2HistoricQ80OrdinaryEstimatorSoundness
open P2SavedFloorSemantics
open P2HistoricSavedOrdinaryDefectAssembly
open P2Author512EnhancedPairCell
open P2Author512EnhancedPairCellActualBindings
open P2Author512EnhancedCellGeometry
open P2Author512EnhancedDefectIntegrability
open P2Author512EnhancedDefectLogMass
open scoped Interval

/-- The ordinary contribution uses the same enhanced residual as h. -/
def enhancedOrdinaryKernel (t u : ℝ) : ℝ :=
  4 * actualExtendedThirdLowerFactor (enhancedResidual t u / ordinaryA) /
    (ordinaryA * t * u)

def enhancedOrdinaryIntegral (tl tr ul ur : ℝ) : ℝ :=
  ∫ t in tl..tr, ∫ u in ul..ur, enhancedOrdinaryKernel t u

/-- A continuous numerator divided by the actual positive logarithmic
weight is integrable on every positive slice. -/
private theorem weighted_inner (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    {t ul ur : ℝ} (ht : 0 < t) (hul : 0 < ul) (hu : ul ≤ ur) :
    IntervalIntegrable (fun u => f t u / (t*u)) volume ul ur := by
  have hn : Continuous (f t) := hf.comp (continuous_const.prodMk continuous_id)
  apply ContinuousOn.intervalIntegrable
  apply hn.continuousOn.div (by fun_prop)
  intro u hu'
  rw [Set.uIcc_of_le hu] at hu'
  exact (mul_pos ht (hul.trans_le hu'.1)).ne'

private theorem weighted_outer (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    {tl tr ul ur : ℝ} (htl : 0 < tl) (hul : 0 < ul)
    (ht : tl ≤ tr) (hu : ul ≤ ur) :
    IntervalIntegrable (fun t => ∫ u in ul..ur, f t u / (t*u))
      volume tl tr := by
  let ext : ℝ → ℝ → ℝ := fun t u =>
    f t u / (max tl t * max ul u)
  have hc : Continuous (fun p : ℝ × ℝ => ext p.1 p.2) := by
    exact hf.div
      ((continuous_const.max continuous_fst).mul
        (continuous_const.max continuous_snd))
      (fun p => (mul_pos (htl.trans_le (le_max_left _ _))
        (hul.trans_le (le_max_left _ _))).ne')
  have hparam : Continuous (fun t => ∫ u in Icc ul ur, ext t u) :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le ht]
  apply hparam.continuousOn.congr
  intro t ht'
  calc
    (∫ u in ul..ur, f t u / (t*u)) = ∫ u in ul..ur, ext t u := by
      apply intervalIntegral.integral_congr
      intro u hu'
      rw [Set.uIcc_of_le hu] at hu'
      simp only [ext, max_eq_right ht'.1, max_eq_right hu'.1]
    _ = ∫ u in Icc ul ur, ext t u := by
      rw [intervalIntegral.integral_of_le hu, integral_Icc_eq_integral_Ioc]

private theorem continuous_enhancedNumerator :
    Continuous (fun p : ℝ × ℝ =>
      (4 / ordinaryA) *
        actualExtendedThirdLowerFactor (enhancedResidual p.1 p.2 / ordinaryA)) :=
  continuous_const.mul
    (continuous_actualExtendedThirdLowerFactor.comp
      (continuous_enhancedResidual.div_const ordinaryA))

private theorem enhanced_kernel_as_weight (t u : ℝ) :
    enhancedOrdinaryKernel t u =
      ((4 / ordinaryA) *
        actualExtendedThirdLowerFactor (enhancedResidual t u / ordinaryA)) / (t*u) := by
  simp only [enhancedOrdinaryKernel, div_eq_mul_inv, mul_inv_rev]
  ring

theorem enhanced_ordinary_inner_integrable {t ul ur : ℝ}
    (ht : 0 < t) (hul : 0 < ul) (hu : ul ≤ ur) :
    IntervalIntegrable (enhancedOrdinaryKernel t) volume ul ur := by
  simp_rw [enhanced_kernel_as_weight]
  exact weighted_inner _ continuous_enhancedNumerator ht hul hu

theorem enhanced_ordinary_outer_integrable {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    IntervalIntegrable (fun t => ∫ u in ul..ur, enhancedOrdinaryKernel t u)
      volume tl tr := by
  simp_rw [enhanced_kernel_as_weight]
  exact weighted_outer _ continuous_enhancedNumerator htl hul ht hu

theorem enhanced_ordinary_integral_nonneg {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    0 ≤ enhancedOrdinaryIntegral tl tr ul ur := by
  apply intervalIntegral.integral_nonneg ht
  intro t ht'
  apply intervalIntegral.integral_nonneg hu
  intro u hu'
  have ht0 : 0 < t := htl.trans_le ht'.1
  have hu0 : 0 < u := hul.trans_le hu'.1
  change 0 ≤ 4 * actualExtendedThirdLowerFactor
    (enhancedResidual t u / ordinaryA) / (ordinaryA*t*u)
  exact div_nonneg
    (mul_nonneg (by norm_num) (actualExtendedThirdLowerFactor_nonneg _))
    (mul_nonneg (mul_nonneg ordinaryA_pos.le ht0.le) hu0.le)

private theorem enhanced_continuous_comparison (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    {tl tr ul ur : ℝ} (htl : 0 < tl) (hul : 0 < ul)
    (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hpoint : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur,
      f t u ≤ (4 / ordinaryA) *
        actualExtendedThirdLowerFactor (enhancedResidual t u / ordinaryA)) :
    weightedIntegral f tl tr ul ur ≤ enhancedOrdinaryIntegral tl tr ul ur := by
  apply intervalIntegral.integral_mono_on ht
    (weighted_outer f hf htl hul ht hu)
    (enhanced_ordinary_outer_integrable htl hul ht hu)
  intro t ht'
  have ht0 : 0 < t := htl.trans_le ht'.1
  apply intervalIntegral.integral_mono_on hu
    (weighted_inner f hf ht0 hul hu)
    (enhanced_ordinary_inner_integrable ht0 hul hu)
  intro u hu'
  rw [enhanced_kernel_as_weight]
  exact div_le_div_of_nonneg_right (hpoint t ht' u hu')
    (mul_nonneg ht0.le (hul.trans_le hu'.1).le)

/-- The real base proxy uses the lower endpoint of the *enhanced* residual
range; no old ordinary-residual corner is substituted. -/
theorem enhanced_base_real_sound {tl tr ul ur rl fl : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hrl : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, rl ≤ enhancedResidual t u)
    (hfl : fl ≤ actualExtendedThirdLowerFactor (rl / ordinaryA)) :
    4*fl*realMass tl tr ul ur / ordinaryA ≤
      enhancedOrdinaryIntegral tl tr ul ur := by
  have hs := enhanced_continuous_comparison (fun _ _ => (4/ordinaryA)*fl)
    continuous_const htl hul ht hu (by
      intro t ht' u hu'
      exact mul_le_mul_of_nonneg_left
        (hfl.trans (monotone_actualExtendedThirdLowerFactor
          (div_le_div_of_nonneg_right (hrl t ht' u hu') ordinaryA_pos.le)))
        (by positivity))
  rw [weightedIntegral_const _ htl (htl.trans_le ht) hul (hul.trans_le hu)] at hs
  convert hs using 1 <;> ring

/-- Actual DDE concavity above two, now against the three-tent residual. -/
theorem enhanced_chord_pointwise (p : Plane) {pl ph fl fh t u : ℝ}
    (hpl : 2*ordinaryA ≤ pl) (hspan : pl < ph)
    (hrange : realPlane p t u ∈ Icc pl ph)
    (hminor : realPlane p t u ≤ enhancedResidual t u)
    (hfl : fl ≤ actualExtendedThirdLowerFactor (pl/ordinaryA))
    (hfh : fh ≤ actualExtendedThirdLowerFactor (ph/ordinaryA)) :
    realChord p pl ph fl fh t u ≤
      actualExtendedThirdLowerFactor (enhancedResidual t u/ordinaryA) := by
  have ha : 2 ≤ pl/ordinaryA := (le_div_iff₀ ordinaryA_pos).mpr hpl
  have hab : pl/ordinaryA < ph/ordinaryA :=
    (div_lt_div_iff_of_pos_right ordinaryA_pos).mpr hspan
  have harg : realPlane p t u/ordinaryA ∈ Icc (pl/ordinaryA) (ph/ordinaryA) :=
    ⟨div_le_div_of_nonneg_right hrange.1 ordinaryA_pos.le,
      div_le_div_of_nonneg_right hrange.2 ordinaryA_pos.le⟩
  have hc := OriginalU2CoupledRecurrenceSourceOnly.actual_lower_query_endpoint_chord
    ha hab harg hfl hfh
  have he : fl + (realPlane p t u/ordinaryA - pl/ordinaryA) /
      (ph/ordinaryA-pl/ordinaryA)*(fh-fl) = realChord p pl ph fl fh t u := by
    unfold realChord
    field_simp [ordinaryA_pos.ne', (sub_pos.mpr hspan).ne'] <;> ring
  rw [he] at hc
  exact hc.trans (monotone_actualExtendedThirdLowerFactor
    (div_le_div_of_nonneg_right hminor ordinaryA_pos.le))

theorem enhanced_chord_real_sound (p : Plane) {tl tr ul ur pl ph fl fh : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hpl : 2*ordinaryA ≤ pl) (hspan : pl < ph)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, realPlane p t u ∈ Icc pl ph)
    (hminor : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur,
      realPlane p t u ≤ enhancedResidual t u)
    (hfl : fl ≤ actualExtendedThirdLowerFactor (pl/ordinaryA))
    (hfh : fh ≤ actualExtendedThirdLowerFactor (ph/ordinaryA)) :
    (4/ordinaryA) *
      ((fl*(ph*realMass tl tr ul ur-realMoment p tl tr ul ur) +
        fh*(realMoment p tl tr ul ur-pl*realMass tl tr ul ur))/(ph-pl)) ≤
      enhancedOrdinaryIntegral tl tr ul ur := by
  have hc : Continuous (fun v : ℝ × ℝ =>
      (4/ordinaryA)*realChord p pl ph fl fh v.1 v.2) := by
    unfold realChord realPlane
    fun_prop
  have hs := enhanced_continuous_comparison
    (fun t u => (4/ordinaryA)*realChord p pl ph fl fh t u)
    hc htl hul ht hu (by
      intro t ht' u hu'
      exact mul_le_mul_of_nonneg_left
        (enhanced_chord_pointwise p hpl hspan (hrange t ht' u hu')
          (hminor t ht' u hu') hfl hfh) (by positivity))
  rw [weightedIntegral_scale, weightedIntegral_realChord p htl hul ht hu hspan] at hs
  exact hs

/-- All five actual eligible planes lie below the same residual. In
particular the two enhanced planes are not added to the two base planes. -/
theorem eligible_alternative_minorant (b : PairBox) (henh : b.enhance = true)
    (pc : Plane × Option Plane) (hmem : pc ∈ alternatives b)
    (hactive : eligible b pc.1 pc.2 = true)
    {t u : ℝ} (ht : t ∈ Icc (b.tl:ℝ) b.tr)
    (hu : u ∈ Icc (b.ul:ℝ) b.ur) :
    realPlane pc.1 t u ≤ enhancedResidual t u := by
  simp only [alternatives, henh, if_true, List.mem_append,
    List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with ((h | h) | (h | h | h))
  · subst pc
    exact active_base_plane₀_below_enhanced b hactive ht hu
  · subst pc
    exact active_base_plane₁_below_enhanced b hactive ht hu
  · subst pc
    exact active_enhanced_plane₀_below_residual b hactive ht hu
  · subst pc
    exact active_enhanced_plane₁_below_residual b hactive ht hu
  · subst pc
    exact singleton_below_residual t u

/-- Real integral semantics of the actual directed base integer. -/
theorem enhanced_base_Q80_lower (b : PairBox)
    (henh : b.enhance = true) (hdiag : b.diagonal = false)
    (htl : 0 < b.tl) (hul : 0 < b.ul) (ht : b.tl ≤ b.tr) (hu : b.ul ≤ b.ur) :
    (((baseLower actualSf actualLog b:ℚ)/Q:ℚ):ℝ) ≤
      enhancedOrdinaryIntegral b.tl b.tr b.ul b.ur := by
  have htr : (b.tl:ℝ) ≤ b.tr := by exact_mod_cast ht
  have hur : (b.ul:ℝ) ≤ b.ur := by exact_mod_cast hu
  have hb := enhanced_base_real_sound
    (show (0:ℝ)<b.tl by exact_mod_cast htl)
    (show (0:ℝ)<b.ul by exact_mod_cast hul) htr hur
    (fun t ht' u hu' => (enhanced_residual_in_pairRanges b henh ht' hu').1)
    (le_rfl : actualExtendedThirdLowerFactor ((pairRanges b).1/ordinaryA) ≤ _)
  have hn := actual_base_directed b hdiag htl hul ht hu
  have he : (actualExtendedThirdLowerFactor (((pairRanges b).1/a:ℚ):ℝ) *
      rectangleMassValue b.tl b.tr b.ul b.ur*4)/(a:ℝ) =
      4*actualExtendedThirdLowerFactor (((pairRanges b).1:ℝ)/ordinaryA)*
        realMass b.tl b.tr b.ul b.ur/ordinaryA := by
    simp only [rectangleMassValue, realMass, Rat.cast_div, cast_source_a]
    ring
  rw [he] at hn
  exact hn.trans hb

/-- Real integral semantics of an actual eligible chord integer. Its
only numerical guard is the positive directed Q80 denominator. -/
theorem enhanced_chord_Q80_lower (b : PairBox)
    (henh : b.enhance = true) (hdiag : b.diagonal = false)
    (htl : 0 < b.tl) (hul : 0 < b.ul) (ht : b.tl ≤ b.tr) (hu : b.ul ≤ b.ur)
    (pc : Plane × Option Plane) (hmem : pc ∈ alternatives b)
    (hactive : eligible b pc.1 pc.2 = true)
    (hden : 0 < (I80.point
      ((affineRange pc.1 b.tl b.tr b.ul b.ur).2 -
        (affineRange pc.1 b.tl b.tr b.ul b.ur).1)).lo) :
    (((chordLower actualSf actualLog b pc.1:ℚ)/Q:ℚ):ℝ) ≤
      enhancedOrdinaryIntegral b.tl b.tr b.ul b.ur := by
  let p := pc.1
  let pl := (affineRange p b.tl b.tr b.ul b.ur).1
  let ph := (affineRange p b.tl b.tr b.ul b.ur).2
  have hg : 2*a ≤ pl ∧ ph ≠ pl := by
    exact of_decide_eq_true (Bool.and_eq_true.mp hactive).1
  have htr : (b.tl:ℝ) ≤ b.tr := by exact_mod_cast ht
  have hur : (b.ul:ℝ) ≤ b.ur := by exact_mod_cast hu
  have hr := affineRange_real_enclosure p b.tl b.tr b.ul b.ur
    (t := (b.tl:ℝ)) (u := (b.ul:ℝ)) ⟨le_rfl,htr⟩ ⟨le_rfl,hur⟩
  have hspan : (pl:ℝ) < (ph:ℝ) := by
    have hne : (pl:ℝ) ≠ (ph:ℝ) := by exact_mod_cast hg.2.symm
    exact lt_of_le_of_ne (hr.1.trans hr.2) hne
  have hpl : 2*ordinaryA ≤ (pl:ℝ) := by
    have hz : (2:ℝ)*(a:ℝ) ≤ (pl:ℝ) := by exact_mod_cast hg.1
    simpa only [cast_source_a] using hz
  have hfl : ((sourceSf (pl/a)).decodeLo:ℝ) ≤
      actualExtendedThirdLowerFactor ((pl:ℝ)/ordinaryA) := by
    simpa only [Rat.cast_div,cast_source_a] using sourceSf_decodeLo_le_actual (pl/a)
  have hfh : ((sourceSf (ph/a)).decodeLo:ℝ) ≤
      actualExtendedThirdLowerFactor ((ph:ℝ)/ordinaryA) := by
    simpa only [Rat.cast_div,cast_source_a] using sourceSf_decodeLo_le_actual (ph/a)
  have ha := enhanced_chord_real_sound p
    (show (0:ℝ)<b.tl by exact_mod_cast htl)
    (show (0:ℝ)<b.ul by exact_mod_cast hul) htr hur hpl hspan
    (fun t ht' u hu' => affineRange_real_enclosure p b.tl b.tr b.ul b.ur ht' hu')
    (fun t ht' u hu' => eligible_alternative_minorant b henh pc hmem hactive ht' hu')
    hfl hfh
  have hn := actual_chord_directed b p hdiag htl hul ht hu hden
  have he : ordinaryRectangleChordValue sourceSf b.tl b.tr b.ul b.ur p =
      (4/ordinaryA) *
        ((((sourceSf (pl/a)).decodeLo:ℝ)*
          ((ph:ℝ)*realMass b.tl b.tr b.ul b.ur-realMoment p b.tl b.tr b.ul b.ur) +
          ((sourceSf (ph/a)).decodeLo:ℝ)*
          (realMoment p b.tl b.tr b.ul b.ur-(pl:ℝ)*realMass b.tl b.tr b.ul b.ur)) /
          ((ph:ℝ)-(pl:ℝ))) := by
    simp only [ordinaryRectangleChordValue, rectangleMassValue,
      rectangleMomentTValue,rectangleMomentUValue,realMass,realMoment,
      Rat.cast_div,Rat.cast_sub,cast_source_a,pl,ph]
    ring
  rw [he] at hn
  exact hn.trans ha

def decodeSaved (z : ℤ) : ℝ := (((z:ℚ)/Q:ℚ):ℝ)

private theorem decode_max_le {x y : ℤ} {v : ℝ}
    (hx : decodeSaved x ≤ v) (hy : decodeSaved y ≤ v) :
    decodeSaved (max x y) ≤ v := by
  rcases le_total x y with h | h
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left h] using hx

/-- Pure finite max-fold induction. It is used with the five proved
actual chord comparisons above, never with assumed target cell bounds. -/
private theorem fold_alternatives_lower (sf logI : ℚ → I80) (b : PairBox)
    (L : List (Plane × Option Plane)) (v : ℝ)
    (hc : ∀ pc ∈ L, eligible b pc.1 pc.2 = true →
      decodeSaved (chordLower sf logI b pc.1) ≤ v)
    (z : ℤ) (hz : decodeSaved z ≤ v) :
    decodeSaved (L.foldl (fun best pc => if eligible b pc.1 pc.2 then
      max best (chordLower sf logI b pc.1) else best) z) ≤ v := by
  induction L generalizing z with
  | nil => simpa using hz
  | cons pc L ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro pc' hp' he'
      exact hc pc' (List.mem_cons_of_mem pc hp') he'
    · by_cases he : eligible b pc.1 pc.2 = true
      · simp only [he, if_true]
        exact decode_max_le hz (hc pc (List.mem_cons_self) he)
      · have he0 : eligible b pc.1 pc.2 = false := Bool.eq_false_iff.mpr he
        simp only [he0, Bool.false_eq_true, if_false]
        exact hz

/-- The complete ordinary max-of-eligible-alternatives on one enhanced
rectangle is below its true integral. No target integral hypothesis occurs. -/
theorem enhanced_box_ordinary_Q80_lower (b : PairBox)
    (henh : b.enhance = true) (hdiag : b.diagonal = false)
    (htl : 0 < b.tl) (hul : 0 < b.ul) (ht : b.tl ≤ b.tr) (hu : b.ul ≤ b.ur)
    (hden : ∀ pc ∈ alternatives b, eligible b pc.1 pc.2 = true →
      0 < (I80.point ((affineRange pc.1 b.tl b.tr b.ul b.ur).2 -
        (affineRange pc.1 b.tl b.tr b.ul b.ur).1)).lo) :
    (((ordinaryLower actualSf actualLog b:ℚ)/Q:ℚ):ℝ) ≤
      enhancedOrdinaryIntegral b.tl b.tr b.ul b.ur := by
  have hb := enhanced_base_Q80_lower b henh hdiag htl hul ht hu
  have hf := fold_alternatives_lower actualSf actualLog b (alternatives b)
    (enhancedOrdinaryIntegral b.tl b.tr b.ul b.ur)
    (fun pc hp he => enhanced_chord_Q80_lower b henh hdiag htl hul ht hu
      pc hp he (hden pc hp he)) (baseLower actualSf actualLog b) hb
  have hz : decodeSaved 0 ≤ enhancedOrdinaryIntegral b.tl b.tr b.ul b.ur := by
    simpa [decodeSaved] using enhanced_ordinary_integral_nonneg
      (show (0:ℝ)<b.tl by exact_mod_cast htl)
      (show (0:ℝ)<b.ul by exact_mod_cast hul)
      (show (b.tl:ℝ)≤b.tr by exact_mod_cast ht)
      (show (b.ul:ℝ)≤b.ur by exact_mod_cast hu)
  exact decode_max_le hz hf

/-- Complete actual pair_cell lower comparison on one enhanced rectangle.
The ordinary alternatives remain a maximum; only the independently positive
h contribution is added. h-bank endpoint licences are retained explicitly.
This statement does not identify any stored selected-L6 numerator or fold. -/
theorem enhanced_box_pairCell_Q80_lower {δ : ℝ} (b : PairBox)
    (henh : b.enhance = true) (hdiag : b.diagonal = false)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hbank : BankEndpointLicences δ)
    (htl : 0 < b.tl) (hul : 0 < b.ul) (ht : b.tl ≤ b.tr) (hu : b.ul ≤ b.ur)
    (hden : ∀ pc ∈ alternatives b, eligible b pc.1 pc.2 = true →
      0 < (I80.point ((affineRange pc.1 b.tl b.tr b.ul b.ur).2 -
        (affineRange pc.1 b.tl b.tr b.ul b.ur).1)).lo)
    (hrl : 0 < ((pairRanges b).1 : ℝ))
    (hhi : (((pairRanges b).2/a:ℚ):ℝ) ≤ 5)
    (horder : (I80.ofEnclosure
      ⟨(pairRanges b).1/a,(pairRanges b).2/a⟩).lo ≤
      (I80.ofEnclosure ⟨(pairRanges b).1/a,(pairRanges b).2/a⟩).hi)
    (hupper : (((pairRanges b).2/a:ℚ):ℝ) ≤
      ((I80.ofEnclosure
        ⟨(pairRanges b).1/a,(pairRanges b).2/a⟩).decodeHi:ℝ))
    (hrhRound : 0 < (I80.point (pairRanges b).2).lo) :
    (((pairCellQ80 actualSf actualLog b:ℚ)/Q:ℚ):ℝ) ≤
      enhancedOrdinaryIntegral b.tl b.tr b.ul b.ur +
        enhancedDefectIntegral δ b.tl b.tr b.ul b.ur := by
  have ho := enhanced_box_ordinary_Q80_lower b henh hdiag htl hul ht hu hden
  have hd := enhanced_box_defect_Q80_lower b henh hdiag hδ hδhi hbank
    htl hul ht hu hrl hhi horder hupper hrhRound
  have hs := add_le_add ho hd
  convert hs using 1
  simp only [pairCellQ80,Int.cast_add,add_div,Rat.cast_add]

end

end ImbalancedChen.P2Author512EnhancedOrdinaryIntegral
