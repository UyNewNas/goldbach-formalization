import ImbalancedChen.P2HistoricQ80DefectLookup
import ImbalancedChen.P2SavedFloorSemantics
import ImbalancedChen.P2TableActionSoundness
import ImbalancedChen.ActualThirdOriginalBoxMoments

/-!
SOURCE_WRITTEN_UNCOMPILED. Analytic half of the literal saved-Q80 pair cell.
The producer/interval/lookup definitions are imported, not redefined.

The actual source was read, never run:
../tmp/publication-20261010/verification-renewal-v2/data/certify_sharp_184_baseline.py
The old ordinary proof is a maximum of a monotone base and legal concave
chords. Their exact weight is 1/(t*u), not rectangular area. This module
proves their real-integral semantics from the actual continuous factor.

The h-term pointwise comparison uses the actual Wu source improvement h,
with its source delta/domain hypotheses. A saved numerical table entry
still needs its actual-h licence; no such licence is inferred from replay.
No historical sf/log node enclosure, final saved loss, or gain is assumed.
-/

namespace ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness

noncomputable section

open Set MeasureTheory P2SavedFloorSemantics
open OriginalU2CoupledRecurrenceSourceOnly
open Certificates.P2HistoricQ80DefectLookup
open scoped Interval

/-- Real extension of the imported rational source plane. -/
def realPlane (p : Plane) (t u : ℝ) : ℝ :=
  (p.c : ℝ) + (p.b : ℝ) * t + (p.d : ℝ) * u

private theorem signed_edge_bounds (m l r : ℚ) {x : ℝ}
    (hx : x ∈ Icc (l : ℝ) (r : ℝ)) :
    ((m * (if 0 ≤ m then l else r) : ℚ) : ℝ) ≤ (m : ℝ) * x ∧
      (m : ℝ) * x ≤ ((m * (if 0 ≤ m then r else l) : ℚ) : ℝ) := by
  by_cases hm : 0 ≤ m
  · have hmr : (0 : ℝ) ≤ m := by exact_mod_cast hm
    simpa only [if_pos hm, Rat.cast_mul] using
      ⟨mul_le_mul_of_nonneg_left hx.1 hmr, mul_le_mul_of_nonneg_left hx.2 hmr⟩
  · have hmr : (m : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hm)
    simpa only [if_neg hm, Rat.cast_mul] using
      ⟨mul_le_mul_of_nonpos_left hx.2 hmr, mul_le_mul_of_nonpos_left hx.1 hmr⟩

/-- The source's signed rational range encloses every real point of its
closed rectangle, including all affine walls and endpoints. -/
theorem affineRange_real_enclosure (p : Plane) (tl tr ul ur : ℚ)
    {t u : ℝ} (ht : t ∈ Icc (tl : ℝ) (tr : ℝ))
    (hu : u ∈ Icc (ul : ℝ) (ur : ℝ)) :
    (((affineRange p tl tr ul ur).1 : ℚ) : ℝ) ≤ realPlane p t u ∧
      realPlane p t u ≤ (((affineRange p tl tr ul ur).2 : ℚ) : ℝ) := by
  rcases signed_edge_bounds p.b tl tr ht with ⟨hbl, hbr⟩
  rcases signed_edge_bounds p.d ul ur hu with ⟨hdl, hdr⟩
  constructor
  · simpa only [affineRange, realPlane, Rat.cast_add] using
      add_le_add (add_le_add_left hbl (p.c : ℝ)) hdl
  · simpa only [affineRange, realPlane, Rat.cast_add] using
      add_le_add (add_le_add_left hbr (p.c : ℝ)) hdr

theorem planeAccepted_real_minorant (p q : Plane) (tl tr ul ur : ℚ)
    (hp : planeAccepted p q tl tr ul ur)
    {t u : ℝ} (ht : t ∈ Icc (tl : ℝ) (tr : ℝ))
    (hu : u ∈ Icc (ul : ℝ) (ur : ℝ)) : realPlane p t u ≤ realPlane q t u := by
  have hupper := (affineRange_real_enclosure (p.sub q) tl tr ul ur ht hu).2
  have hz : (((affineRange (p.sub q) tl tr ul ur).2 : ℚ) : ℝ) ≤ 0 := by
    exact_mod_cast hp
  have he : realPlane (p.sub q) t u = realPlane p t u - realPlane q t u := by
    unfold realPlane Plane.sub
    push_cast
    ring
  rw [he] at hupper
  linarith

theorem ordinaryPlane₁_real (t u : ℝ) :
    realPlane ordinaryPlane₁ t u = ordinaryResidual t u := by
  norm_num [realPlane, ordinaryPlane₁, ordinaryResidual]
  <;> ring

def realMass (tl tr ul ur : ℝ) : ℝ := Real.log (tr / tl) * Real.log (ur / ul)

def realMoment (p : Plane) (tl tr ul ur : ℝ) : ℝ :=
  (p.c : ℝ) * realMass tl tr ul ur +
    (p.b : ℝ) * (tr - tl) * Real.log (ur / ul) +
    (p.d : ℝ) * (ur - ul) * Real.log (tr / tl)

/-- Semantic integral with the source's logarithmic measure. -/
def weightedIntegral (f : ℝ → ℝ → ℝ) (tl tr ul ur : ℝ) : ℝ :=
  ∫ t in tl..tr, ∫ u in ul..ur, f t u / (t * u)

private theorem reciprocal_integrable {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    IntervalIntegrable (fun x : ℝ => 1 / x) volume l r := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div continuousOn_id
  intro x hx
  rw [Set.uIcc_of_le hlr] at hx
  exact (hl.trans_le hx.1).ne'

private theorem weighted_inner_integrable (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    {t ul ur : ℝ} (ht : 0 < t) (hul : 0 < ul) (hu : ul ≤ ur) :
    IntervalIntegrable (fun u => f t u / (t * u)) volume ul ur := by
  have hn : Continuous (f t) := hf.comp (continuous_const.prodMk continuous_id)
  apply ContinuousOn.intervalIntegrable
  apply hn.continuousOn.div (by fun_prop)
  intro u hu'
  rw [Set.uIcc_of_le hu] at hu'
  exact (mul_pos ht (hul.trans_le hu'.1)).ne'

private theorem weighted_outer_integrable (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    {tl tr ul ur : ℝ} (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    IntervalIntegrable (fun t => ∫ u in ul..ur, f t u / (t * u)) volume tl tr := by
  let ext : ℝ → ℝ → ℝ := fun t u =>
    f (max tl t) (max ul u) / (max tl t * max ul u)
  have hc : Continuous (fun p : ℝ × ℝ => ext p.1 p.2) := by
    have hct : Continuous (fun p : ℝ × ℝ => max tl p.1) :=
      continuous_const.max continuous_fst
    have hcu : Continuous (fun p : ℝ × ℝ => max ul p.2) :=
      continuous_const.max continuous_snd
    exact (hf.comp (hct.prodMk hcu)).div (hct.mul hcu) (fun p =>
      (mul_pos (htl.trans_le (le_max_left _ _))
        (hul.trans_le (le_max_left _ _))).ne')
  have hparam : Continuous (fun t => ∫ u in Icc ul ur, ext t u) :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le ht]
  apply hparam.continuousOn.congr
  intro t ht'
  calc
    (∫ u in ul..ur, f t u / (t * u)) = ∫ u in ul..ur, ext t u := by
      apply intervalIntegral.integral_congr
      intro u hu'
      rw [Set.uIcc_of_le hu] at hu'
      simp only [ext, max_eq_right ht'.1, max_eq_right hu'.1]
    _ = ∫ u in Icc ul ur, ext t u := by
      rw [intervalIntegral.integral_of_le hu, integral_Icc_eq_integral_Ioc]

theorem weightedIntegral_const (v : ℝ) {tl tr ul ur : ℝ}
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hur : 0 < ur) :
    weightedIntegral (fun _ _ => v) tl tr ul ur = v * realMass tl tr ul ur := by
  have halg (t u : ℝ) : v / (t * u) = v * (1 / t) * (1 / u) := by
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  unfold weightedIntegral
  simp_rw [halg]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  rw [integral_one_div_of_pos htl htr, integral_one_div_of_pos hul hur]
  unfold realMass
  ring

/-- Exact three moments used by the historical ordinary chord. -/
theorem weightedIntegral_affine (c b d : ℝ) {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    weightedIntegral (fun t u => c + b * t + d * u) tl tr ul ur =
      c * realMass tl tr ul ur + b * (tr - tl) * Real.log (ur / ul) +
        d * (ur - ul) * Real.log (tr / tl) := by
  have htr := htl.trans_le ht
  have hur := hul.trans_le hu
  have hinner : ∀ t ∈ Icc tl tr,
      (∫ u in ul..ur, (c + b * t + d * u) / (t * u)) =
        (c + b * t) / t * Real.log (ur / ul) + d / t * (ur - ul) := by
    intro t ht'
    have ht0 := htl.trans_le ht'.1
    calc
      (∫ u in ul..ur, (c + b * t + d * u) / (t * u)) =
          ∫ u in ul..ur, ((c + b * t) / t) * (1 / u) + d / t := by
        apply intervalIntegral.integral_congr
        intro u hu'
        rw [Set.uIcc_of_le hu] at hu'
        field_simp [ht0.ne', (hul.trans_le hu'.1).ne']
        <;> ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((reciprocal_integrable hul hu).const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, integral_one_div_of_pos hul hur,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  unfold weightedIntegral
  calc
    (∫ t in tl..tr, ∫ u in ul..ur, (c + b * t + d * u) / (t * u)) =
        ∫ t in tl..tr,
          (c * Real.log (ur / ul) + d * (ur - ul)) * (1 / t) +
            b * Real.log (ur / ul) := by
      apply intervalIntegral.integral_congr
      intro t ht'
      rw [Set.uIcc_of_le ht] at ht'
      rw [hinner t ht']
      field_simp [(htl.trans_le ht'.1).ne']
      <;> ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        ((reciprocal_integrable htl ht).const_mul _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, integral_one_div_of_pos htl htr,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul, realMass]
      ring

theorem weightedIntegral_scale (v : ℝ) (f : ℝ → ℝ → ℝ) (tl tr ul ur : ℝ) :
    weightedIntegral (fun t u => v * f t u) tl tr ul ur =
      v * weightedIntegral f tl tr ul ur := by
  simp only [weightedIntegral, mul_div_assoc, intervalIntegral.integral_const_mul]

private theorem continuous_lower_comparison (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    {tl tr ul ur : ℝ} (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hpoint : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur,
      f t u ≤ (4 / ordinaryA) * actualExtendedThirdLowerFactor (ordinaryResidual t u / ordinaryA)) :
    weightedIntegral f tl tr ul ur ≤ ordinaryCellIntegral tl tr ul ur := by
  have hinner : ∀ t ∈ Icc tl tr,
      (∫ u in ul..ur, f t u / (t * u)) ≤ ∫ u in ul..ur, ordinaryPairKernel t u := by
    intro t ht'
    have ht0 := htl.trans_le ht'.1
    apply intervalIntegral.integral_mono_on hu
      (weighted_inner_integrable f hf ht0 hul hu)
      (ordinaryPairKernel_intervalIntegrable ht0 hul hu)
    intro u hu'
    have hu0 := hul.trans_le hu'.1
    calc
      f t u / (t * u) ≤
          ((4 / ordinaryA) * actualExtendedThirdLowerFactor (ordinaryResidual t u / ordinaryA)) /
            (t * u) := div_le_div_of_nonneg_right (hpoint t ht' u hu') (by positivity)
      _ = ordinaryPairKernel t u := by
        unfold ordinaryPairKernel
        field_simp [ordinaryA_pos.ne', ht0.ne', hu0.ne']
        <;> ring
  exact intervalIntegral.integral_mono_on ht
    (weighted_outer_integrable f hf htl hul ht hu)
    (ordinaryPairKernel_outer_intervalIntegrable htl hul ht hu) hinner

/-- The historical base uses logarithmic mass and the actual smallest
residual query; it is not the area-times-corner estimator of earlier drafts. -/
theorem ordinary_base_real_sound {tl tr ul ur rl fl : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hrl : rl ≤ ordinaryResidual tr ur)
    (hfl : fl ≤ actualExtendedThirdLowerFactor (rl / ordinaryA)) :
    4 * fl * realMass tl tr ul ur / ordinaryA ≤ ordinaryCellIntegral tl tr ul ur := by
  have hs := continuous_lower_comparison (fun _ _ => (4 / ordinaryA) * fl)
    continuous_const htl hul ht hu (by
      intro t ht' u hu'
      have hr := hrl.trans (ordinaryResidual_antitone ht'.2 hu'.2)
      have hp := monotone_actualExtendedThirdLowerFactor
        (div_le_div_of_nonneg_right hr ordinaryA_pos.le)
      exact mul_le_mul_of_nonneg_left (hfl.trans hp) (by positivity))
  rw [weightedIntegral_const _ htl (htl.trans_le ht) hul (hul.trans_le hu)] at hs
  convert hs using 1 <;> ring

def realChord (p : Plane) (pl ph fl fh : ℝ) (t u : ℝ) : ℝ :=
  fl + (realPlane p t u - pl) / (ph - pl) * (fh - fl)

/-- Concavity is applied only above two, with both endpoint queries kept
as lower endpoints. A cap-plane minorant licenses the actual residual. -/
theorem ordinary_chord_pointwise (p : Plane) {pl ph fl fh t u : ℝ}
    (hpl : 2 * ordinaryA ≤ pl) (hspan : pl < ph)
    (hrange : realPlane p t u ∈ Icc pl ph)
    (hminor : realPlane p t u ≤ ordinaryResidual t u)
    (hfl : fl ≤ actualExtendedThirdLowerFactor (pl / ordinaryA))
    (hfh : fh ≤ actualExtendedThirdLowerFactor (ph / ordinaryA)) :
    realChord p pl ph fl fh t u ≤
      actualExtendedThirdLowerFactor (ordinaryResidual t u / ordinaryA) := by
  have ha : 2 ≤ pl / ordinaryA := (le_div_iff₀ ordinaryA_pos).mpr hpl
  have hab : pl / ordinaryA < ph / ordinaryA :=
    (div_lt_div_iff_of_pos_right ordinaryA_pos).mpr hspan
  have harg : realPlane p t u / ordinaryA ∈ Icc (pl / ordinaryA) (ph / ordinaryA) :=
    ⟨div_le_div_of_nonneg_right hrange.1 ordinaryA_pos.le,
      div_le_div_of_nonneg_right hrange.2 ordinaryA_pos.le⟩
  have hc := actual_lower_query_endpoint_chord ha hab harg hfl hfh
  have he : fl + (realPlane p t u / ordinaryA - pl / ordinaryA) /
      (ph / ordinaryA - pl / ordinaryA) * (fh - fl) = realChord p pl ph fl fh t u := by
    unfold realChord
    field_simp [ordinaryA_pos.ne', (sub_pos.mpr hspan).ne']
    <;> ring
  rw [he] at hc
  exact hc.trans (monotone_actualExtendedThirdLowerFactor
    (div_le_div_of_nonneg_right hminor ordinaryA_pos.le))

theorem weightedIntegral_realChord (p : Plane) {tl tr ul ur pl ph fl fh : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) (hspan : pl < ph) :
    weightedIntegral (realChord p pl ph fl fh) tl tr ul ur =
      (fl * (ph * realMass tl tr ul ur - realMoment p tl tr ul ur) +
        fh * (realMoment p tl tr ul ur - pl * realMass tl tr ul ur)) / (ph - pl) := by
  have hf : realChord p pl ph fl fh = fun t u =>
      (fl + ((p.c : ℝ) - pl) / (ph - pl) * (fh - fl)) +
        ((p.b : ℝ) / (ph - pl) * (fh - fl)) * t +
        ((p.d : ℝ) / (ph - pl) * (fh - fl)) * u := by
    funext t u
    unfold realChord realPlane
    ring
  rw [hf, weightedIntegral_affine _ _ _ htl hul ht hu]
  unfold realMoment realMass
  field_simp [(sub_pos.mpr hspan).ne']
  <;> ring

/-- Exact historical concave-chord candidate before outward I80 rounding. -/
theorem ordinary_chord_real_sound (p : Plane) {tl tr ul ur pl ph fl fh : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hpl : 2 * ordinaryA ≤ pl) (hspan : pl < ph)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, realPlane p t u ∈ Icc pl ph)
    (hminor : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, realPlane p t u ≤ ordinaryResidual t u)
    (hfl : fl ≤ actualExtendedThirdLowerFactor (pl / ordinaryA))
    (hfh : fh ≤ actualExtendedThirdLowerFactor (ph / ordinaryA)) :
    (4 / ordinaryA) *
      ((fl * (ph * realMass tl tr ul ur - realMoment p tl tr ul ur) +
        fh * (realMoment p tl tr ul ur - pl * realMass tl tr ul ur)) / (ph - pl)) ≤
      ordinaryCellIntegral tl tr ul ur := by
  have hc : Continuous (fun v : ℝ × ℝ =>
      (4 / ordinaryA) * realChord p pl ph fl fh v.1 v.2) := by
    unfold realChord realPlane
    fun_prop
  have hs := continuous_lower_comparison
    (fun t u => (4 / ordinaryA) * realChord p pl ph fl fh t u) hc htl hul ht hu (by
      intro t ht' u hu'
      exact mul_le_mul_of_nonneg_left
        (ordinary_chord_pointwise p hpl hspan (hrange t ht' u hu')
          (hminor t ht' u hu') hfl hfh) (by positivity))
  rw [weightedIntegral_scale, weightedIntegral_realChord p htl hul ht hu hspan] at hs
  exact hs

/-- The actual Wu source h supplies the defect endpoint comparison. The
denominator uses rh, while the actual point has its own positive residual.
The table endpoint licence is a local supplier, not a target integral bound. -/
theorem actual_defect_endpoint_pointwise {δ rl rh hlow t u : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hlo : 2 * ordinaryA ≤ rl) (hrange : ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) (hh0 : 0 ≤ hlow)
    (hh : hlow ≤ P2TableActionSourceOnly.h δ (rh / ordinaryA)) :
    hlow / rh ≤ P2TableActionSourceOnly.h δ (ordinaryResidual t u / ordinaryA) /
      ordinaryResidual t u := by
  have hl2 : 2 ≤ rl / ordinaryA := (le_div_iff₀ ordinaryA_pos).mpr hlo
  have hlr : rl / ordinaryA ≤ rh / ordinaryA :=
    div_le_div_of_nonneg_right (hrange.1.trans hrange.2) ordinaryA_pos.le
  have harg : ordinaryResidual t u / ordinaryA ∈ Icc (rl / ordinaryA) (rh / ordinaryA) :=
    ⟨div_le_div_of_nonneg_right hrange.1 ordinaryA_pos.le,
      div_le_div_of_nonneg_right hrange.2 ordinaryA_pos.le⟩
  have hactual := P2TableActionSourceOnly.actual_cell_enclosure false hδ hδhi
    hl2 hlr (hhi.trans (by norm_num : (5 : ℝ) ≤ 10)) hh
    (ordinaryResidual t u / ordinaryA) harg
  have hr0 : 0 < ordinaryResidual t u := by
    have := ordinaryA_pos
    linarith [hrange.1]
  exact (div_le_div_of_nonneg_left hh0 hr0 hrange.2).trans
    (div_le_div_of_nonneg_right hactual hr0.le)

def actualDefectKernel (δ t u : ℝ) : ℝ :=
  4 * P2TableActionSourceOnly.h δ (ordinaryResidual t u / ordinaryA) /
    (ordinaryResidual t u * t * u)

/-- Actual-h integral comparison. The two explicit integrability inputs
are about the actual h-composition, not a floor or integral lower bound.
They are deliberately not inferred from an interval-table replay. -/
theorem actual_defect_logmass_sound {δ tl tr ul ur rl rh hlow : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hlo : 2 * ordinaryA ≤ rl)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) (hh0 : 0 ≤ hlow)
    (hh : hlow ≤ P2TableActionSourceOnly.h δ (rh / ordinaryA))
    (hinner : ∀ t ∈ Icc tl tr, IntervalIntegrable (actualDefectKernel δ t) volume ul ur)
    (houter : IntervalIntegrable (fun t => ∫ u in ul..ur, actualDefectKernel δ t u)
      volume tl tr) :
    4 * hlow * realMass tl tr ul ur / rh ≤
      ∫ t in tl..tr, ∫ u in ul..ur, actualDefectKernel δ t u := by
  have hcompare : weightedIntegral (fun _ _ => 4 * hlow / rh) tl tr ul ur ≤
      ∫ t in tl..tr, ∫ u in ul..ur, actualDefectKernel δ t u := by
    apply intervalIntegral.integral_mono_on ht
      (weighted_outer_integrable (fun _ _ => 4 * hlow / rh) continuous_const htl hul ht hu) houter
    intro t ht'
    have ht0 := htl.trans_le ht'.1
    apply intervalIntegral.integral_mono_on hu
      (weighted_inner_integrable (fun _ _ => 4 * hlow / rh) continuous_const ht0 hul hu)
      (hinner t ht')
    intro u hu'
    have hu0 := hul.trans_le hu'.1
    have hp := actual_defect_endpoint_pointwise hδ hδhi hlo (hrange t ht' u hu') hhi hh0 hh
    have hscaled := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ 4 / (t * u) from by positivity)
    calc
      (4 * hlow / rh) / (t * u) = (4 / (t * u)) * (hlow / rh) := by ring
      _ ≤ (4 / (t * u)) *
          (P2TableActionSourceOnly.h δ (ordinaryResidual t u / ordinaryA) / ordinaryResidual t u) := hscaled
      _ = actualDefectKernel δ t u := by
        unfold actualDefectKernel
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  rw [weightedIntegral_const _ htl (htl.trans_le ht) hul (hul.trans_le hu)] at hcompare
  convert hcompare using 1 <;> ring

theorem cast_source_a : (a : ℝ) = ordinaryA := by
  norm_num [a, ordinaryA]

theorem ordinary_integral_nonneg {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    0 ≤ ordinaryCellIntegral tl tr ul ur := by
  apply intervalIntegral.integral_nonneg ht
  intro t ht'
  apply intervalIntegral.integral_nonneg hu
  intro u hu'
  exact ordinaryPairKernel_nonneg (htl.trans_le ht'.1) (hul.trans_le hu'.1)

/-- The literal I80 base, with its actual local sf and logarithm query
licences, now has an actual-integral lower theorem. -/
theorem historical_base_decode_sound (sf logI : ℚ → I80)
    (tl tr ul ur rl : ℚ)
    (htl : (0 : ℝ) < tl) (hul : (0 : ℝ) < ul)
    (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hrl : (rl : ℝ) ≤ ordinaryResidual tr ur)
    (hsf : (sf (rl/a)).Contains (actualExtendedThirdLowerFactor ((rl/a:ℚ):ℝ)))
    (hlogT : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ)))
    (hlogU : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ))) :
    ((ordinaryRectangleBase sf logI tl tr ul ur rl).decodeLo : ℝ) ≤
      ordinaryCellIntegral tl tr ul ur := by
  have htr : (tl : ℝ) ≤ tr := by exact_mod_cast ht
  have hur : (ul : ℝ) ≤ ur := by exact_mod_cast hu
  have hn := ordinaryRectangleBase_decodeLo_le sf logI tl tr ul ur rl
    (actualExtendedThirdLowerFactor ((rl/a:ℚ):ℝ)) hsf hlogT hlogU
  have ha := ordinary_base_real_sound htl hul htr hur hrl
    (le_rfl : actualExtendedThirdLowerFactor ((rl:ℝ)/ordinaryA) ≤
      actualExtendedThirdLowerFactor ((rl:ℝ)/ordinaryA))
  have he : (actualExtendedThirdLowerFactor ((rl/a:ℚ):ℝ) *
      rectangleMassValue tl tr ul ur * 4) / (a:ℝ) =
      4 * actualExtendedThirdLowerFactor ((rl:ℝ)/ordinaryA) *
        realMass tl tr ul ur / ordinaryA := by
    simp only [rectangleMassValue, realMass, Rat.cast_div, cast_source_a]
    ring
  rw [he] at hn
  exact hn.trans ha

/-- The literal I80 chord needs only its primitive positive divisor guard,
logarithm enclosures, and lower sf endpoint licences. The chord's range
and true concavity are proved here; no row floor inequality is assumed. -/
theorem historical_chord_decode_sound (sf logI : ℚ → I80)
    (tl tr ul ur : ℚ) (p : Plane)
    (htl : (0 : ℝ) < tl) (hul : (0 : ℝ) < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hpl : 2*a ≤ (affineRange p tl tr ul ur).1)
    (hne : (affineRange p tl tr ul ur).2 ≠ (affineRange p tl tr ul ur).1)
    (hminor : ∀ t ∈ Icc (tl:ℝ) (tr:ℝ), ∀ u ∈ Icc (ul:ℝ) (ur:ℝ),
      realPlane p t u ≤ ordinaryResidual t u)
    (hfl : ((sf ((affineRange p tl tr ul ur).1/a)).decodeLo : ℝ) ≤
      actualExtendedThirdLowerFactor (((affineRange p tl tr ul ur).1/a:ℚ):ℝ))
    (hfh : ((sf ((affineRange p tl tr ul ur).2/a)).decodeLo : ℝ) ≤
      actualExtendedThirdLowerFactor (((affineRange p tl tr ul ur).2/a:ℚ):ℝ))
    (hlogT : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ)))
    (hlogU : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ)))
    (hden : 0 < (I80.point ((affineRange p tl tr ul ur).2 -
      (affineRange p tl tr ul ur).1)).lo) :
    ((ordinaryRectangleChord sf logI tl tr ul ur p).decodeLo : ℝ) ≤
      ordinaryCellIntegral tl tr ul ur := by
  have htr : (tl : ℝ) ≤ tr := by exact_mod_cast ht
  have hur : (ul : ℝ) ≤ ur := by exact_mod_cast hu
  have hends := affineRange_real_enclosure p tl tr ul ur
    (t := (tl:ℝ)) (u := (ul:ℝ)) ⟨le_rfl,htr⟩ ⟨le_rfl,hur⟩
  have hspan : (((affineRange p tl tr ul ur).1:ℚ):ℝ) <
      (((affineRange p tl tr ul ur).2:ℚ):ℝ) := by
    have hneR : (((affineRange p tl tr ul ur).1:ℚ):ℝ) ≠
        (((affineRange p tl tr ul ur).2:ℚ):ℝ) := by exact_mod_cast hne.symm
    exact lt_of_le_of_ne (hends.1.trans hends.2) hneR
  have hplR : 2 * ordinaryA ≤ (((affineRange p tl tr ul ur).1:ℚ):ℝ) := by
    have hh : (2:ℝ) * (a:ℝ) ≤ (((affineRange p tl tr ul ur).1:ℚ):ℝ) := by
      exact_mod_cast hpl
    simpa only [cast_source_a] using hh
  have hflR : ((sf ((affineRange p tl tr ul ur).1/a)).decodeLo : ℝ) ≤
      actualExtendedThirdLowerFactor ((((affineRange p tl tr ul ur).1:ℚ):ℝ)/ordinaryA) := by
    simpa only [Rat.cast_div, cast_source_a] using hfl
  have hfhR : ((sf ((affineRange p tl tr ul ur).2/a)).decodeLo : ℝ) ≤
      actualExtendedThirdLowerFactor ((((affineRange p tl tr ul ur).2:ℚ):ℝ)/ordinaryA) := by
    simpa only [Rat.cast_div, cast_source_a] using hfh
  have ha := ordinary_chord_real_sound p htl hul htr hur hplR hspan
    (fun t ht' u hu' => affineRange_real_enclosure p tl tr ul ur ht' hu')
    hminor hflR hfhR
  have hn := ordinaryRectangleChord_decodeLo_le sf logI tl tr ul ur p hlogT hlogU hden
  have he : ordinaryRectangleChordValue sf tl tr ul ur p =
      (4 / ordinaryA) *
        ((((sf ((affineRange p tl tr ul ur).1/a)).decodeLo:ℝ) *
          ((((affineRange p tl tr ul ur).2:ℚ):ℝ) * realMass tl tr ul ur -
            realMoment p tl tr ul ur) +
          ((sf ((affineRange p tl tr ul ur).2/a)).decodeLo:ℝ) *
            (realMoment p tl tr ul ur - (((affineRange p tl tr ul ur).1:ℚ):ℝ) *
              realMass tl tr ul ur)) /
          ((((affineRange p tl tr ul ur).2:ℚ):ℝ) - (((affineRange p tl tr ul ur).1:ℚ):ℝ))) := by
    simp only [ordinaryRectangleChordValue, rectangleMassValue,
      rectangleMomentTValue, rectangleMomentUValue, realMass, realMoment,
      Rat.cast_div, Rat.cast_sub, cast_source_a]
    ring
  rw [he] at hn
  exact hn.trans ha

private def decodeInteger (z : ℤ) : ℝ := (((z:ℚ) / Q : ℚ):ℝ)

private theorem decodeInteger_max_le {x y : ℤ} {v : ℝ}
    (hx : decodeInteger x ≤ v) (hy : decodeInteger y ≤ v) :
    decodeInteger (max x y) ≤ v := by
  rcases le_total x y with h | h
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left h] using hx

/-- Actual positive-cell ordinary historical estimator theorem. sf/logI
are the literal imported engine arguments, with their primitive query
licences made explicit. The two source chord guards are preserved.
The conclusion concerns the saved max of proofs, not a sum of chords. -/
theorem savedOrdinaryRectangle_actual_lower (sf logI : ℚ → I80)
    (tl tr ul ur : ℚ) (htl : (0 : ℝ) < tl) (hul : (0 : ℝ) < ul)
    (ht : tl ≤ tr) (hu : ul ≤ ur) (_hHighBranch : (25/128:ℚ) ≤ tl)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q:ℝ)))
    (hlogT : (logI (tr/tl)).Contains (Real.log ((tr/tl:ℚ):ℝ)))
    (hlogU : (logI (ur/ul)).Contains (Real.log ((ur/ul:ℚ):ℝ)))
    (hden₀ : chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur →
      0 < (I80.point ((affineRange ordinaryPlane₀ tl tr ul ur).2 -
        (affineRange ordinaryPlane₀ tl tr ul ur).1)).lo)
    (hden₁ : chordEligible ordinaryPlane₁ ordinaryPlane₀ tl tr ul ur →
      0 < (I80.point ((affineRange ordinaryPlane₁ tl tr ul ur).2 -
        (affineRange ordinaryPlane₁ tl tr ul ur).1)).lo) :
    ((((savedOrdinaryRectangle sf logI tl tr ul ur : ℤ):ℚ) / Q : ℚ):ℝ) ≤
      ordinaryCellIntegral tl tr ul ur := by
  have htr : (tl : ℝ) ≤ tr := by exact_mod_cast ht
  have hur : (ul : ℝ) ≤ ur := by exact_mod_cast hu
  have hrl : (((ordinaryRanges tl tr ul ur).1:ℚ):ℝ) ≤ ordinaryResidual tr ur := by
    have hm : (ordinaryRanges tl tr ul ur).1 ≤ (affineRange ordinaryPlane₁ tl tr ul ur).1 :=
      min_le_right _ _
    have hmR : (((ordinaryRanges tl tr ul ur).1:ℚ):ℝ) ≤
        (((affineRange ordinaryPlane₁ tl tr ul ur).1:ℚ):ℝ) := by exact_mod_cast hm
    have he := (affineRange_real_enclosure ordinaryPlane₁ tl tr ul ur
      (t := (tr:ℝ)) (u := (ur:ℝ)) ⟨htr,le_rfl⟩ ⟨hur,le_rfl⟩).1
    rw [ordinaryPlane₁_real] at he
    exact hmR.trans he
  have hb := historical_base_decode_sound sf logI tl tr ul ur
    (ordinaryRanges tl tr ul ur).1 htl hul ht hu hrl
    (hsf _) hlogT hlogU
  have hc₀ : chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur →
      ((ordinaryRectangleChord sf logI tl tr ul ur ordinaryPlane₀).decodeLo:ℝ) ≤
        ordinaryCellIntegral tl tr ul ur := by
    intro hc
    apply historical_chord_decode_sound sf logI tl tr ul ur ordinaryPlane₀
      htl hul ht hu hc.2.1 hc.2.2
    · intro t ht' u hu'
      have hm := planeAccepted_real_minorant ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur hc.1 ht' hu'
      simpa only [ordinaryPlane₁_real] using hm
    · exact (hsf _).1
    · exact (hsf _).1
    · exact hlogT
    · exact hlogU
    · exact hden₀ hc
  have hc₁ : chordEligible ordinaryPlane₁ ordinaryPlane₀ tl tr ul ur →
      ((ordinaryRectangleChord sf logI tl tr ul ur ordinaryPlane₁).decodeLo:ℝ) ≤
        ordinaryCellIntegral tl tr ul ur := by
    intro hc
    apply historical_chord_decode_sound sf logI tl tr ul ur ordinaryPlane₁
      htl hul ht hu hc.2.1 hc.2.2
    · intro t _ht' u _hu'
      exact (ordinaryPlane₁_real t u).le
    · exact (hsf _).1
    · exact (hsf _).1
    · exact hlogT
    · exact hlogU
    · exact hden₁ hc
  have hbest₀ : decodeInteger
      (if chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur then
        max (ordinaryRectangleBase sf logI tl tr ul ur (ordinaryRanges tl tr ul ur).1).lo
          (ordinaryRectangleChord sf logI tl tr ul ur ordinaryPlane₀).lo
        else (ordinaryRectangleBase sf logI tl tr ul ur (ordinaryRanges tl tr ul ur).1).lo) ≤
      ordinaryCellIntegral tl tr ul ur := by
    by_cases hc : chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur
    · rw [if_pos hc]
      exact decodeInteger_max_le hb (hc₀ hc)
    · rw [if_neg hc]
      exact hb
  have hbest₁ : decodeInteger
      (if chordEligible ordinaryPlane₁ ordinaryPlane₀ tl tr ul ur then
        max
          (if chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur then
            max (ordinaryRectangleBase sf logI tl tr ul ur (ordinaryRanges tl tr ul ur).1).lo
              (ordinaryRectangleChord sf logI tl tr ul ur ordinaryPlane₀).lo
            else (ordinaryRectangleBase sf logI tl tr ul ur (ordinaryRanges tl tr ul ur).1).lo)
          (ordinaryRectangleChord sf logI tl tr ul ur ordinaryPlane₁).lo
        else
          (if chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur then
            max (ordinaryRectangleBase sf logI tl tr ul ur (ordinaryRanges tl tr ul ur).1).lo
              (ordinaryRectangleChord sf logI tl tr ul ur ordinaryPlane₀).lo
            else (ordinaryRectangleBase sf logI tl tr ul ur (ordinaryRanges tl tr ul ur).1).lo)) ≤
      ordinaryCellIntegral tl tr ul ur := by
    by_cases hc : chordEligible ordinaryPlane₁ ordinaryPlane₀ tl tr ul ur
    · rw [if_pos hc]
      exact decodeInteger_max_le hbest₀ (hc₁ hc)
    · rw [if_neg hc]
      exact hbest₀
  exact decodeInteger_max_le
    (by simpa [decodeInteger] using ordinary_integral_nonneg htl hul htr hur) hbest₁

end

end ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness
