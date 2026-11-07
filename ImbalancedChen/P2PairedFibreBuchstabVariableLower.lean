import ImbalancedChen.P2HistoricalFibreBinding
import ImbalancedChen.Certificates.PairedV2FullBuchstab
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# P2: literal paired iterated integrals of the actual Buchstab gain

SOURCE ONLY, uncompiled.  Future installation maps the companion candidate
`20261024z-P2/P2HistoricalFibreBinding.lean` to
`ImbalancedChen/P2HistoricalFibreBinding.lean`; the first import is that
explicit future dependency, not a claim that the draft is installed.

The existing FullBuchstab module proves an open-fibre pointwise comparison.
Here the closed integration supports, including degenerate inner slices,
are checked and the comparison is integrated through all four actual
intervals.  Global continuous extensions are used only to supply genuine
integrability of each successive integral; on every integration point the
extension equals the literal original kernel.  No integrability, parent
ownership, or final gain inequality is assumed.

`row_gainIntegral_lower_of_local_barrier` also accepts any rational local
lower barrier for the actual pinned Buchstab function.  Its hypothesis is
a pointwise analytic certificate, not an assumed integral gain.  The proved
11/20 barrier supplies the unconditional specialization for every one of
the 17572 existing FullMask rows.  This analytic comparison does not prove
the missing historical five-to-four-coordinate arithmetic-parent identity.
-/

namespace ImbalancedChen.Certificates.P2PairedFibreBuchstabVariableLower

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators
open P2HistoricalFibreBinding

abbrev Quad := ((ℝ × ℝ) × ℝ) × ℝ

/-- Four actual nested intervals, with the original triangular last fibre. -/
def fourfold (F : Quad → ℝ) (a tl tr ul ur Z : ℝ) : ℝ :=
  ∫ t in tl..tr, ∫ u in ul..ur, ∫ z in a..Z, ∫ w in a..z,
    F (((t, u), z), w)

private theorem continuous_integral_w (F : Quad → ℝ) (hF : Continuous F) (a : ℝ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => ∫ w in a..p.2, F (p, w)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun p w => F (p, w)) hF continuous_snd

private theorem continuous_integral_zw (F : Quad → ℝ) (hF : Continuous F)
    (a Z : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ z in a..Z, ∫ w in a..z, F ((p, z), w)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun p z => ∫ w in a..z, F ((p, z), w))
    (continuous_integral_w F hF a) a Z

private theorem continuous_integral_uzw (F : Quad → ℝ) (hF : Continuous F)
    (a ul ur Z : ℝ) :
    Continuous (fun t : ℝ => ∫ u in ul..ur, ∫ z in a..Z,
      ∫ w in a..z, F (((t, u), z), w)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t u => ∫ z in a..Z, ∫ w in a..z, F (((t, u), z), w))
    (continuous_integral_zw F hF a Z) ul ur

/-- Genuine fourfold monotonicity.  Successive integrability follows from
continuity, including the variable upper endpoint of the inner integral. -/
theorem fourfold_mono {F G : Quad → ℝ} (hF : Continuous F) (hG : Continuous G)
    {a tl tr ul ur Z : ℝ} (ht : tl ≤ tr) (hu : ul ≤ ur) (hZ : a ≤ Z)
    (hpoint : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ∀ z ∈ Icc a Z,
      ∀ w ∈ Icc a z, F (((t, u), z), w) ≤ G (((t, u), z), w)) :
    fourfold F a tl tr ul ur Z ≤ fourfold G a tl tr ul ur Z := by
  unfold fourfold
  apply intervalIntegral.integral_mono_on ht
    ((continuous_integral_uzw F hF a ul ur Z).intervalIntegrable tl tr)
    ((continuous_integral_uzw G hG a ul ur Z).intervalIntegrable tl tr)
  intro t ht'
  apply intervalIntegral.integral_mono_on hu
    (((continuous_integral_zw F hF a Z).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable ul ur)
    (((continuous_integral_zw G hG a Z).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable ul ur)
  intro u hu'
  apply intervalIntegral.integral_mono_on hZ
    (((continuous_integral_w F hF a).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable a Z)
    (((continuous_integral_w G hG a).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable a Z)
  intro z hz'
  apply intervalIntegral.integral_mono_on hz'.1
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a z)
    ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a z)
  intro w hw'
  exact hpoint t ht' u hu' z hz' w hw'

namespace FullMask

open PairedV2
open PairedV2.FullMask

/-- Exactly the closed nested supports used by the iterated integrals. -/
def closedSupport (r : Row) (t u z w : ℝ) : Prop :=
  t ∈ Icc (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ) ∧
  u ∈ Icc (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ) ∧
  z ∈ Icc (a : ℝ) (cutoff r : ℝ) ∧ w ∈ Icc (a : ℝ) z

/-- All four original coordinates stay above the same positive cutoff,
also on the outer endpoints and the inner diagonal. -/
theorem closedSupport_lower_bounds (r : Row) {t u z w : ℝ}
    (hs : closedSupport r t u z w) :
    (a : ℝ) ≤ t ∧ (a : ℝ) ≤ u ∧ (a : ℝ) ≤ z ∧ (a : ℝ) ≤ w := by
  obtain ⟨haZ, hzul, _huu, _hurh, hhtl, _htu, _htrd, _hcut⟩ := row_endpoint_bounds r
  have haZR : (a : ℝ) < (cutoff r : ℝ) := by exact_mod_cast haZ
  have hzulR : (cutoff r : ℝ) ≤ (uLower (indices r).2 : ℝ) := by exact_mod_cast hzul
  have hhtlR : (h : ℝ) < (tLower (indices r).1 : ℝ) := by exact_mod_cast hhtl
  have hah : (a : ℝ) < (h : ℝ) := by norm_num [a, h]
  exact ⟨(hah.trans hhtlR).le.trans hs.1.1,
    (haZR.le.trans hzulR).trans hs.2.1.1, hs.2.2.1.1, hs.2.2.2.1⟩

/-- The complete integration support obeys the actual Buchstab cutoff,
including its boundary; there is no endpoint limit assumption. -/
theorem closedSupport_argument (r : Row) {t u z w : ℝ}
    (hs : closedSupport r t u z w) :
    (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z := by
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have hz : 0 < z := ha.trans_le hs.2.2.1.1
  have hc := (row_endpoint_bounds r).2.2.2.2.2.2.2
  have hcR : (13 / 3 : ℝ) * (cutoff r : ℝ) ≤
      1 - (tUpper (indices r).1 : ℝ) - (uUpper (indices r).2 : ℝ) := by
    exact_mod_cast hc
  apply (le_div_iff₀ hz).mpr
  rcases hs with ⟨⟨htl, htr⟩, ⟨hul, hur⟩, ⟨haz, hzZ⟩, ⟨haw, hwz⟩⟩
  linarith

/-- The same literal Chen-quarter weight used by the certificate is
nonnegative everywhere on the closed integration support. -/
theorem closedSupport_weight_nonneg (r : Row) {t u z w : ℝ}
    (hs : closedSupport r t u z w) :
    0 ≤ pairedChenQuarterWeight (K : ℝ) t u z w := by
  obtain ⟨ht, hu, hz, hw⟩ := closedSupport_lower_bounds r hs
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have ht' : 0 < t := ha.trans_le ht
  have hu' : 0 < u := ha.trans_le hu
  have hz' : 0 < z := ha.trans_le hz
  have hw' : 0 < w := ha.trans_le hw
  unfold pairedChenQuarterWeight
  have hK : (0 : ℝ) < (K : ℝ) := by norm_num [K]
  positivity

private def clip (x : ℝ) : ℝ := max (a : ℝ) x

private theorem continuous_clip : Continuous clip := continuous_const.max continuous_id

private theorem clip_ne_zero (x : ℝ) : clip x ≠ 0 := by
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  exact (ha.trans_le (le_max_left (a : ℝ) x)).ne'

private def safeWeight (p : Quad) : ℝ :=
  pairedChenQuarterWeight (K : ℝ)
    (clip p.1.1.1) (clip p.1.1.2) (clip p.1.2) (clip p.2)

private def safeGain (p : Quad) : ℝ :=
  pairedSemanticBuchstabGain
    (clip p.1.1.1) (clip p.1.1.2) (clip p.1.2) (clip p.2)

private theorem continuous_safeWeight : Continuous safeWeight := by
  have ht : Continuous (fun p : Quad => clip p.1.1.1) := continuous_clip.comp (by fun_prop)
  have hu : Continuous (fun p : Quad => clip p.1.1.2) := continuous_clip.comp (by fun_prop)
  have hz : Continuous (fun p : Quad => clip p.1.2) := continuous_clip.comp (by fun_prop)
  have hw : Continuous (fun p : Quad => clip p.2) := continuous_clip.comp (by fun_prop)
  exact continuous_const.div (((ht.mul hu).mul (hz.pow 2)).mul hw)
    (fun p => mul_ne_zero (mul_ne_zero (mul_ne_zero (clip_ne_zero _) (clip_ne_zero _))
      (pow_ne_zero 2 (clip_ne_zero _))) (clip_ne_zero _))

private theorem continuous_safeGain : Continuous safeGain := by
  have ht : Continuous (fun p : Quad => clip p.1.1.1) := continuous_clip.comp (by fun_prop)
  have hu : Continuous (fun p : Quad => clip p.1.1.2) := continuous_clip.comp (by fun_prop)
  have hz : Continuous (fun p : Quad => clip p.1.2) := continuous_clip.comp (by fun_prop)
  have hw : Continuous (fun p : Quad => clip p.2) := continuous_clip.comp (by fun_prop)
  exact (LiLiuPrereqBuchstab.continuous_buchstab.comp
    (((((continuous_const.sub ht).sub hu).sub hz).sub hw).div hz
      (fun p => clip_ne_zero p.1.2))).sub continuous_const

private theorem safeWeight_eq (r : Row) {t u z w : ℝ}
    (hs : closedSupport r t u z w) :
    safeWeight (((t, u), z), w) = pairedChenQuarterWeight (K : ℝ) t u z w := by
  obtain ⟨ht, hu, hz, hw⟩ := closedSupport_lower_bounds r hs
  simp only [safeWeight, clip, max_eq_right ht, max_eq_right hu,
    max_eq_right hz, max_eq_right hw]

private theorem safeGain_eq (r : Row) {t u z w : ℝ}
    (hs : closedSupport r t u z w) :
    safeGain (((t, u), z), w) = pairedSemanticBuchstabGain t u z w := by
  obtain ⟨ht, hu, hz, hw⟩ := closedSupport_lower_bounds r hs
  simp only [safeGain, clip, max_eq_right ht, max_eq_right hu,
    max_eq_right hz, max_eq_right hw]

/-- Literal actual semantic gain integral for an adopted row. -/
def rowGainIntegral (r : Row) : ℝ :=
  ∫ t in (tLower (indices r).1 : ℝ)..(tUpper (indices r).1 : ℝ),
  ∫ u in (uLower (indices r).2 : ℝ)..(uUpper (indices r).2 : ℝ),
  ∫ z in (a : ℝ)..(cutoff r : ℝ), ∫ w in (a : ℝ)..z,
    pairedChenQuarterWeight (K : ℝ) t u z w * pairedSemanticBuchstabGain t u z w

private theorem fourfold_safeGain_eq (r : Row) :
    fourfold (fun p => safeWeight p * safeGain p) (a : ℝ)
      (tLower (indices r).1) (tUpper (indices r).1)
      (uLower (indices r).2) (uUpper (indices r).2) (cutoff r) = rowGainIntegral r := by
  unfold fourfold rowGainIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro u hu
  apply intervalIntegral.integral_congr
  intro z hz
  apply intervalIntegral.integral_congr
  intro w hw
  have he := row_endpoint_bounds r
  have htt : (tLower (indices r).1 : ℝ) ≤ (tUpper (indices r).1 : ℝ) := by
    exact_mod_cast he.2.2.2.2.2.1.le
  have huu : (uLower (indices r).2 : ℝ) ≤ (uUpper (indices r).2 : ℝ) := by
    exact_mod_cast he.2.2.1.le
  have hZZ : (a : ℝ) ≤ (cutoff r : ℝ) := by exact_mod_cast he.1.le
  rw [uIcc_of_le htt] at ht
  rw [uIcc_of_le huu] at hu
  rw [uIcc_of_le hZZ] at hz
  rw [uIcc_of_le hz.1] at hw
  rw [safeWeight_eq r ⟨ht, hu, hz, hw⟩, safeGain_eq r ⟨ht, hu, hz, hw⟩]

private theorem fourfold_safeConstant_eq (r : Row) (c : ℝ) :
    fourfold (fun p => safeWeight p * c) (a : ℝ)
      (tLower (indices r).1) (tUpper (indices r).1)
      (uLower (indices r).2) (uUpper (indices r).2) (cutoff r) =
      20 * c * pairedLocalIntegral (K : ℝ) a
        (tLower (indices r).1) (tUpper (indices r).1)
        (uLower (indices r).2) (uUpper (indices r).2) (cutoff r) := by
  have he := row_endpoint_bounds r
  have htt : (tLower (indices r).1 : ℝ) ≤ (tUpper (indices r).1 : ℝ) := by
    exact_mod_cast he.2.2.2.2.2.1.le
  have huu : (uLower (indices r).2 : ℝ) ≤ (uUpper (indices r).2 : ℝ) := by
    exact_mod_cast he.2.2.1.le
  have hZZ : (a : ℝ) ≤ (cutoff r : ℝ) := by exact_mod_cast he.1.le
  have hpoint : ∀ t ∈ Icc (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ),
      ∀ u ∈ Icc (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ),
      ∀ z ∈ Icc (a : ℝ) (cutoff r : ℝ), ∀ w ∈ Icc (a : ℝ) z,
      safeWeight (((t, u), z), w) * c =
        ((20 * c) * ((K : ℝ) / 80)) * pairedFibreKernel t u z w := by
    intro t ht u hu z hz w hw
    rw [safeWeight_eq r ⟨ht, hu, hz, hw⟩, pairedFibreKernel_eq]
    unfold pairedChenQuarterWeight
    ring
  unfold fourfold
  have hrewrite :
      (∫ t in (tLower (indices r).1 : ℝ)..(tUpper (indices r).1 : ℝ),
        ∫ u in (uLower (indices r).2 : ℝ)..(uUpper (indices r).2 : ℝ),
        ∫ z in (a : ℝ)..(cutoff r : ℝ), ∫ w in (a : ℝ)..z,
          safeWeight (((t, u), z), w) * c) =
      ∫ t in (tLower (indices r).1 : ℝ)..(tUpper (indices r).1 : ℝ),
        ∫ u in (uLower (indices r).2 : ℝ)..(uUpper (indices r).2 : ℝ),
        ∫ z in (a : ℝ)..(cutoff r : ℝ), ∫ w in (a : ℝ)..z,
          ((20 * c) * ((K : ℝ) / 80)) * pairedFibreKernel t u z w := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro z hz
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le htt] at ht
    rw [uIcc_of_le huu] at hu
    rw [uIcc_of_le hZZ] at hz
    rw [uIcc_of_le hz.1] at hw
    exact hpoint t ht u hu z hz w hw
  rw [hrewrite]
  simp only [intervalIntegral.integral_const_mul, pairedLocalIntegral]
  ring

/-- Variable rational local Buchstab barrier, integrated against the exact
same nonnegative W_E.  This changes no adopted constants or certificate. -/
theorem row_gainIntegral_lower_of_local_barrier (r : Row) (L : ℚ)
    (hL : ∀ t u z w : ℝ, closedSupport r t u z w →
      (L : ℝ) ≤ LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z)) :
    20 * ((L : ℝ) - (1 : ℝ) / 2) * pairedLocalIntegral (K : ℝ) a
        (tLower (indices r).1) (tUpper (indices r).1)
        (uLower (indices r).2) (uUpper (indices r).2) (cutoff r) ≤ rowGainIntegral r := by
  have he := row_endpoint_bounds r
  have htt : (tLower (indices r).1 : ℝ) ≤ (tUpper (indices r).1 : ℝ) := by
    exact_mod_cast he.2.2.2.2.2.1.le
  have huu : (uLower (indices r).2 : ℝ) ≤ (uUpper (indices r).2 : ℝ) := by
    exact_mod_cast he.2.2.1.le
  have hZZ : (a : ℝ) ≤ (cutoff r : ℝ) := by exact_mod_cast he.1.le
  have hm := fourfold_mono
    (F := fun p => safeWeight p * ((L : ℝ) - (1 : ℝ) / 2))
    (G := fun p => safeWeight p * safeGain p)
    (continuous_safeWeight.mul continuous_const)
    (continuous_safeWeight.mul continuous_safeGain) htt huu hZZ
    (fun t ht u hu z hz w hw => by
      have hs : closedSupport r t u z w := ⟨ht, hu, hz, hw⟩
      rw [safeWeight_eq r hs, safeGain_eq r hs]
      apply mul_le_mul_of_nonneg_left _ (closedSupport_weight_nonneg r hs)
      unfold pairedSemanticBuchstabGain
      exact sub_le_sub_right (hL t u z w hs) _)
  rw [fourfold_safeConstant_eq r ((L : ℝ) - (1 : ℝ) / 2),
    fourfold_safeGain_eq r] at hm
  exact hm

/-- The proved global actual Buchstab theorem closes the local analytic
certificate for every adopted row, including all integration endpoints. -/
theorem row_gainIntegral_ge_certificate (r : Row) :
    pairedLocalIntegral (K : ℝ) a
        (tLower (indices r).1) (tUpper (indices r).1)
        (uLower (indices r).2) (uUpper (indices r).2) (cutoff r) ≤ rowGainIntegral r := by
  have hm := row_gainIntegral_lower_of_local_barrier r (11 / 20 : ℚ)
    (fun t u z w hs => by
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      exact ImbalancedChen.currentChen_buchstab_eleven_twentieths
        (closedSupport_argument r hs))
  norm_num at hm
  exact hm

/-- All 17572 fourfold semantic gain integrals dominate their complete
existing certificate assembly.  This is an analytic integral theorem. -/
theorem fullMask_semantic_gain_ge_integral :
    PairedV2.FullMask.integral ≤ ∑ r : Row, rowGainIntegral r := by
  unfold PairedV2.FullMask.integral
  exact Finset.sum_le_sum (fun r _hr => row_gainIntegral_ge_certificate r)

/-- Finer row-dependent rational pointwise certificates can be inserted
without changing the original same-weight assembly. -/
theorem fullMask_semantic_gain_ge_variable_barriers (L : Row → ℚ)
    (hL : ∀ r : Row, ∀ t u z w : ℝ, closedSupport r t u z w →
      (L r : ℝ) ≤ LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z)) :
    (∑ r : Row, 20 * ((L r : ℝ) - (1 : ℝ) / 2) * pairedLocalIntegral (K : ℝ) a
      (tLower (indices r).1) (tUpper (indices r).1)
      (uLower (indices r).2) (uUpper (indices r).2) (cutoff r)) ≤
        ∑ r : Row, rowGainIntegral r := by
  exact Finset.sum_le_sum (fun r _hr => row_gainIntegral_lower_of_local_barrier r (L r) (hL r))

end FullMask

end

end ImbalancedChen.Certificates.P2PairedFibreBuchstabVariableLower
