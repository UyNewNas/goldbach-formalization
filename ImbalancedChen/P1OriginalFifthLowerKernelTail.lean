import ImbalancedChen.P1HistoricalFifthJointIntegralSign
import ImbalancedChen.ActualThirdPrefixTailIntegralCore
import ImbalancedChen.P1OriginalHistoricalSmallCoordinateGap

/-!
The genuine lower/I5 kernel at the noncompact last-coordinate boundary.
The decay is supplied by the already proved canonical Suzuki source DDE,
not by an assumed limit of the target integral. The independent old and new
strict own-cube indicators are retained in the definition and both are
proved open on the small-coordinate region.

The fourth coordinate is integrated from the fifth coordinate to rho.
Consequently its logarithm is present in the exact envelope
  C * h * (log(rho/h)+1),
rather than silently treating the fourth coordinate as bounded away from zero.
Only local geometric level/gap conditions are supplied by the original
strategy. No arithmetic small-prime approximation is asserted here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open scoped Classical BigOperators ENNReal

namespace P1OriginalFifthLowerKernelTail

def kernel (old new : ℝ) (t : Fin 5 → ℝ) : ℝ :=
  (primeOwnCubeGatedProfile new t - primeOwnCubeGatedProfile old t) * ∏ i, 1 / t i

/-- This is the actual two-indicator lower profile, not a shared-gate model. -/
theorem small_last_both_ownCubes {u old new : ℝ} {t : Fin 5 → ℝ}
    (hu : 0 < u) (hw : 0 < t 4) (hsmall : t 4 ≤ u / 3)
    (hgap : u ≤ old - ∑ i, t i) (hlevels : old ≤ new) :
    3 ≤ (old - ∑ i, t i) / t 4 ∧
      primeTupleOwnCubeForm t < old ∧ primeTupleOwnCubeForm t < new := by
  have hs : 3 * t 4 ≤ old - ∑ i, t i := by linarith
  refine ⟨(le_div_iff₀ hw).mpr (by linarith), ?_, ?_⟩ <;>
    unfold primeTupleOwnCubeForm <;> change (∑ i, t i) + 2 * t 4 < _ <;> linarith

/-- Quadratic decay comes from the genuine canonical gap at the smaller
argument. Cancellation against both occurrences of the last coordinate
leaves one reciprocal fourth coordinate, which must still be integrated. -/
theorem kernel_tail_bound {u old new : ℝ} {t : Fin 5 → ℝ}
    (hu : 0 < u) (hpos : ∀ i, 0 < t i) (hsmall : t 4 ≤ u / 3)
    (hgap : u ≤ old - ∑ i, t i) (hlevels : old ≤ new) :
    0 ≤ kernel old new t ∧
      kernel old new t ≤ 12 / (t 0 * t 1 * t 2 * t 3 * u ^ 2) := by
  have hw := hpos 4
  have hg := small_last_both_ownCubes hu hw hsmall hgap hlevels
  have hsnew : (old - ∑ i, t i) / t 4 ≤ (new - ∑ i, t i) / t 4 :=
    div_le_div_of_nonneg_right (sub_le_sub_right hlevels _) hw.le
  have hsold2 : 2 ≤ (old - ∑ i, t i) / t 4 := by linarith [hg.1]
  have hsnew2 := hsold2.trans hsnew
  have hdiff := thirdTailLowerFactor_difference hsold2 hsnew
  have hdecay := hdiff.2.trans (actualSieveGap_normalized_le_three_div_sq hg.1)
  have hweight : 0 ≤ ∏ i, 1 / t i := Finset.prod_nonneg (fun i _ => by positivity)
  have hgapPos : 0 < old - ∑ i, t i := hu.trans_le hgap
  have hprofile : primeOwnCubeGatedProfile new t - primeOwnCubeGatedProfile old t =
      4 * (thirdTailLowerFactor ((new - ∑ i, t i) / t 4) -
        thirdTailLowerFactor ((old - ∑ i, t i) / t 4)) / t 4 := by
    rw [primeOwnCubeGatedProfile, if_pos hg.2.2,
      primeOwnCubeGatedProfile, if_pos hg.2.1,
      p1PrimeTupleMinusProfile_eq_lowerFactor new t hw,
      p1PrimeTupleMinusProfile_eq_lowerFactor old t hw,
      actualExtendedThirdLowerFactor_of_two_le hsnew2,
      actualExtendedThirdLowerFactor_of_two_le hsold2]
    ring
  have hprofileBound : primeOwnCubeGatedProfile new t - primeOwnCubeGatedProfile old t ≤
      12 * t 4 / u ^ 2 := by
    rw [hprofile]
    calc
      _ ≤ 4 * (3 / ((old - ∑ i, t i) / t 4) ^ 2) / t 4 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay (by norm_num)) hw.le
      _ = 12 * t 4 / (old - ∑ i, t i) ^ 2 := by
        field_simp [hw.ne', hgapPos.ne']
        <;> ring
      _ ≤ 12 * t 4 / u ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hu)
        gcongr
  constructor
  · exact mul_nonneg (sub_nonneg.mpr (p1PrimeOwnCubeGatedProfile_mono t hw hlevels)) hweight
  · unfold kernel
    calc
      _ ≤ (12 * t 4 / u ^ 2) * ∏ i, 1 / t i :=
        mul_le_mul_of_nonneg_right hprofileBound hweight
      _ = 12 / (t 0 * t 1 * t 2 * t 3 * u ^ 2) := by
        simp only [Fin.prod_univ_succ]
        field_simp [(hpos 0).ne', (hpos 1).ne', (hpos 2).ne', (hpos 3).ne', hw.ne', hu.ne']
        <;> ring

def logPrimitive (rho h : ℝ) : ℝ := h * (Real.log (rho / h) + 1)

theorem hasDerivAt_logPrimitive {rho z : ℝ} (hrho : 0 < rho) (hz : 0 < z) :
    HasDerivAt (logPrimitive rho) (Real.log (rho / z)) z := by
  have hlog : HasDerivAt (fun t : ℝ => Real.log (rho / t)) (-1 / z) z := by
    apply (((hasDerivAt_const z rho).fun_div (hasDerivAt_id z) hz.ne').log
      (div_ne_zero hrho.ne' hz.ne')).congr_deriv
    simp only [id_eq]
    field_simp [hrho.ne', hz.ne']
    <;> ring
  unfold logPrimitive
  apply ((hasDerivAt_id z).fun_mul (hlog.add_const 1)).congr_deriv
  simp only [id_eq]
  field_simp [hz.ne']
  <;> ring

theorem tendsto_logPrimitive_zero {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (logPrimitive rho) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun h : ℝ => h * Real.log (rho / h)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [pow_one] using tendsto_mul_log_div_pow_zero 1 hrho
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsum := hlog.add hid
  simp only [add_zero] at hsum
  convert hsum using 1
  ext h
  unfold logPrimitive
  ring

theorem continuousOn_logPrimitive {rho h : ℝ} (hrho : 0 < rho) :
    ContinuousOn (logPrimitive rho) (Icc 0 h) := by
  intro z hz
  rcases eq_or_lt_of_le hz.1 with rfl | hzpos
  · have hc : ContinuousWithinAt (logPrimitive rho) (Ioi 0) 0 := by
      simpa [ContinuousWithinAt, logPrimitive] using tendsto_logPrimitive_zero hrho
    apply hc.insert.mono
    intro z hz
    rcases eq_or_lt_of_le hz.1 with rfl | hzpos
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ hzpos
  · exact (hasDerivAt_logPrimitive hrho hzpos).continuousAt.continuousWithinAt

theorem integrableOn_log {rho h : ℝ} (hrho : 0 < rho) (hhrho : h ≤ rho) :
    IntegrableOn (fun z : ℝ => Real.log (rho / z)) (Ioc 0 h) := by
  apply intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_logPrimitive hrho)
    (fun z hz => hasDerivAt_logPrimitive hrho hz.1)
  intro z hz
  exact Real.log_nonneg ((le_div_iff₀ hz.1).mpr (by linarith [hz.2]))

theorem integral_log {rho h : ℝ} (hrho : 0 < rho) (hh : 0 < h) (hhrho : h ≤ rho) :
    (∫ z in Ioc 0 h, Real.log (rho / z)) = logPrimitive rho h := by
  have hint : IntervalIntegrable (fun z : ℝ => Real.log (rho / z)) volume 0 h := by
    constructor
    · exact integrableOn_log hrho hhrho
    · simp [Ioc_eq_empty (not_lt.mpr hh.le)]
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hh
    (fun z hz => hasDerivAt_logPrimitive hrho hz.1) hint
    (tendsto_logPrimitive_zero hrho)
    (tendsto_nhdsWithin_of_tendsto_nhds
      (hasDerivAt_logPrimitive hrho hh).continuousAt.tendsto)
  simpa only [intervalIntegral.integral_of_le hh.le, sub_zero] using heq

theorem lintegral_log {rho h : ℝ} (hrho : 0 < rho) (hh : 0 < h) (hhrho : h ≤ rho) :
    (∫⁻ z in Ioc 0 h, ENNReal.ofReal (Real.log (rho / z))) =
      ENNReal.ofReal (logPrimitive rho h) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 h)] (fun z : ℝ => Real.log (rho / z)) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact ae_of_all _ (fun z hz =>
      Real.log_nonneg ((le_div_iff₀ hz.1).mpr (by linarith [hz.2])))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_log hrho hhrho) hnn,
    integral_log hrho hh hhrho]

/-- Three active coordinates are bounded below by omega. Their reciprocal
mass is exactly log(rho/omega)^3, not an unproved volume budget. -/
theorem lintegral_active_three {c omega rho : ℝ} (hc : 0 ≤ c)
    (homega : 0 < omega) (horho : omega ≤ rho) :
    (∫⁻ x in Ioc omega rho, ∫⁻ y in Ioc omega rho, ∫⁻ z in Ioc omega rho,
      ENNReal.ofReal (c * (1 / x) * (1 / y) * (1 / z))) =
      ENNReal.ofReal (c * Real.log (rho / omega) ^ 3) := by
  have hlog : 0 ≤ Real.log (rho / omega) :=
    Real.log_nonneg ((le_div_iff₀ homega).mpr (by simpa using horho))
  calc
    _ = ∫⁻ x in Ioc omega rho,
        ENNReal.ofReal ((c * Real.log (rho / omega) ^ 2) * (1 / x)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hxpos : 0 < x := homega.trans hx.1
      rw [thirdTail_lintegral_square (mul_nonneg hc (by positivity)) homega horho]
      congr 1
      ring
    _ = ENNReal.ofReal ((c * Real.log (rho / omega) ^ 2) * Real.log (rho / omega)) :=
      thirdTail_lintegral_const_mul_one_div (mul_nonneg hc (sq_nonneg _)) homega horho
    _ = _ := by congr 1; ring

def join (x y z v w : ℝ) : Fin 5 → ℝ := ![x, y, z, v, w]

def tailMass (S : Set (Fin 5 → ℝ)) (old new : (Fin 5 → ℝ) → ℝ)
    (omega rho h : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in Ioc 0 h, ∫⁻ v in Ioc w rho,
    ∫⁻ x in Ioc omega rho, ∫⁻ y in Ioc omega rho, ∫⁻ z in Ioc omega rho,
      ENNReal.ofReal (if join x y z v w ∈ S ∧ StrictAnti (join x y z v w) then
        kernel (old (join x y z v w)) (new (join x y z v w)) (join x y z v w) else 0)

/-- A genuine fivefold improper integral of the explicit positive envelope. -/
theorem lintegral_majorant {c omega rho h : ℝ} (hc : 0 ≤ c)
    (homega : 0 < omega) (horho : omega ≤ rho) (hh : 0 < h) (hhrho : h ≤ rho) :
    (∫⁻ w in Ioc 0 h, ∫⁻ v in Ioc w rho,
      ∫⁻ x in Ioc omega rho, ∫⁻ y in Ioc omega rho, ∫⁻ z in Ioc omega rho,
        ENNReal.ofReal (c * (1 / v) * (1 / x) * (1 / y) * (1 / z))) =
      ENNReal.ofReal (c * Real.log (rho / omega) ^ 3 * logPrimitive rho h) := by
  have hlog : 0 ≤ Real.log (rho / omega) :=
    Real.log_nonneg ((le_div_iff₀ homega).mpr (by simpa using horho))
  calc
    _ = ∫⁻ w in Ioc 0 h,
        ENNReal.ofReal ((c * Real.log (rho / omega) ^ 3) * Real.log (rho / w)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro w hw
      calc
        _ = ∫⁻ v in Ioc w rho,
            ENNReal.ofReal ((c * Real.log (rho / omega) ^ 3) * (1 / v)) := by
          apply setLIntegral_congr_fun measurableSet_Ioc
          intro v hv
          have hvpos : 0 < v := hw.1.trans hv.1
          rw [lintegral_active_three (mul_nonneg hc (by positivity)) homega horho]
          congr 1
          ring
        _ = _ := thirdTail_lintegral_const_mul_one_div
          (mul_nonneg hc (pow_nonneg hlog 3)) hw.1 (hw.2.trans hhrho)
    _ = ENNReal.ofReal (c * Real.log (rho / omega) ^ 3) *
        ∫⁻ w in Ioc 0 h, ENNReal.ofReal (Real.log (rho / w)) := by
      simp_rw [ENNReal.ofReal_mul (mul_nonneg hc (pow_nonneg hlog 3))]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      rw [lintegral_log (homega.trans_le horho) hh hhrho,
        ENNReal.ofReal_mul (mul_nonneg hc (pow_nonneg hlog 3))]

/-- A local original-strategy numerator gap is the only analytic input
condition. The canonical source decay and integrable majorant are conclusions. -/
theorem tailMass_le {S : Set (Fin 5 → ℝ)} {old new : (Fin 5 → ℝ) → ℝ}
    {u omega rho h : ℝ} (hu : 0 < u) (homega : 0 < omega) (horho : omega ≤ rho)
    (hh : 0 < h) (hsmall : h ≤ u / 3) (hhrho : h ≤ rho)
    (hgeom : ∀ t ∈ S, StrictAnti t → (∀ i, 0 < t i) →
      omega ≤ t 2 → t 0 ≤ rho → t 4 ≤ h →
        old t ≤ new t ∧ u ≤ old t - ∑ i, t i) :
    tailMass S old new omega rho h ≤
      ENNReal.ofReal ((12 / u ^ 2) * Real.log (rho / omega) ^ 3 * logPrimitive rho h) := by
  rw [← lintegral_majorant (c := 12 / u ^ 2) (by positivity) homega horho hh hhrho]
  unfold tailMass
  apply setLIntegral_mono' measurableSet_Ioc
  intro w hw
  apply setLIntegral_mono' measurableSet_Ioc
  intro v hv
  apply setLIntegral_mono' measurableSet_Ioc
  intro x hx
  apply setLIntegral_mono' measurableSet_Ioc
  intro y hy
  apply setLIntegral_mono' measurableSet_Ioc
  intro z hz
  have hxpos : 0 < x := homega.trans hx.1
  have hypos : 0 < y := homega.trans hy.1
  have hzpos : 0 < z := homega.trans hz.1
  have hvpos : 0 < v := hw.1.trans hv.1
  apply ENNReal.ofReal_le_ofReal
  by_cases hs : join x y z v w ∈ S ∧ StrictAnti (join x y z v w)
  · rw [if_pos hs]
    have hpos : ∀ i, 0 < join x y z v w i := by
      intro i
      fin_cases i <;> simp [join] <;> linarith [hw.1]
    have hg := hgeom _ hs.1 hs.2 hpos (by simpa [join] using hz.1.le)
      (by simpa [join] using hx.2) (by simpa [join] using hw.2)
    have hk := (kernel_tail_bound hu hpos (by simpa [join] using hw.2.trans hsmall) hg.2 hg.1).2
    calc
      _ ≤ 12 / (x * y * z * v * u ^ 2) := by simpa [join] using hk
      _ = (12 / u ^ 2) * (1 / v) * (1 / x) * (1 / y) * (1 / z) := by
        field_simp [hu.ne', hxpos.ne', hypos.ne', hzpos.ne', hvpos.ne']
        <;> ring
  · rw [if_neg hs]
    positivity

theorem tailMass_ne_top {S : Set (Fin 5 → ℝ)} {old new : (Fin 5 → ℝ) → ℝ}
    {u omega rho h : ℝ} (hu : 0 < u) (homega : 0 < omega) (horho : omega ≤ rho)
    (hh : 0 < h) (hsmall : h ≤ u / 3) (hhrho : h ≤ rho)
    (hgeom : ∀ t ∈ S, StrictAnti t → (∀ i, 0 < t i) →
      omega ≤ t 2 → t 0 ≤ rho → t 4 ≤ h →
        old t ≤ new t ∧ u ≤ old t - ∑ i, t i) :
    tailMass S old new omega rho h ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (tailMass_le hu homega horho hh hsmall hhrho hgeom)

/-- The cutoff may change the finite joint table. The tail bound remains
uniform because u and omega are geometric constants, not a target-tail premise. -/
theorem tailMass_tendsto_zero {omega rho u : ℝ}
    (homega : 0 < omega) (horho : omega ≤ rho) (hu : 0 < u)
    (S : ℝ → Set (Fin 5 → ℝ)) (old new : ℝ → (Fin 5 → ℝ) → ℝ)
    (hgeom : ∀ h, 0 < h → h ≤ u / 3 →
      ∀ t ∈ S h, StrictAnti t → (∀ i, 0 < t i) →
        omega ≤ t 2 → t 0 ≤ rho → t 4 ≤ h →
          old h t ≤ new h t ∧ u ≤ old h t - ∑ i, t i) :
    Tendsto (fun h => tailMass (S h) (old h) (new h) omega rho h)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have hrho : 0 < rho := homega.trans_le horho
  have hupper : Tendsto (fun h => ENNReal.ofReal
      ((12 / u ^ 2) * Real.log (rho / omega) ^ 3 * logPrimitive rho h))
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal ((tendsto_logPrimitive_zero hrho).const_mul
        ((12 / u ^ 2) * Real.log (rho / omega) ^ 3))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · exact Eventually.of_forall (fun _ => bot_le)
  · have hsmall : Iio (u / 3) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
    have hr : Iio rho ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds hrho)
    filter_upwards [self_mem_nhdsWithin, hsmall, hr] with h hh hs hr
    exact tailMass_le hu homega horho hh hs.le hr.le (hgeom h hh hs.le)

/-- Concrete original-third hypotheses supply the required u=omega/2.
Only the last coordinate is small; the fourth may range all the way to rho. -/
theorem kernel_bound_of_original_third_cube {omega gamma old new : ℝ}
    (t : Fin 5 → ℝ) (homega : 0 < omega) (hpos : ∀ i, 0 < t i)
    (hactive : omega ≤ t 2) (hcube : t 0 + t 1 + 3 * t 2 < gamma)
    (horder : t 3 < t 2) (h34 : gamma ≤ old) (h45 : old ≤ new)
    (hsmall : t 4 ≤ omega / 6) :
    0 ≤ kernel old new t ∧
      kernel old new t ≤ 12 / (t 0 * t 1 * t 2 * t 3 * (omega / 2) ^ 2) := by
  have hgap := (HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_numerator_gap
    omega gamma old t hactive hcube horder h34).2
  apply kernel_tail_bound (by positivity) hpos
    (by linarith : t 4 ≤ (omega / 2) / 3) (by linarith) h45

/-- The original third cube and the actual h34/h45 level comparisons imply
the local gap; no target-integral tail hypothesis is supplied. -/
theorem tailMass_tendsto_zero_of_original_third_cube {omega rho : ℝ}
    (homega : 0 < omega) (horho : omega ≤ rho)
    (S : ℝ → Set (Fin 5 → ℝ)) (gamma old new : ℝ → (Fin 5 → ℝ) → ℝ)
    (hregion : ∀ h, 0 < h → h ≤ omega / 6 →
      ∀ t ∈ S h, StrictAnti t → (∀ i, 0 < t i) →
        omega ≤ t 2 → t 0 ≤ rho → t 4 ≤ h →
          t 0 + t 1 + 3 * t 2 < gamma h t ∧
            gamma h t ≤ old h t ∧ old h t ≤ new h t) :
    Tendsto (fun h => tailMass (S h) (old h) (new h) omega rho h)
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  apply tailMass_tendsto_zero homega horho (by positivity : 0 < omega / 2) S old new
  intro h hh hs t ht hanti hpos hactive hrho hlast
  have hc := hregion h hh (by linarith) t ht hanti hpos hactive hrho hlast
  have hg := (HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_numerator_gap
    omega (gamma h t) (old h t) t hactive hc.1
      (hanti (by decide : (2 : Fin 5) < 3)) hc.2.1).2
  exact ⟨hc.2.2, by linarith⟩

/-- Real convergence follows from a genuine nonnegative mass limit, with
all sufficiently small masses already bounded by a finite envelope. -/
theorem tail_toReal_tendsto_zero_of_original_third_cube {omega rho : ℝ}
    (homega : 0 < omega) (horho : omega ≤ rho)
    (S : ℝ → Set (Fin 5 → ℝ)) (gamma old new : ℝ → (Fin 5 → ℝ) → ℝ)
    (hregion : ∀ h, 0 < h → h ≤ omega / 6 →
      ∀ t ∈ S h, StrictAnti t → (∀ i, 0 < t i) →
        omega ≤ t 2 → t 0 ≤ rho → t 4 ≤ h →
          t 0 + t 1 + 3 * t 2 < gamma h t ∧
            gamma h t ≤ old h t ∧ old h t ≤ new h t) :
    Tendsto (fun h => (tailMass (S h) (old h) (new h) omega rho h).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  have hm := tailMass_tendsto_zero_of_original_third_cube homega horho S gamma old new hregion
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hm

end P1OriginalFifthLowerKernelTail

end

end ImbalancedChen
