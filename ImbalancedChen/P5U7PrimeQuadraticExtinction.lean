import ImbalancedChen.P5U7PrimeExtinctionGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact actual support restriction and quadratic extinction of the prime
cutoff family. Positive-part amplitude and support width are both proved
from the literal log formula; their constants multiply to exactly 1/2.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

/-- The actual prime integral reduces to the raw logarithm on its exact
active outer interval. This includes the zero-width threshold endpoint. -/
theorem p5U7PrimeLeadingIntegral_eq_active_log_interval (eta : ℝ)
    (heta : 0 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ)) :
    p5U7PrimeLeadingIntegral eta =
      ∫ t in (59/250 : ℝ)..(1/(3+eta)), p5U7PrimeCutoffLogRow eta t := by
  let f : ℝ → ℝ := fun t => max 0 (p5U7PrimeCutoffLogRow eta t)
  have hw := p5U7PrimeExtinction_support_width heta hetaH
  have hc : ContinuousOn f (Icc (59/250 : ℝ) (1/3)) :=
    continuousOn_const.max (p5U7PrimeCutoffLogRow_continuousOn eta heta)
  have hp : IntervalIntegrable f volume (59/250 : ℝ) (1/(3+eta)) :=
    ContinuousOn.intervalIntegrable_of_Icc hw.1
      (hc.mono (fun t ht => ⟨ht.1,ht.2.trans hw.2.1⟩))
  have ht : IntervalIntegrable f volume (1/(3+eta)) (1/3 : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hw.2.1
      (hc.mono (fun t ht => ⟨hw.1.trans ht.1,ht.2⟩))
  have htail : (∫ t in (1/(3+eta))..(1/3 : ℝ), f t) = 0 := by
    calc
      _ = ∫ t in (1/(3+eta))..(1/3 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hw.2.1] at ht
        have htI : t ∈ Icc (59/250 : ℝ) (1/3) := ⟨hw.1.trans ht.1,ht.2⟩
        have hlog : p5U7PrimeCutoffLogRow eta t ≤ 0 := by
          apply le_of_not_gt
          intro hpos
          exact (not_lt_of_ge ht.1) ((p5U7PrimeCutoffLogRow_pos_iff heta htI).mp hpos)
        exact max_eq_left hlog
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hp ht
  have hprefix : (∫ t in (59/250 : ℝ)..(1/(3+eta)), f t) =
      ∫ t in (59/250 : ℝ)..(1/(3+eta)), p5U7PrimeCutoffLogRow eta t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hw.1] at ht
    have htI : t ∈ Icc (59/250 : ℝ) (1/3) := ⟨ht.1,ht.2.trans hw.2.1⟩
    have hactive := (p5U7PrimeCutoff_active_iff_outer_cap heta).mpr ht.2
    have hlog := p5U7PrimeCutoffRow_eq_log_active heta htI hactive
    have hmax := p5U7PrimeCutoffRow_eq_log_positive_part heta htI
    exact hmax.symm.trans hlog
  have hfull : p5U7PrimeLeadingIntegral eta =
      ∫ t in (59/250 : ℝ)..(1/3 : ℝ), f t :=
    p5U7PrimeLeadingIntegral_eq_log_positive_part eta heta
  rw [htail,add_zero] at hadd
  exact hfull.trans (hadd.symm.trans hprefix)

/-- Explicit quadratic upper decay throughout the entire valid native
interval 0<=eta<=73/59, including both endpoints. -/
theorem p5U7PrimeLeadingIntegral_quadratic_extinction (eta : ℝ)
    (heta : 0 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ)) :
    0 ≤ p5U7PrimeLeadingIntegral eta ∧
      p5U7PrimeLeadingIntegral eta ≤ (1/2 : ℝ)*((73/59 : ℝ)-eta)^2 := by
  have hw := p5U7PrimeExtinction_support_width heta hetaH
  have hdelta : 0 ≤ (73/59 : ℝ)-eta := sub_nonneg.mpr hetaH
  have hAmp : 0 ≤ p5U7PrimeExtinctionAmplitude*((73/59 : ℝ)-eta) := by
    unfold p5U7PrimeExtinctionAmplitude
    positivity
  have hnonneg : 0 ≤ p5U7PrimeLeadingIntegral eta := by
    rw [p5U7PrimeLeadingIntegral_eq_log_positive_part eta heta]
    apply intervalIntegral.integral_nonneg (by norm_num : (59/250 : ℝ) ≤ 1/3)
    intro t _
    exact le_max_left _ _
  have hcont := p5U7PrimeCutoffLogRow_continuousOn eta heta
  have hp : IntervalIntegrable (p5U7PrimeCutoffLogRow eta) volume
      (59/250 : ℝ) (1/(3+eta)) :=
    ContinuousOn.intervalIntegrable_of_Icc hw.1
      (hcont.mono (fun t ht => ⟨ht.1,ht.2.trans hw.2.1⟩))
  have hrow : ∀ t ∈ Icc (59/250 : ℝ) (1/(3+eta)),
      p5U7PrimeCutoffLogRow eta t ≤ p5U7PrimeExtinctionAmplitude*((73/59 : ℝ)-eta) := by
    intro t ht
    exact (le_max_right _ _).trans
      (p5U7PrimeExtinction_row_amplitude heta hetaH ⟨ht.1,ht.2.trans hw.2.1⟩).2
  have hm := intervalIntegral.integral_mono_on hw.1 hp
    (continuous_const.intervalIntegrable (59/250) (1/(3+eta))) hrow
  have hconst : (∫ t in (59/250 : ℝ)..(1/(3+eta)),
      p5U7PrimeExtinctionAmplitude*((73/59 : ℝ)-eta)) =
      (p5U7PrimeExtinctionAmplitude*((73/59 : ℝ)-eta))*(1/(3+eta)-(59/250 : ℝ)) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hconst,← p5U7PrimeLeadingIntegral_eq_active_log_interval eta heta hetaH] at hm
  have hwidth := mul_le_mul_of_nonneg_left hw.2.2 hAmp
  have hexact : (p5U7PrimeExtinctionAmplitude*((73/59 : ℝ)-eta)) *
      (((59/250 : ℝ)/3)*((73/59 : ℝ)-eta)) = (1/2 : ℝ)*((73/59 : ℝ)-eta)^2 := by
    dsimp only [p5U7PrimeExtinctionAmplitude]
    ring
  rw [hexact] at hwidth
  exact ⟨hnonneg,hm.trans hwidth⟩
end
end ImbalancedChen
