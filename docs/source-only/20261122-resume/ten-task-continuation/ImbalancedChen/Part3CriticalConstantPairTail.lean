import ImbalancedChen.Part3CuspConstantModeTailL2
import ImbalancedChen.Part3ConstantWeightedHeightFlux
import ImbalancedChen.Part3PrimePhysicalScattering
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Tail integrability of the incoming and outgoing critical powers in the
constant Fourier coefficient. The positive height dilation below preserves
the full mixed term and reverses its sign. The application uses the actual
ordinary Eisenstein horocycle mean at the original level. -/

namespace ImbalancedChen.Part3.CriticalConstantPairTail

noncomputable section

open Set MeasureTheory
open CuspConstantModeTailL2SourceOnly CriticalEisensteinScattering20261025a
open AllLevelCentralNormalization20261026a OrdinaryCentralFourierMeans20261026b
open LevelOldformScattering20261026a CompletedActualEisensteinIdentity20261025a
open PrimePhysicalScattering20261026b PrimitiveEisensteinFourierParameterAnalytic

/-- The two powers in the width-one constant coefficient. -/
def criticalPair (t : ℝ) (A B : ℂ) (y : ℝ) : ℂ :=
  A * (y : ℂ) ^ criticalParameter t + B * (y : ℂ) ^ (1 - criticalParameter t)

private theorem critical_norm_sq {s : ℂ} (hs : s.re = 1 / 2)
    {y : ℝ} (hy : 0 < y) : ‖(y : ℂ) ^ s‖ ^ 2 = y := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, hs, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt hy.le]

private theorem reflected_re (t : ℝ) : (1 - criticalParameter t).re = 1 / 2 := by
  rw [Complex.sub_re, Complex.one_re, criticalParameter_re]
  norm_num

/-- At this dilation the two critical powers acquire opposite multipliers.
The dilation also works when the frequency is negative. -/
private theorem exists_opposite_dilation {t : ℝ} (ht : t ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      (c : ℂ) ^ (1 - criticalParameter t) = -((c : ℂ) ^ criticalParameter t) := by
  let c := Real.exp (Real.pi / (2 * t))
  have hc : 0 < c := Real.exp_pos _
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have harg : ((Real.pi / (2 * t) : ℝ) : ℂ) * (2 * criticalParameter t - 1) =
      (Real.pi : ℂ) * Complex.I := by
    unfold criticalParameter
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ht] <;> ring
  have he : (c : ℂ) ^ (2 * criticalParameter t - 1) = -1 := by
    rw [Complex.cpow_def_of_ne_zero hcC, ← Complex.ofReal_log hc.le,
      show Real.log c = Real.pi / (2 * t) from Real.log_exp _, harg, Complex.exp_pi_mul_I]
  have h : (c : ℂ) ^ criticalParameter t = -((c : ℂ) ^ (1 - criticalParameter t)) := by
    calc
      (c : ℂ) ^ criticalParameter t =
          (c : ℂ) ^ ((1 - criticalParameter t) + (2 * criticalParameter t - 1)) := by
        congr 1 <;> ring
      _ = _ := by rw [Complex.cpow_add _ _ hcC, he]; ring
  exact ⟨c, hc, by rw [h, neg_neg]⟩

/-- The energy at two dilated heights gives the complete diagonal energy,
even when the undilated waves cancel at some heights. -/
theorem criticalPair_two_heights {t c y : ℝ} (A B : ℂ) (hc : 0 < c) (hy : 0 < y)
    (hphase : (c : ℂ) ^ (1 - criticalParameter t) = -((c : ℂ) ^ criticalParameter t)) :
    hyperbolicEnergyDensity (criticalPair t A B) y +
        c * hyperbolicEnergyDensity (criticalPair t A B) (c * y) =
      (2 * (‖A‖ ^ 2 + ‖B‖ ^ 2)) / y := by
  let u := A * (y : ℂ) ^ criticalParameter t
  let v := B * (y : ℂ) ^ (1 - criticalParameter t)
  have hscale : criticalPair t A B (c * y) =
      (c : ℂ) ^ criticalParameter t * (u - v) := by
    unfold criticalPair
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hy.le,
      Complex.mul_cpow_ofReal_nonneg hc.le hy.le, hphase]
    dsimp only [u, v]
    ring
  have huv : ‖u‖ ^ 2 + ‖v‖ ^ 2 = (‖A‖ ^ 2 + ‖B‖ ^ 2) * y := by
    dsimp only [u, v]
    simp only [norm_mul, mul_pow, critical_norm_sq (criticalParameter_re t) hy,
      critical_norm_sq (reflected_re t) hy]
    ring
  calc
    _ = (‖u + v‖ ^ 2 + ‖u - v‖ ^ 2) / y ^ 2 := by
      unfold hyperbolicEnergyDensity
      rw [hscale, norm_mul, mul_pow, critical_norm_sq (criticalParameter_re t) hc]
      change ‖u + v‖ ^ 2 / y ^ 2 + c * (c * ‖u - v‖ ^ 2 / (c * y) ^ 2) = _
      field_simp [hy.ne', hc.ne'] <;> ring
    _ = _ := by
      rw [parallelogram_law_with_norm ℂ u v, huv]
      field_simp [hy.ne'] <;> ring

private theorem coeff_zero_of_integrable_div {k H : ℝ}
    (h : IntegrableOn (fun y : ℝ => k / y) (Ioi H)) : k = 0 := by
  have hC : IntegrableOn (fun y : ℝ => (k : ℂ) / (y : ℂ)) (Ioi H) := by
    simpa only [Complex.ofReal_div] using (Integrable.ofReal (𝕜 := ℂ) h)
  exact_mod_cast (ConstantWeightedHeightFlux20261026b.eq_zero_of_integrableOn_div_height hC)

/-- At every nonzero real frequency both coefficients must vanish. No
condition on their phases or relative moduli is needed. -/
theorem criticalPair_tailL2_iff {t Y : ℝ} (ht : t ≠ 0) (hY : 0 < Y) (A B : ℂ) :
    TailL2 (criticalPair t A B) Y ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc, hphase⟩ := exists_opposite_dilation ht
    let D := hyperbolicEnergyDensity (criticalPair t A B)
    let H := max Y (Y / c)
    have hYH : Y ≤ H := le_max_left _ _
    have hYcH : Y ≤ c * H := by
      rw [mul_comm c H]
      exact (div_le_iff₀ hc).mp (le_max_right _ _)
    have hD : IntegrableOn D (Ioi H) := h.mono (Ioi_subset_Ioi hYH) le_rfl
    have hDc : IntegrableOn (fun y => D (c * y)) (Ioi H) :=
      (integrableOn_Ioi_comp_mul_left_iff D H hc).mpr (h.mono (Ioi_subset_Ioi hYcH) le_rfl)
    have hdiag : IntegrableOn (fun y : ℝ => (2 * (‖A‖ ^ 2 + ‖B‖ ^ 2)) / y) (Ioi H) := by
      apply (hD.add (hDc.const_mul c)).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact criticalPair_two_heights A B hc ((hY.trans_le hYH).trans hy) hphase
    have hz := coeff_zero_of_integrable_div hdiag
    constructor
    · by_contra hA
      have hp := pow_pos (norm_pos_iff.mpr hA) 2
      linarith [sq_nonneg ‖B‖]
    · by_contra hB
      have hp := pow_pos (norm_pos_iff.mpr hB) 2
      linarith [sq_nonneg ‖A‖]
  · rintro ⟨rfl, rfl⟩
    simp [TailL2, hyperbolicEnergyDensity, criticalPair]

/-- At the double root the two displayed powers coincide. Only their
sum can be recovered from the tail of this particular pair. -/
theorem criticalPair_zero_tailL2_iff {Y : ℝ} (hY : 0 < Y) (A B : ℂ) :
    TailL2 (criticalPair 0 A B) Y ↔ A + B = 0 := by
  have hhalf : criticalParameter 0 = 1 / 2 := by simp [criticalParameter]
  have hpair (y : ℝ) : criticalPair 0 A B y = (A + B) * (y : ℂ) ^ (1 / 2 : ℂ) := by
    unfold criticalPair
    rw [hhalf, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, add_mul]
  constructor
  · intro h
    have hdiv : IntegrableOn (fun y : ℝ => ‖A + B‖ ^ 2 / y) (Ioi Y) := by
      apply h.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 := hY.trans hy
      rw [hyperbolicEnergyDensity, hpair, norm_mul, mul_pow,
        critical_norm_sq (s := (1 / 2 : ℂ)) (by norm_num) hy0]
      field_simp [hy0.ne'] <;> ring
    have hz := coeff_zero_of_integrable_div hdiv
    by_contra hab
    exact (pow_pos (norm_pos_iff.mpr hab) 2).ne' hz
  · intro hab
    have hf : criticalPair 0 A B = fun _ => 0 := by funext y; rw [hpair, hab, zero_mul]
    simp [TailL2, hyperbolicEnergyDensity, hf]

/-- The ordinary unit-width horocycle mean at infinity, extended by zero
outside the geometric height domain. -/
def ordinaryInfinityMean (N : ℕ) (t y : ℝ) : ℂ :=
  if hy : 0 < y then
    ∫ x in (0 : ℝ)..1, centralOrdinaryLevel N (criticalParameter t) (horizontalPoint y hy x)
  else 0

/-- The mean of the actual incoming Eisenstein series at infinity, for
every positive level, belongs to the height tail precisely at its
pole-removed central parameter. -/
theorem ordinaryInfinityMean_tailL2_iff (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) : TailL2 (ordinaryInfinityMean N t) Y ↔ t = 0 := by
  by_cases ht : t = 0
  · subst t
    have hf : ordinaryInfinityMean N 0 = fun _ => 0 := by
      funext y
      by_cases hy : 0 < y
      · simpa [ordinaryInfinityMean, hy, criticalParameter] using ordinary_infinity_mean_center N y hy
      · simp [ordinaryInfinityMean, hy]
    simp [TailL2, hyperbolicEnergyDensity, hf]
  let s := criticalParameter t
  let B := completedScattering s * normalizedHeightMoment N s (1 - s)
  have hs : 0 < s.re := by rw [show s = criticalParameter t from rfl, criticalParameter_re]; norm_num
  have hh := criticalParameter_ne_half ht
  have hd := critical_completed_denominator_ne_zero t
  have hmean (y : ℝ) (hy : 0 < y) : ordinaryInfinityMean N t y = criticalPair t 1 B y := by
    rw [ordinaryInfinityMean, dif_pos hy, ordinary_infinity_mean,
      completedInfinityConstant_eq N _ hs hh y hy,
      inverseCompletion_eq_actual_reciprocal _ (criticalParameter_mem_centralDomain t) hh,
      completionFactor_eq_completedZeta_of_re_pos _ hs]
    dsimp only [criticalPair, B, s, completedScattering]
    field_simp [hd] <;> ring
  have heq : TailL2 (ordinaryInfinityMean N t) Y ↔ TailL2 (criticalPair t 1 B) Y := by
    apply integrableOn_congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [hyperbolicEnergyDensity, hmean y (hY.trans hy)]
  rw [heq, criticalPair_tailL2_iff ht hY]
  simp [ht]

end
end ImbalancedChen.Part3.CriticalConstantPairTail
