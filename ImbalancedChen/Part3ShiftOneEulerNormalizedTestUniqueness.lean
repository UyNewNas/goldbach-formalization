import ImbalancedChen.Part3ShiftOneEulerNormalizedTestEstimate
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Exact scalar shift-one deficiency uniqueness from the ACTUAL normalized
test norm bound, without a pointwise small-height growth assertion.
Tail L2 selects B*y^alphaMinus. Actual profile scaling and the supplied
C*t^(-1/2) bound force ||B||*||moment||<=C*t^beta with beta>0. Native
positive-power continuity at zero makes the coefficient vanish whenever
the fixed test's actual weighted moment is nonzero.

The geometric normalized-test estimate remains an explicit input.
No global horocycle-mean L2 or pointwise growth is inferred. The fixed
test's nonzero moment is explicit here and has a separate constructive
witness downstream. Exact shift 1 only; no Gamma completeness claim.
-/

namespace ImbalancedChen.Part3.ShiftOneEulerNormalizedTestUniqueness20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z NormalizedHeightProfileScaling20261026b
open ShiftOneEulerClassification20261026b ShiftOneEulerTailSelection20261026b
open ShiftOneEulerNormalizedTestEstimate20261026b

theorem decayingCoefficient_zero_of_normalizedTests {C : ℝ} {φ : PositiveHeight → ℂ}
    {f : ℝ → ℂ} {B : ℂ}
    (hclass : ∀ y : ℝ, 0 < y → f y = B * eulerPower alphaMinus y)
    (hmoment : heightPowerPairing alphaMinus φ ≠ 0)
    (hbound : NormalizedEulerTestBound C φ f) : B = 0 := by
  have hpow : Tendsto (fun y : ℝ => y ^ normalizedDecayGap) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [Real.zero_rpow normalizedDecayGap_pos.ne'] using
      ((Real.continuous_rpow_const normalizedDecayGap_pos.le).tendsto (0 : ℝ)).mono_left inf_le_left
  have hright : Tendsto (fun y : ℝ => C * y ^ normalizedDecayGap) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hpow
  have hupper0 : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y < 1 := Iio_mem_nhds zero_lt_one
  have hupper : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), y < 1 := hupper0.filter_mono inf_le_left
  have hbudget : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      ‖B‖ * ‖heightPowerPairing alphaMinus φ‖ ≤ C * y ^ normalizedDecayGap := by
    filter_upwards [self_mem_nhdsWithin, hupper] with y hy hy1
    exact normalizedTest_coefficient_budget hclass hbound (⟨y, hy⟩ : PositiveHeight) hy1.le
  have hle : ‖B‖ * ‖heightPowerPairing alphaMinus φ‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hright hbudget
  have hzero : ‖B‖ * ‖heightPowerPairing alphaMinus φ‖ = 0 :=
    le_antisymm hle (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hBnorm : ‖B‖ = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (norm_ne_zero_iff.mpr hmoment)
  exact norm_eq_zero.mp hBnorm

/-- Needed scalar input variant: tail physical L2 plus the geometric
normalized-test bound suffice; pointwise small-y growth is absent. -/
theorem shiftOneEuler_normalizedTest_unique (f : ℝ → ℂ)
    (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)))
    (hODE : ∀ y : ℝ, 0 < y → deriv (deriv f) y = f y / (y : ℂ) ^ 2)
    (hL2 : MemLp f 2 physicalTailMeasure)
    (φ : PositiveHeight → ℂ) (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    (hmoment : heightPowerPairing alphaMinus φ ≠ 0)
    (C : ℝ) (hbound : NormalizedEulerTestBound C φ f) :
    ∀ y : ℝ, 0 < y → f y = 0 := by
  have htests := fun t : PositiveHeight => normalizedHeightProfilePairing_integrable
    t hφ hcompact hC2.continuousOn
  obtain ⟨B, hclass⟩ := shiftOneEuler_tail_selection f hC2 hODE hL2
  have hB := decayingCoefficient_zero_of_normalizedTests hclass hmoment hbound
  intro y hy
  simpa only [hB, zero_mul] using hclass y hy

theorem physical_shiftOne_deficiency_normalizedTest_unique (f : ℝ → ℂ)
    (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)))
    (hODE : ∀ y : ℝ, 0 < y → -((y : ℂ) ^ 2) * deriv (deriv f) y + f y = 0)
    (hL2 : MemLp f 2 physicalTailMeasure)
    (φ : PositiveHeight → ℂ) (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    (hmoment : heightPowerPairing alphaMinus φ ≠ 0)
    (C : ℝ) (hbound : NormalizedEulerTestBound C φ f) :
    ∀ y : ℝ, 0 < y → f y = 0 := by
  apply shiftOneEuler_normalizedTest_unique f hC2 _ hL2 φ hφ hcompact hmoment C hbound
  intro y hy
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  apply (eq_div_iff (pow_ne_zero 2 hyC)).mpr
  linear_combination -(hODE y hy)

end
end ImbalancedChen.Part3.ShiftOneEulerNormalizedTestUniqueness20261026b
