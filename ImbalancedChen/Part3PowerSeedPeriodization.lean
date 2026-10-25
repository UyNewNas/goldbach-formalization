import ImbalancedChen.Part3PowerSeedNonzeroFourierK
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Literal integer periodization and Fourier unfolding of the power seed

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The translated seed has locally summable compact norms because its actual
decay is |x|^(-2s), with 2s>1. This proves convergence and supplies the
native interval-tiling Fourier unfolding theorem, rather than assuming a
periodization identity. The resulting coefficient is the literal integral
over [0,1], whose normalization factor is one. Primitive Eisenstein c sums
and their arithmetic weights are not assembled here.
-/

namespace ImbalancedChen.Part3.PowerSeedPeriodization

noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology FourierTransform
open PowerSeedGaussianLaplace PowerSeedFourierLaplaceFubini PowerSeedNonzeroFourierK

def periodizedPowerSeed (s y x : ℝ) : ℝ :=
  ∑' k : ℤ, powerSeed s y (x + (k : ℝ))

theorem powerSeed_nonneg {y : ℝ} (hy : 0 < y) (s x : ℝ) :
    0 ≤ powerSeed s y x := by
  unfold powerSeed
  positivity

theorem powerSeed_continuous (s : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous (powerSeed s y) := by
  unfold powerSeed
  fun_prop (disch := positivity)

def powerSeedMap (s : ℝ) {y : ℝ} (hy : 0 < y) : C(ℝ, ℂ) :=
  ⟨fun x => (powerSeed s y x : ℂ), Complex.continuous_ofReal.comp (powerSeed_continuous s hy)⟩

/-- A quantitative decay inequality for the literal positive seed. -/
theorem powerSeed_le_rpow_tail {s y x : ℝ}
    (hs : 0 < s) (hy : 0 < y) (hx : x ≠ 0) :
    powerSeed s y x ≤ y ^ s * |x| ^ (-(2 * s)) := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hden : (x ^ 2) ^ s ≤ (x ^ 2 + y ^ 2) ^ s :=
    Real.rpow_le_rpow hx2.le (le_add_of_nonneg_right (sq_nonneg y)) hs.le
  calc
    powerSeed s y x ≤ y ^ s / (x ^ 2) ^ s :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le s)
        (Real.rpow_pos_of_pos hx2 s) hden
    _ = y ^ s * |x| ^ (-(2 * s)) := by
      rw [Real.rpow_neg (abs_nonneg x), div_eq_mul_inv]
      congr 2
      rw [← Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]

theorem powerSeedMap_rpow_decay {s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    (powerSeedMap s hy : ℝ → ℂ) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2 * s))) := by
  apply IsBigO.of_bound (y ^ s)
  filter_upwards [show {0}ᶜ ∈ cocompact ℝ from isCompact_singleton.compl_mem_cocompact]
    with x hx
  have hx0 : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
  simpa only [powerSeedMap, ContinuousMap.coe_mk, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (powerSeed_nonneg hy s x),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) (-(2 * s)))] using
    powerSeed_le_rpow_tail hs hy hx0

/-- Uniform summability on every compact is proved before periodization. -/
theorem powerSeed_translates_locally_summable_norm {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun k : ℤ =>
      ‖((powerSeedMap s hy).comp (ContinuousMap.addRight (k : ℝ))).restrict K‖) := by
  have h2s : 1 < 2 * s := by linarith only [hs]
  exact summable_of_isBigO (Real.summable_abs_int_rpow h2s)
    ((isBigO_norm_restrict_cocompact (powerSeedMap s hy) (by linarith only [h2s])
      (powerSeedMap_rpow_decay (by linarith only [hs]) hy) K).comp_tendsto
        Int.tendsto_coe_cofinite)

theorem powerSeed_translates_summable {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) (x : ℝ) :
    Summable (fun k : ℤ => powerSeed s y (x + (k : ℝ))) := by
  apply Complex.summable_ofReal.mp
  have hm := ContinuousMap.summable_of_locally_summable_norm
    (powerSeed_translates_locally_summable_norm hs hy)
  simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    powerSeedMap, ContinuousMap.coe_mk] using (ContinuousMap.hasSum_apply hm.hasSum x).summable

theorem powerSeed_integrable {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) : Integrable (powerSeed s y) := by
  have hc : Integrable (powerSeedMap s hy : ℝ → ℂ) :=
    Real.integrable_of_summable_norm_Icc
      (powerSeed_translates_locally_summable_norm hs hy ⟨Icc 0 1, isCompact_Icc⟩)
  simpa only [powerSeedMap, ContinuousMap.coe_mk, Complex.ofReal_re] using hc.re

/-- Native continuous periodization evaluates to the literal real tsum. -/
theorem continuousMap_periodization_apply {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) (x : ℝ) :
    (∑' k : ℤ, (powerSeedMap s hy).comp (ContinuousMap.addRight (k : ℝ))) x =
      (periodizedPowerSeed s y x : ℂ) := by
  rw [← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
    (powerSeed_translates_locally_summable_norm hs hy))]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, powerSeedMap,
    ContinuousMap.coe_mk, periodizedPowerSeed, Complex.ofReal_tsum]

theorem periodizedPowerSeed_continuous {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) : Continuous (periodizedPowerSeed s y) := by
  have he : periodizedPowerSeed s y = fun x =>
      ((∑' k : ℤ, (powerSeedMap s hy).comp (ContinuousMap.addRight (k : ℝ))) x).re := by
    funext x
    rw [continuousMap_periodization_apply hs hy x, Complex.ofReal_re]
  rw [he]
  exact Complex.continuous_re.comp (map_continuous _)

theorem periodizedPowerSeed_intervalIntegrable {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) :
    IntervalIntegrable (periodizedPowerSeed s y) volume 0 1 :=
  (periodizedPowerSeed_continuous hs hy).intervalIntegrable 0 1

theorem native_fourier_phase (n : ℤ) (x : ℝ) :
    fourier (-n) (x : UnitAddCircle) = fourierPhase n x := by
  rw [fourier_coe_apply]
  unfold fourierPhase
  congr 1
  push_cast
  ring

/-- The integer phase shift used by the native tiling proof is exact. -/
theorem fourierPhase_add_int (n k : ℤ) (x : ℝ) :
    fourierPhase n (x + (k : ℝ)) = fourierPhase n x := by
  have hp : Function.Periodic (fun x : ℝ => fourier (-n) (x : UnitAddCircle)) 1 :=
    Function.Periodic.comp (fun x => AddCircle.coe_add_period 1 x) (fourier (-n))
  simpa only [mul_one, native_fourier_phase] using hp.int_mul k x

/-- Exact unfolding of the normalized period-one coefficient. -/
theorem periodizedPowerSeed_fourier_unfold {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * (periodizedPowerSeed s y x : ℂ)) =
      ∫ x : ℝ, fourierPhase n x * (powerSeed s y x : ℂ) := by
  let f := powerSeedMap s hy
  let F : UnitAddCircle → ℂ := Function.Periodic.lift (f.periodic_tsum_comp_add_zsmul 1)
  have hF (x : ℝ) : F (x : UnitAddCircle) = (periodizedPowerSeed s y x : ℂ) := by
    simp only [F, Function.Periodic.lift_coe, zsmul_one]
    exact continuousMap_periodization_apply hs hy x
  have hcoef := Real.fourierCoeff_tsum_comp_add
    (powerSeed_translates_locally_summable_norm hs hy) n
  change fourierCoeff F n = 𝓕 (f : ℝ → ℂ) (n : ℝ) at hcoef
  rw [fourierCoeff_eq_intervalIntegral F n 0] at hcoef
  simp only [div_one, one_smul, zero_add, smul_eq_mul, native_fourier_phase, hF] at hcoef
  rw [hcoef, fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  change Complex.exp (↑(-2 * Real.pi * x * (n : ℝ)) * Complex.I) *
      (powerSeed s y x : ℂ) = _
  unfold fourierPhase
  congr 2
  push_cast
  ring

/-- The literal periodization therefore has the actual K coefficient at
every nonzero integer mode, with no additional period normalization. -/
theorem periodizedPowerSeed_nonzero_fourier_actualK {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) {n : ℤ} (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * (periodizedPowerSeed s y x : ℂ)) =
      ((2 * Real.pi ^ s / Real.Gamma s * |(n : ℝ)| ^ (s - 1 / 2) * Real.sqrt y *
        RealOrderKExceptionalSourceOnly.realOrderK (s - 1 / 2)
          (2 * Real.pi * |(n : ℝ)| * y) : ℝ) : ℂ) := by
  rw [periodizedPowerSeed_fourier_unfold hs hy n]
  exact powerSeed_nonzero_fourier_actualK hs hy hn

end

end ImbalancedChen.Part3.PowerSeedPeriodization
