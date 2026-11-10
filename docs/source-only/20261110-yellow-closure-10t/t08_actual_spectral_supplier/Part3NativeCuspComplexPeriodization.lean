import ImbalancedChen.Part3NativeCuspComplexPowerFourier

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- Complex periodization of the literal native cusp power kernel.
-- The complex seed has the exact real power-seed norm. The proved tail
-- gives locally summable compact norms, so native Poisson unfolding
-- evaluates the actual interval coefficient. Translation gives e(+n*a).

namespace ImbalancedChen.Part3.NativeCuspComplexPeriodization20261027

noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology FourierTransform
open ImbalancedChen.Part3.PowerSeedGaussianLaplace
open ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini
open ImbalancedChen.Part3.PowerSeedPeriodization
open ImbalancedChen.Part3.NativeCuspComplexPowerFourier20261027

def complexPowerMap (y : ℝ) (hy : 0 < y) (s : ℂ) : C(ℝ, ℂ) :=
  ⟨complexPowerSeed y s, complexPowerSeed_continuous hy s⟩

def periodizedComplexPowerSeed (y : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  ∑' k : ℤ, complexPowerSeed y s (x + (k : ℝ))

theorem complexPowerMap_rpow_decay {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) :
    (complexPowerMap y hy s : ℝ → ℂ) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2 * s.re))) := by
  apply IsBigO.of_bound (y ^ s.re)
  filter_upwards [show {0}ᶜ ∈ cocompact ℝ from isCompact_singleton.compl_mem_cocompact]
    with x hx
  have hx0 : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
  simpa only [complexPowerMap, ContinuousMap.coe_mk, norm_complexPowerSeed hy,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) (-(2 * s.re)))] using
    powerSeed_le_rpow_tail (by linarith : 0 < s.re) hy hx0

theorem complexPower_translates_locally_summable_norm {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun k : ℤ =>
      ‖((complexPowerMap y hy s).comp (ContinuousMap.addRight (k : ℝ))).restrict K‖) := by
  have h2s : 1 < 2 * s.re := by linarith
  exact summable_of_isBigO (Real.summable_abs_int_rpow h2s)
    ((isBigO_norm_restrict_cocompact (complexPowerMap y hy s) (by linarith only [h2s])
      (complexPowerMap_rpow_decay hy s hs) K).comp_tendsto Int.tendsto_coe_cofinite)

theorem continuousMap_periodization_apply {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    (∑' k : ℤ, (complexPowerMap y hy s).comp (ContinuousMap.addRight (k : ℝ))) x =
      periodizedComplexPowerSeed y s x := by
  rw [← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
    (complexPower_translates_locally_summable_norm hy s hs))]
  rfl

theorem complexPower_translates_summable {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    Summable (fun k : ℤ => complexPowerSeed y s (x + (k : ℝ))) := by
  have hm := ContinuousMap.summable_of_locally_summable_norm
    (complexPower_translates_locally_summable_norm hy s hs)
  simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    complexPowerMap, ContinuousMap.coe_mk] using
    (ContinuousMap.hasSum_apply hm.hasSum x).summable

theorem periodizedComplexPowerSeed_continuous {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) : Continuous (periodizedComplexPowerSeed y s) := by
  have he : periodizedComplexPowerSeed y s = fun x =>
      (∑' k : ℤ, (complexPowerMap y hy s).comp (ContinuousMap.addRight (k : ℝ))) x :=
    funext (fun x => (continuousMap_periodization_apply hy s hs x).symm)
  rw [he]
  exact map_continuous _

theorem periodizedComplexPowerSeed_periodic (y : ℝ) (s : ℂ) :
    Function.Periodic (periodizedComplexPowerSeed y s) 1 := by
  intro x
  change (∑' k : ℤ, complexPowerSeed y s (x + 1 + (k : ℝ))) =
    ∑' k : ℤ, complexPowerSeed y s (x + (k : ℝ))
  calc
    _ = ∑' k : ℤ, complexPowerSeed y s (x + ((k + 1 : ℤ) : ℝ)) := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring
    _ = _ := (Equiv.addRight (1 : ℤ)).tsum_eq _

-- Native normalized Haar interval coefficient, unfolded before evaluation.
theorem periodizedComplexPowerSeed_fourier_unfold {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * periodizedComplexPowerSeed y s x) =
      actualPowerFourier y n s := by
  let f := complexPowerMap y hy s
  let F : UnitAddCircle → ℂ := Function.Periodic.lift (f.periodic_tsum_comp_add_zsmul 1)
  have hF (x : ℝ) : F (x : UnitAddCircle) = periodizedComplexPowerSeed y s x := by
    simp only [F, Function.Periodic.lift_coe, zsmul_one]
    exact continuousMap_periodization_apply hy s hs x
  have hcoef := Real.fourierCoeff_tsum_comp_add
    (complexPower_translates_locally_summable_norm hy s hs) n
  change _root_.fourierCoeff F n = 𝓕 (f : ℝ → ℂ) (n : ℝ) at hcoef
  rw [_root_.fourierCoeff_eq_intervalIntegral F n 0] at hcoef
  simp only [div_one, one_smul, zero_add, smul_eq_mul, native_fourier_phase, hF] at hcoef
  rw [hcoef, fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  change Complex.exp (↑(-2 * Real.pi * x * (n : ℝ)) * Complex.I) *
      complexPowerSeed y s x = fourierPhase n x * complexPowerSeed y s x
  unfold fourierPhase
  congr 2
  push_cast
  ring

theorem shifted_complex_phase_integrable {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (n : ℤ) (a : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => fourierPhase n x * periodizedComplexPowerSeed y s (x + a))
      volume 0 1 := by
  have hp : Continuous (fourierPhase n) := by unfold fourierPhase; fun_prop
  exact (hp.mul ((periodizedComplexPowerSeed_continuous hy s hs).comp
    (continuous_id.add_const a))).intervalIntegrable 0 1

-- The positive arithmetic sign is a consequence of the literal translation.
theorem shifted_periodizedComplexPowerSeed_fourier {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (n : ℤ) (a : ℝ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * periodizedComplexPowerSeed y s (x + a)) =
      fourierPhase (-n) a * actualPowerFourier y n s := by
  have hphase (x : ℝ) :
      fourierPhase n x = fourierPhase (-n) a * fourierPhase n (x + a) := by
    unfold fourierPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hperiod : Function.Periodic
      (fun x : ℝ => fourierPhase n x * periodizedComplexPowerSeed y s x) 1 := by
    intro x
    have hp : fourierPhase n (x + 1) = fourierPhase n x := by
      simpa using fourierPhase_add_int n 1 x
    rw [hp, periodizedComplexPowerSeed_periodic y s x]
  calc
    _ = fourierPhase (-n) a * ∫ x in (0 : ℝ)..1,
        fourierPhase n (x + a) * periodizedComplexPowerSeed y s (x + a) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      rw [hphase]
      ring
    _ = fourierPhase (-n) a * ∫ x in a..a+1,
        fourierPhase n x * periodizedComplexPowerSeed y s x := by
      rw [intervalIntegral.integral_comp_add_right]
      simp only [zero_add, add_comm (1 : ℝ) a]
    _ = fourierPhase (-n) a * ∫ x in (0 : ℝ)..1,
        fourierPhase n x * periodizedComplexPowerSeed y s x := by
      simpa only [zero_add] using congrArg (fun v : ℂ => fourierPhase (-n) a * v)
        (hperiod.intervalIntegral_add_eq a 0)
    _ = _ := by rw [periodizedComplexPowerSeed_fourier_unfold hy s hs]

theorem shifted_periodizedComplexPowerSeed_nonzero {y : ℝ} (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) {n : ℤ} (hn : n ≠ 0) (a : ℝ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * periodizedComplexPowerSeed y s (x + a)) =
      fourierPhase (-n) a * nonzeroKExpression y n s := by
  rw [shifted_periodizedComplexPowerSeed_fourier hy s hs,
    actualPowerFourier_nonzero hy hn s hs]

end
end ImbalancedChen.Part3.NativeCuspComplexPeriodization20261027
