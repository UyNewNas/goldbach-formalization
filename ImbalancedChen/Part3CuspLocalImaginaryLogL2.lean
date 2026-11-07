import ImbalancedChen.Part3CuspLocalFourierBesselJets
import ImbalancedChen.Part3ActualImaginaryFourierLogODE

/-!
# Genuine cusp-local native log ODE and exact physical strip L2 transfer

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original function/PDE/periodicity are assumed ONLY on y>Y>0.
Actual local Bessel jets imply native log jets only on
r>log((2*pi*|n|)Y), through local eventual equality of the true derivative.
Actual horizontal Parseval and product Fubini extract coefficient height
energy from the original strip norm. The existing exact scalar Jacobian
then gives log L2 with no residual frequency scale. No continuation,
regularity or PDE below Y, transformed-L2 premise or held K chain occurs.
-/

namespace ImbalancedChen.Part3.CuspLocalImaginaryLogL220261026b

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
open ActualFourierBesselLogL220261026a ActualImaginaryFourierLogODE20261026b
open CuspLocalFourierCalculus20261026b CuspLocalFourierBesselJets20261026b
open ImaginaryRadialCutoffEnergy20261026b
attribute [local instance] Measure.Subtype.measureSpace

local instance periodCell_finite : IsFiniteMeasure (volume : Measure PeriodCell) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top

private theorem imaginary_parameter (tau : ℝ) :
    (1/4 : ℂ)-((tau : ℂ)*Complex.I)^2=((1/4+tau^2 : ℝ) : ℂ) := by
  rw [mul_pow,Complex.I_sq]
  push_cast
  ring

private theorem imaginary_log_coefficient (tau r : ℝ) :
    ((Real.exp (2*r)-tau^2 : ℝ) : ℂ)=(Real.exp r : ℂ)^2+((tau : ℂ)*Complex.I)^2 := by
  rw [show Real.exp (2*r)=(Real.exp r)^2 by
    rw [show 2*r=r+r by ring,Real.exp_add,pow_two],mul_pow,Complex.I_sq]
  push_cast
  ring

variable {u : ℝ × ℝ → ℂ} {tau Y : ℝ} {n : ℤ}
variable (hY : 0<Y) (hu : ContDiffOn ℝ 2 u (cuspDomain Y))
  (hp : ∀ x y : ℝ, Y<y → u (x+1,y)=u(x,y))
  (hPDE : ∀ p ∈ cuspDomain Y,
    -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p)=
      ((1/4+tau^2 : ℝ) : ℂ)*u p)
  (hn : n≠0)

private theorem exp_in_scaled_tail {r : ℝ} (hr : Real.log (modeFrequency n*Y)<r) :
    modeFrequency n*Y<Real.exp r := by
  have he := Real.exp_lt_exp.mpr hr
  simpa only [Real.exp_log (mul_pos (modeFrequency_pos hn) hY)] using he

/-- Genuine first native log derivative on the precise open cusp tail. -/
theorem localLogMode_hasDerivAt {r : ℝ} (hr : Real.log (modeFrequency n*Y)<r) :
    HasDerivAt (actualFourierLogMode u n)
      (Real.exp r • deriv (actualBesselMode u n) (Real.exp r)) r := by
  have hjet := actual_fourier_bessel_jet_local hY.le hu hp ((tau : ℂ)*Complex.I)
    (by simpa only [imaginary_parameter] using hPDE) hn (exp_in_scaled_tail hY hn hr)
  simpa only [actualFourierLogMode,Function.comp_def] using hjet.1.scomp r (Real.hasDerivAt_exp r)

/-- Genuine second native log derivative is obtained using local
first-derivative equality, not an identity asserted below the cusp. -/
theorem localLogMode_second_hasDerivAt {r : ℝ} (hr : Real.log (modeFrequency n*Y)<r) :
    HasDerivAt (deriv (actualFourierLogMode u n))
      (((Real.exp (2*r)-tau^2 : ℝ) : ℂ)*actualFourierLogMode u n r) r := by
  have heq : deriv (actualFourierLogMode u n)=ᶠ[𝓝 r]
      (fun s => Real.exp s • deriv (actualBesselMode u n) (Real.exp s)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact (localLogMode_hasDerivAt hY hu hp hPDE hn hs).deriv
  have hjet := actual_fourier_bessel_jet_local hY.le hu hp ((tau : ℂ)*Complex.I)
    (by simpa only [imaginary_parameter] using hPDE) hn (exp_in_scaled_tail hY hn hr)
  have hd := (Real.hasDerivAt_exp r).smul (hjet.2.1.scomp r (Real.hasDerivAt_exp r))
  have hnative : HasDerivAt
      (fun s => Real.exp s • deriv (actualBesselMode u n) (Real.exp s))
      (((Real.exp (2*r)-tau^2 : ℝ) : ℂ)*actualFourierLogMode u n r) r := by
    convert hd using 1
    simp only [smul_smul,Complex.real_smul,Complex.ofReal_mul,actualFourierLogMode]
    rw [imaginary_log_coefficient]
    linear_combination -hjet.2.2
  exact hnative.congr_of_eventuallyEq heq

/-- Original cusp-local C2 PDE pays both native radial ODE jets. -/
theorem localLogMode_tailSolution :
    TailSolution tau (Real.log (modeFrequency n*Y)) (actualFourierLogMode u n) := by
  intro r hr
  exact ⟨(localLogMode_hasDerivAt hY hu hp hPDE hn hr).differentiableAt.hasDerivAt,
    localLogMode_second_hasDerivAt hY hu hp hPDE hn hr⟩

/-- Actual fixed-height Parseval bound with only cusp-local continuity. -/
theorem local_coefficient_norm_sq_le_slice {u : ℝ × ℝ → ℂ} {Y y : ℝ}
    (hu : ContinuousOn u (cuspDomain Y)) (n : ℤ) (hy : Y<y) :
    ‖coefficient u n y‖^2≤∫ x : PeriodCell, ‖u (x,y)‖^2 := by
  have hslice := continuous_slice_local hu hy
  have hsq : IntegrableOn (fun x => ‖u (x,y)‖^2) (Ioc (0 : ℝ) 1) :=
    ((hslice.norm.pow 2).intervalIntegrable 0 1).1
  have hlp : MemLp (fun x => u (x,y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hslice.aestronglyMeasurable.restrict).mpr hsq
  have hs := AddCircle.hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ)<1) hlp
  have hb := hs.summable.le_tsum n (fun m _ => sq_nonneg _)
  rw [hs.tsum_eq] at hb
  rw [coefficient_eq_fourierCoeffOn,integral_subtype_comap measurableSet_Icc,integral_Icc_eq_integral_Ioc]
  simpa only [sub_zero,inv_one,one_smul,intervalIntegral.integral_of_le zero_le_one] using hb

/-- Original cusp-local strip L2 pays literal coefficient height energy;
there is no coefficient-L2 or globally smooth extension premise. -/
theorem local_heightEnergy_integrable_of_strip {u : ℝ × ℝ → ℂ} {Y : ℝ}
    (hu : ContinuousOn u (cuspDomain Y)) (hY : 0<Y)
    (hstrip : Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2*‖u (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y)))) (n : ℤ) :
    IntegrableOn (heightEnergy (coefficient u n)) (Ioi Y) := by
  have hc := coefficient_continuousOn_local hu n
  have hcont : ContinuousOn (heightEnergy (coefficient u n)) (Ioi Y) :=
    ((continuousOn_id.inv₀ (fun y hy => (hY.trans hy).ne')).pow 2).mul (hc.norm.pow 2)
  apply hstrip.integral_prod_right.mono_nonneg (hcont.aestronglyMeasurable measurableSet_Ioi)
  · exact Eventually.of_forall (fun y => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (local_coefficient_norm_sq_le_slice hu n hy) (sq_nonneg _)

/-- Exact log-tail L2 obtained from the actual physical cusp strip norm,
with all cutoff endpoints and the true 2*pi*|n| scaling preserved. -/
theorem localLogMode_memLp_two_of_strip
    (hstrip : Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2*‖u (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y)))) :
    MemLp (actualFourierLogMode u n) 2
      (volume.restrict (Ioi (Real.log (modeFrequency n*Y)))) := by
  have hcont : ContinuousOn (actualFourierLogMode u n) (Ioi (Real.log (modeFrequency n*Y))) :=
    fun r hr => (localLogMode_hasDerivAt hY hu hp hPDE hn hr).continuousAt.continuousWithinAt
  apply (memLp_two_iff_integrable_sq_norm (hcont.aestronglyMeasurable measurableSet_Ioi)).mpr
  change IntegrableOn (fun r => ‖logarithmicMode (coefficient u n) (modeFrequency n) r‖^2)
    (Ioi (Real.log (modeFrequency n*Y)))
  apply (logarithmicMode_sq_integrable_iff (coefficient u n) (modeFrequency_pos hn)
    (Real.log (modeFrequency n*Y))).mpr
  simpa only [Real.exp_log (mul_pos (modeFrequency_pos hn) hY),
    mul_div_cancel_left₀ _ (modeFrequency_pos hn).ne'] using
    local_heightEnergy_integrable_of_strip hu.continuousOn hY hstrip n

end
end ImbalancedChen.Part3.CuspLocalImaginaryLogL220261026b
