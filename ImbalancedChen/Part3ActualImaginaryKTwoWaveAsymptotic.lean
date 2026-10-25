import ImbalancedChen.Part3ImaginaryKWaveCoefficients
import ImbalancedChen.Part3ActualImaginaryKIConnection
import Mathlib.Tactic

/-!
# Two-wave asymptotics of the actual imaginary-order K integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual K/I connection is a proved imported theorem, not a hypothesis.
The two actual I-series remainders tend to zero; multiplication by the fixed
connection coefficient and exact Gamma reflection then identify the two
waves. The q=exp(r) pullback proves the limit at the left radial endpoint.
The last theorem writes every factor for the original K_(2*i*t) convention.
No canonical KL measure, Plancherel identity, or spectral saving is asserted.
-/

namespace ImbalancedChen.Part3.ActualImaginaryKTwoWaveAsymptotic20261025a

noncomputable section
open Complex Filter Set Topology
open GeneralComplexISeriesSourceOnly GeneralIConjugation20261025a
open ComplexOrderKBridgeSourceOnly ActualImaginaryKIConnectionSourceOnly
open ImaginaryOrderKBesselSourceOnly ImaginaryKWaveCoefficients20261025a

/-- Actual complex K minus its two oscillatory q-waves tends to zero.
Neither the connection nor either leading remainder is assumed. -/
theorem tendsto_complexOrderK_minus_qWaveProfile_zero (tau : ℝ) (htau : tau ≠ 0) :
    Tendsto (fun q : ℝ => complexOrderK ((tau : ℂ) * I) q - qWaveProfile tau q)
      (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun q : ℝ => generalI ((tau : ℂ) * I) q -
      (((q / 2 : ℝ) : ℂ) ^ ((tau : ℂ) * I)) *
        (Complex.Gamma ((tau : ℂ) * I + 1))⁻¹)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_imaginaryI_oscillatory_error_zero tau)
  have hm : Tendsto (fun q : ℝ => generalI (-((tau : ℂ) * I)) q -
      (((q / 2 : ℝ) : ℂ) ^ (-((tau : ℂ) * I))) *
        (Complex.Gamma (1 - (tau : ℂ) * I))⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_zero_iff_norm_tendsto_zero.mpr
      (tendsto_imaginaryI_oscillatory_error_zero (-tau))
    have ho : ((-tau : ℝ) : ℂ) * I = -((tau : ℂ) * I) := by push_cast; ring
    simpa only [ho, show -((tau : ℂ) * I) + 1 = 1 - (tau : ℂ) * I by ring] using h
  have hlin := (hm.sub hp).const_mul (connectionCoefficient tau)
  have hzero : Tendsto
      (fun q : ℝ => connectionCoefficient tau *
        ((generalI (-((tau : ℂ) * I)) q -
          (((q / 2 : ℝ) : ℂ) ^ (-((tau : ℂ) * I))) *
            (Complex.Gamma (1 - (tau : ℂ) * I))⁻¹) -
         (generalI ((tau : ℂ) * I) q -
          (((q / 2 : ℝ) : ℂ) ^ ((tau : ℂ) * I)) *
            (Complex.Gamma ((tau : ℂ) * I + 1))⁻¹)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_zero, mul_zero] using hlin
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [complexOrderK_imaginary_eq_generalI_sub tau htau hq]
  change connectionCoefficient tau * _ =
    connectionCoefficient tau *
      (generalI (-((tau : ℂ) * I)) q - generalI ((tau : ℂ) * I) q) - qWaveProfile tau q
  rw [qWaveProfile, ← connectionCoefficient_mul_gamma_minus_inv,
    ← neg_connectionCoefficient_mul_gamma_plus_inv]
  ring

/-- Genuine left-end radial two-wave asymptotic for the actual integral. -/
theorem tendsto_complexOrderK_log_two_wave_error_zero (tau : ℝ) (htau : tau ≠ 0) :
    Tendsto (fun r : ℝ => complexOrderK ((tau : ℂ) * I) (Real.exp r) - logWaveProfile tau r)
      atBot (𝓝 0) := by
  simpa only [qWaveProfile_exp_eq] using
    (tendsto_complexOrderK_minus_qWaveProfile_zero tau htau).comp Real.tendsto_exp_atBot_nhdsGT

/-- The original cosine-Laplace K_(2*i*t) integral with every coefficient,
power of two, and oscillatory frequency written explicitly. -/
theorem tendsto_original_imaginaryOrderK_log_two_wave_error_zero (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun r : ℝ => (imaginaryOrderK t (Real.exp r) : ℂ) -
      ((Complex.Gamma (((2 * t : ℝ) : ℂ) * I) / 2) *
          (2 : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) *
          Complex.exp (-(((2 * t : ℝ) : ℂ) * I) * (r : ℂ)) +
       (Complex.Gamma (-(((2 * t : ℝ) : ℂ) * I)) / 2) *
          (2 : ℂ) ^ (-(((2 * t : ℝ) : ℂ) * I)) *
          Complex.exp ((((2 * t : ℝ) : ℂ) * I) * (r : ℂ))))
      atBot (𝓝 0) := by
  simpa only [complexOrderK_imaginary, logWaveProfile, waveMinus, wavePlus] using
    tendsto_complexOrderK_log_two_wave_error_zero (2 * t) (mul_ne_zero (by norm_num) ht)

end
end ImbalancedChen.Part3.ActualImaginaryKTwoWaveAsymptotic20261025a
