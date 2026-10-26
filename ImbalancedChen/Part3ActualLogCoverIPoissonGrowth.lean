import ImbalancedChen.Part3ActualComplexIPoissonCore
import ImbalancedChen.Part3ActualLogCoverKModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual Poisson representation and growth of the literal logarithmic-cover
I. The physical argument is q=2exp(L), so its HALF argument is exp(L),
and the prefactor is exp(nu*L), without a principal-log substitution.
The actual core Poisson evaluation supplies the representation and its
growth exp(|Re(q)|). A bounded imaginary half-log gives the explicit
radial power |q|^Re(nu). In |Re(nu)|<1/2 the actual I-minus-I definition
then gives nonzero-order K-cover growth. Zero order is deliberately left
to an honest order-derivative/Cauchy estimate in the next leaf.
-/

namespace ImbalancedChen.Part3.ActualLogCoverIPoissonGrowth20261026b

noncomputable section
open Set
open GeneralComplexISeriesSourceOnly GeneralIOrderHolomorphySourceOnly
open ActualComplexIPoissonCore20261026b ActualLogCoverKModel20261026b

def coverPhysicalArgument (L : ℂ) : ℂ := 2 * Complex.exp L

def iPoissonGrowthConstant (nu : ℂ) (T : ℝ) : ℝ :=
  (complexIPoissonNormMass nu / ‖poissonGammaNormalization nu‖) *
    Real.exp (|nu.im| * T - nu.re * Real.log 2)

theorem iPoissonGrowthConstant_nonneg (nu : ℂ) (T : ℝ) :
    0 ≤ iPoissonGrowthConstant nu T :=
  mul_nonneg (div_nonneg (complexIPoissonNormMass_nonneg nu) (norm_nonneg _)) (Real.exp_pos _).le

theorem coverPhysicalArgument_half_square (L : ℂ) :
    (coverPhysicalArgument L / 2) ^ (2 : ℕ) = Complex.exp (2 * L) := by
  have hh : coverPhysicalArgument L / 2 = Complex.exp L := by
    unfold coverPhysicalArgument
    ring
  rw [hh, pow_two, ← Complex.exp_add]
  congr 1
  ring

theorem coverPhysicalArgument_norm (L : ℂ) :
    ‖coverPhysicalArgument L‖ = 2 * Real.exp L.re := by
  norm_num [coverPhysicalArgument, norm_mul, Complex.norm_exp]

theorem coverPhysicalArgument_norm_pos (L : ℂ) : 0 < ‖coverPhysicalArgument L‖ := by
  rw [coverPhysicalArgument_norm]
  positivity

theorem coverPhysicalArgument_log_norm (L : ℂ) :
    Real.log ‖coverPhysicalArgument L‖ = Real.log 2 + L.re := by
  rw [coverPhysicalArgument_norm, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (Real.exp_ne_zero _), Real.log_exp]

/-- Genuine DLMF 10.32.2 on the logarithmic cover. The half-log L is
retained in the power prefactor even if the physical argument crosses
the principal negative cut or makes a full turn. -/
theorem logCoverI_eq_poisson {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re) (L : ℂ) :
    logCoverI nu L = Complex.exp (nu * L) / poissonGammaNormalization nu *
      complexIPoissonIntegral nu (coverPhysicalArgument L) := by
  have hcore := complexIPoissonIntegral_eq_core hnu (coverPhysicalArgument L)
  rw [coverPhysicalArgument_half_square] at hcore
  rw [hcore]
  unfold logCoverI
  field_simp [poissonGammaNormalization_ne_zero hnu] <;> ring

theorem inversePoissonGammaNormalization_continuous :
    Continuous (fun nu : ℂ => (poissonGammaNormalization nu)⁻¹) := by
  have hc : Continuous (fun nu : ℂ => (Complex.Gamma (nu + 1 / 2))⁻¹) :=
    (Complex.differentiable_one_div_Gamma.comp
      (differentiable_id.add (differentiable_const (1 / 2 : ℂ)))).continuous
  simpa only [poissonGammaNormalization, mul_inv_rev] using
    hc.mul_const ((Real.sqrt Real.pi : ℂ)⁻¹)

theorem logCoverI_order_analyticAt (nu L : ℂ) (hnu : -1 < nu.re) :
    AnalyticAt ℂ (fun mu : ℂ => logCoverI mu L) nu := by
  have hp : AnalyticAt ℂ (fun mu : ℂ => Complex.exp (mu * L)) nu :=
    (analyticAt_id.mul analyticAt_const).cexp
  exact hp.mul (analyticAt_generalICore_order nu (Complex.exp (2 * L)) hnu)

/-- Exact phase-sensitive growth before replacing the half-log phase by
a bound. This follows directly from the actual Poisson integral norm. -/
theorem logCoverI_norm_le_exact {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re) (L : ℂ) :
    ‖logCoverI nu L‖ ≤
      (complexIPoissonNormMass nu / ‖poissonGammaNormalization nu‖) *
        Real.exp (nu.re * L.re - nu.im * L.im + |(coverPhysicalArgument L).re|) := by
  rw [logCoverI_eq_poisson hnu L, norm_mul, norm_div, Complex.norm_exp]
  have h := mul_le_mul_of_nonneg_left
    (complexIPoissonIntegral_norm_le hnu (coverPhysicalArgument L))
    (by positivity : 0 ≤ Real.exp ((nu * L).re) / ‖poissonGammaNormalization nu‖)
  calc
    _ ≤ (Real.exp ((nu * L).re) / ‖poissonGammaNormalization nu‖) *
        (Real.exp |(coverPhysicalArgument L).re| * complexIPoissonNormMass nu) := h
    _ = _ := by
      rw [Complex.mul_re, Real.exp_add]
      ring

/-- Actual radial-power growth, uniformly over a prescribed half-log
phase band. The norm power is a positive-real power, not principal cpow. -/
theorem logCoverI_norm_le_bounded_phase {nu L : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) {T : ℝ} (hphase : |L.im| ≤ T) :
    ‖logCoverI nu L‖ ≤ iPoissonGrowthConstant nu T *
      ‖coverPhysicalArgument L‖ ^ nu.re * Real.exp |(coverPhysicalArgument L).re| := by
  have hphaseBound : -nu.im * L.im ≤ |nu.im| * T := by
    calc
      _ ≤ |nu.im * L.im| := by simpa only [neg_mul] using neg_le_abs (nu.im * L.im)
      _ = |nu.im| * |L.im| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hphase (abs_nonneg _)
  have hexp : nu.re * L.re - nu.im * L.im + |(coverPhysicalArgument L).re| ≤
      nu.re * L.re + |nu.im| * T + |(coverPhysicalArgument L).re| := by linarith
  calc
    _ ≤ (complexIPoissonNormMass nu / ‖poissonGammaNormalization nu‖) *
        Real.exp (nu.re * L.re - nu.im * L.im + |(coverPhysicalArgument L).re|) :=
      logCoverI_norm_le_exact hnu L
    _ ≤ (complexIPoissonNormMass nu / ‖poissonGammaNormalization nu‖) *
        Real.exp (nu.re * L.re + |nu.im| * T + |(coverPhysicalArgument L).re|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
        (div_nonneg (complexIPoissonNormMass_nonneg nu) (norm_nonneg _))
    _ = _ := by
      rw [Real.rpow_def_of_pos (coverPhysicalArgument_norm_pos L),
        coverPhysicalArgument_log_norm]
      unfold iPoissonGrowthConstant
      have he : nu.re * L.re + |nu.im| * T + |(coverPhysicalArgument L).re| =
          (|nu.im| * T - nu.re * Real.log 2) +
            (Real.log 2 + L.re) * nu.re + |(coverPhysicalArgument L).re| := by ring
      rw [he]
      simp only [Real.exp_add]
      ring

/-- The actual nonzero-order K cover has polynomial times exponential
growth on bounded phase bands. Both I orders satisfy the exact Poisson
domain; the sine quotient is never evaluated at order zero here. -/
theorem logCoverKNonintegral_norm_le_bounded_phase {nu L : ℂ}
    (hL : -(1 / 2 : ℝ) < nu.re) (hU : nu.re < 1 / 2)
    {T : ℝ} (hphase : |L.im| ≤ T) :
    ‖logCoverKNonintegral nu L‖ ≤ ‖(Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu))‖ *
      (iPoissonGrowthConstant nu T * ‖coverPhysicalArgument L‖ ^ nu.re +
        iPoissonGrowthConstant (-nu) T * ‖coverPhysicalArgument L‖ ^ (-nu.re)) *
      Real.exp |(coverPhysicalArgument L).re| := by
  have hm : -(1 / 2 : ℝ) < (-nu).re := by rw [Complex.neg_re]; linarith
  have hp := logCoverI_norm_le_bounded_phase hL hphase
  have hn := logCoverI_norm_le_bounded_phase hm hphase
  rw [Complex.neg_re] at hn
  have hsub := (norm_sub_le (logCoverI (-nu) L) (logCoverI nu L)).trans (add_le_add hn hp)
  unfold logCoverKNonintegral
  rw [norm_mul]
  calc
    _ ≤ ‖(Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu))‖ *
        (iPoissonGrowthConstant (-nu) T * ‖coverPhysicalArgument L‖ ^ (-nu.re) *
            Real.exp |(coverPhysicalArgument L).re| +
          iPoissonGrowthConstant nu T * ‖coverPhysicalArgument L‖ ^ nu.re *
            Real.exp |(coverPhysicalArgument L).re|) :=
      mul_le_mul_of_nonneg_left hsub (norm_nonneg _)
    _ = _ := by ring

theorem logCoverK_nonzero_norm_le_bounded_phase {nu L : ℂ} (hne : nu ≠ 0)
    (hL : -(1 / 2 : ℝ) < nu.re) (hU : nu.re < 1 / 2)
    {T : ℝ} (hphase : |L.im| ≤ T) :
    ‖logCoverK nu L‖ ≤ ‖(Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu))‖ *
      (iPoissonGrowthConstant nu T * ‖coverPhysicalArgument L‖ ^ nu.re +
        iPoissonGrowthConstant (-nu) T * ‖coverPhysicalArgument L‖ ^ (-nu.re)) *
      Real.exp |(coverPhysicalArgument L).re| := by
  simpa only [logCoverK, if_neg hne] using logCoverKNonintegral_norm_le_bounded_phase hL hU hphase

end
end ImbalancedChen.Part3.ActualLogCoverIPoissonGrowth20261026b
