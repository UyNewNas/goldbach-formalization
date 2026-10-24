import ImbalancedChen.Part3CuspConstantModeLogOperator
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24.

Sharpness of the `1/4` vertical Hardy threshold on the compactly
supported positive-height core.  For one fixed nonzero smooth compact
bump `g`, the family is `h_R(y) = sqrt(y) * g(log(y)/R)`, `R > 0`.
The logarithmic-coordinate mass is `R*M`; its vertical energy is
`R*M/4 + D/R`, where `M = ∫ g²` and `D = ∫ (g')²`.
This is a chart and test-function assertion only.  It does not assert
any quotient spectral gap, eigenvalue exclusion, or automorphic claim.
-/

namespace ImbalancedChen.Part3.VerticalHardySharpness20261024zz

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.CuspConstantModeLogOperatorSourceOnly
open ImbalancedChen.Part3.PositiveMultiplicativeLogSourceOnly
open ImbalancedChen.Part3.CuspCylinderMeasure20261024z

def scaledLogProfile (g : ℝ → ℝ) (R : ℝ) (t : ℝ) : ℝ := g (t / R)

def stretchedMode (g : ℝ → ℝ) (R : ℝ) (y : ℝ) : ℝ :=
  constantMode (scaledLogProfile g R) y

theorem scaledLogProfile_deriv (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    {R : ℝ} (hR : R ≠ 0) (t : ℝ) :
    deriv (scaledLogProfile g R) t =
      R⁻¹ * deriv g (t / R) := by
  have hlin : HasDerivAt (fun x : ℝ => x / R) R⁻¹ t := by
    convert (hasDerivAt_id t).mul_const R⁻¹ using 1 <;>
      simp [div_eq_mul_inv]
  convert ((hg (t / R)).hasDerivAt.comp t hlin).deriv using 1 <;>
    simp [scaledLogProfile, Function.comp_def, mul_comm]

theorem scaledLogProfile_contDiff (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) {R : ℝ} (hR : R ≠ 0) :
    ContDiff ℝ 1 (scaledLogProfile g R) := by
  unfold scaledLogProfile
  fun_prop

theorem scaledLogProfile_compact (g : ℝ → ℝ)
    (hgc : HasCompactSupport g) {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (scaledLogProfile g R) := by
  simpa only [scaledLogProfile, div_eq_mul_inv, mul_comm] using
    hgc.comp_smul (inv_ne_zero hR)

/-- Exact change from unweighted physical derivative energy to the
additive logarithmic coordinate. -/
theorem constantMode_vertical_energy (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) :
    (∫ y in Ioi (0 : ℝ), (deriv (constantMode g) y) ^ 2) =
      ∫ t : ℝ, (deriv g t + (1 / 2 : ℝ) * g t) ^ 2 := by
  have hdensity (y : ℝ) (hy : y ∈ Ioi (0 : ℝ)) :
      (deriv (constantMode g) y) ^ 2 =
        y⁻¹ * (deriv g (Real.log y) +
          (1 / 2 : ℝ) * g (Real.log y)) ^ 2 := by
    rw [(constantMode_hasDerivAt g hg.differentiable_one hy).deriv]
    simp only [constantModeFirst, mul_pow]
    have hp : (y ^ (-(1 / 2 : ℝ))) ^ 2 = y⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
      norm_num
    rw [hp]
  have hmeasure :
      (∫ y in Ioi (0 : ℝ),
        y⁻¹ * (deriv g (Real.log y) +
          (1 / 2 : ℝ) * g (Real.log y)) ^ 2) =
      ∫ y : ℝ,
        (deriv g (Real.log y) +
          (1 / 2 : ℝ) * g (Real.log y)) ^ 2
        ∂positiveMultiplicativeMeasure := by
    have hwd := integral_withDensity_eq_integral_toReal_smul
      (μ := (volume : Measure ℝ).restrict (Ioi 0))
      (by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (y⁻¹)))
      (Filter.Eventually.of_forall (fun y : ℝ => ENNReal.ofReal_lt_top))
      (fun y : ℝ =>
        (deriv g (Real.log y) + (1 / 2 : ℝ) * g (Real.log y)) ^ 2)
    rw [positiveMultiplicativeMeasure, hwd]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hy.le)]
    simp only [smul_eq_mul]
  calc
    (∫ y in Ioi (0 : ℝ), (deriv (constantMode g) y) ^ 2) =
        ∫ y in Ioi (0 : ℝ),
          y⁻¹ * (deriv g (Real.log y) +
            (1 / 2 : ℝ) * g (Real.log y)) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact hdensity y hy
    _ = ∫ y : ℝ,
          (deriv g (Real.log y) +
            (1 / 2 : ℝ) * g (Real.log y)) ^ 2
          ∂positiveMultiplicativeMeasure := hmeasure
    _ = ∫ t : ℝ, (deriv g t + (1 / 2 : ℝ) * g t) ^ 2 := by
      rw [← map_exp_volume]
      have hmeas : AEStronglyMeasurable
          (fun y : ℝ =>
            (deriv g (Real.log y) +
              (1 / 2 : ℝ) * g (Real.log y)) ^ 2)
          positiveMultiplicativeMeasure := by
        exact (((hg.continuous_deriv_one.measurable.comp Real.measurable_log).add
          ((hg.continuous.measurable.comp Real.measurable_log).const_mul _)).pow_const 2).aestronglyMeasurable
      rw [integral_map (by fun_prop) hmeas]
      simp only [Real.log_exp]

/-- Compact support eliminates the cross term in the logarithmic
energy.  This is a second actual integration by parts. -/
theorem integral_deriv_mul_self_zero (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ t : ℝ, deriv g t * g t) = 0 := by
  have hgd : Continuous (deriv g) := hg.continuous_deriv_one
  have hi : Integrable (fun t : ℝ => g t * deriv g t) :=
    (hg.continuous.mul hgd).integrable_of_hasCompactSupport
      (hgc.deriv.mul_left)
  have hi' : Integrable (fun t : ℝ => deriv g t * g t) :=
    (hgd.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left)
  have hi0 : Integrable (fun t : ℝ => g t * g t) :=
    (hg.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := g) (u' := deriv g) (v' := deriv g)
    (fun t _ => (hg.differentiable_one t).hasDerivAt)
    (fun t _ => (hg.differentiable_one t).hasDerivAt)
    hi hi' hi0
  have hcomm : (∫ t : ℝ, g t * deriv g t) =
      ∫ t : ℝ, deriv g t * g t := by
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [hcomm] at hibp
  linarith

/-- Exact vertical energy identity for a compact logarithmic profile. -/
theorem constantMode_vertical_energy_split (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ y in Ioi (0 : ℝ), (deriv (constantMode g) y) ^ 2) =
      (1 / 4 : ℝ) * (∫ t : ℝ, (g t) ^ 2) +
        ∫ t : ℝ, (deriv g t) ^ 2 := by
  rw [constantMode_vertical_energy g hg]
  have hgd : Continuous (deriv g) := hg.continuous_deriv_one
  have hgi : Integrable (fun t : ℝ => (g t) ^ 2) := by
    convert (hg.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left) using 1 <;> ext t <;> ring
  have hgdi : Integrable (fun t : ℝ => (deriv g t) ^ 2) := by
    convert (hgd.mul hgd).integrable_of_hasCompactSupport
      (hgc.deriv.mul_left) using 1 <;> ext t <;> ring
  have hcross : Integrable (fun t : ℝ => deriv g t * g t) :=
    (hgd.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left)
  have hpoint (t : ℝ) :
      (deriv g t + (1 / 2 : ℝ) * g t) ^ 2 =
        (deriv g t) ^ 2 + deriv g t * g t +
          (1 / 4 : ℝ) * (g t) ^ 2 := by ring
  simp_rw [hpoint]
  rw [integral_add (hgdi.add hcross) hgi.const_mul,
    integral_add hgdi hcross, integral_const_mul,
    integral_deriv_mul_self_zero g hg hgc]
  ring

theorem scaledLogProfile_mass (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ, (scaledLogProfile g R t) ^ 2) =
      R * ∫ t : ℝ, (g t) ^ 2 := by
  simpa only [scaledLogProfile, div_eq_mul_inv, mul_comm, abs_of_pos hR,
    smul_eq_mul] using
    (Measure.integral_comp_inv_mul_left (fun t : ℝ => (g t) ^ 2) R)

theorem scaledLogProfile_deriv_energy (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ, (deriv (scaledLogProfile g R) t) ^ 2) =
      R⁻¹ * ∫ t : ℝ, (deriv g t) ^ 2 := by
  simp_rw [scaledLogProfile_deriv g hg.differentiable_one hR.ne']
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hscale := Measure.integral_comp_inv_mul_left
    (fun t : ℝ => (deriv g t) ^ 2) R
  simp only [abs_of_pos hR, smul_eq_mul] at hscale
  rw [hscale]
  ring

/-- The requested exact quotient, stated as a cross-multiplied identity
to avoid division by a possibly zero mass for arbitrary `g`. -/
theorem stretchedMode_energy_exact (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (hMpos : 0 < ∫ t : ℝ, (g t) ^ 2)
    {R : ℝ} (hR : 0 < R) :
    (∫ y in Ioi (0 : ℝ), (deriv (stretchedMode g R) y) ^ 2) =
      ((1 / 4 : ℝ) + R⁻² *
        ((∫ t : ℝ, (deriv g t) ^ 2) /
          (∫ t : ℝ, (g t) ^ 2))) *
        (∫ y : PositiveHeight,
          (stretchedMode g R (y : ℝ)) ^ 2 ∂heightMeasure) := by
  have hRprof : ContDiff ℝ 1 (scaledLogProfile g R) :=
    scaledLogProfile_contDiff g hg hR.ne'
  have hRcomp : HasCompactSupport (scaledLogProfile g R) :=
    scaledLogProfile_compact g hgc hR.ne'
  have hmass := constantMode_height_energy
    (scaledLogProfile g R) hRprof.continuous
  have henergy := constantMode_vertical_energy_split
    (scaledLogProfile g R) hRprof hRcomp
  rw [scaledLogProfile_mass g hR,
    scaledLogProfile_deriv_energy g hg hR] at henergy
  rw [hmass, scaledLogProfile_mass g hR]
  rw [henergy]
  field_simp [hMpos.ne', hR.ne']
  ring

/-- Compact support remains strictly inside the positive chart after
logarithmic dilation. -/
theorem stretchedMode_compact_positive (g : ℝ → ℝ)
    (hgc : HasCompactSupport g) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (stretchedMode g R) ∧
      tsupport (stretchedMode g R) ⊆ Ioi (0 : ℝ) := by
  let K : Set ℝ := (fun t : ℝ => Real.exp (R * t)) '' tsupport g
  have hK : IsCompact K := hgc.image (by fun_prop)
  have hKpos : K ⊆ Ioi (0 : ℝ) := by
    rintro y ⟨t, _, rfl⟩
    exact Real.exp_pos _
  have hsupport : Function.support (stretchedMode g R) ⊆ K := by
    intro y hy
    have hprod : Real.sqrt y * g (Real.log y / R) ≠ 0 := by
      change stretchedMode g R y ≠ 0 at hy
      simpa only [stretchedMode, constantMode, scaledLogProfile] using hy
    have hsqrt : Real.sqrt y ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    have hypos : 0 < y := by
      by_contra hn
      exact hsqrt (Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hn))
    have hgval : g (Real.log y / R) ≠ 0 :=
      (mul_ne_zero_iff.mp hprod).2
    have hmem : Real.log y / R ∈ tsupport g :=
      subset_tsupport g hgval
    refine ⟨Real.log y / R, hmem, ?_⟩
    simp only [div_eq_mul_inv]
    rw [show R * (Real.log y * R⁻¹) = Real.log y by
      field_simp [hR.ne']; ring, Real.exp_log hypos]
  have hcomp : HasCompactSupport (stretchedMode g R) :=
    HasCompactSupport.of_support_subset_isCompact hK hsupport
  refine ⟨hcomp, ?_⟩
  exact (closure_minimal hsupport hK.isClosed).trans hKpos

/-- The physical test is smooth on the entire real height axis; it is
identically zero in a neighborhood of every nonpositive height. -/
theorem stretchedMode_contDiff (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (stretchedMode g R) := by
  have hpos := (stretchedMode_compact_positive g hgc hR).2
  have hscaled : ContDiff ℝ ∞ (scaledLogProfile g R) := by
    unfold scaledLogProfile
    fun_prop
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · have hlog : ContDiffAt ℝ ∞ Real.log y :=
      Real.contDiffAt_log.mpr hy.ne'
    have hsqrt : ContDiffAt ℝ ∞ Real.sqrt y :=
      Real.contDiffAt_sqrt hy.ne'
    simpa only [stretchedMode, constantMode, Function.comp_def] using
      hsqrt.mul (hscaled.contDiffAt.comp y hlog)
  · have hout : y ∉ tsupport (stretchedMode g R) := by
      intro hm
      exact (not_lt.mpr (le_of_not_gt hy)) (hpos hm)
    have he : stretchedMode g R =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mp hout
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- One nonzero smooth compact profile is supplied by Mathlib's real
bump function. -/
private def fixedBump : ContDiffBump (0 : ℝ) := default

private theorem fixedBump_smooth : ContDiff ℝ ∞ (fixedBump : ℝ → ℝ) :=
  fixedBump.contDiff

private theorem fixedBump_compact : HasCompactSupport (fixedBump : ℝ → ℝ) :=
  fixedBump.hasCompactSupport

private theorem fixedBump_zero_value : (fixedBump : ℝ → ℝ) 0 = 1 := by
  exact fixedBump.one_of_mem_closedBall (by simp [fixedBump])

private theorem fixedBump_mass_pos :
    0 < ∫ t : ℝ, ((fixedBump : ℝ → ℝ) t) ^ 2 := by
  have hc : Continuous (fun t : ℝ => ((fixedBump : ℝ → ℝ) t) ^ 2) :=
    fixedBump_smooth.continuous.pow 2
  have hcomp : HasCompactSupport
      (fun t : ℝ => ((fixedBump : ℝ → ℝ) t) ^ 2) := by
    convert (fixedBump_compact.mul_right
      (f' := (fixedBump : ℝ → ℝ))) using 1 <;> ext t <;> ring
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcomp
    (fun t => sq_nonneg _)
  simp [fixedBump_zero_value]

/-- Exact quotient for the fixed nonzero bump. -/
theorem fixedBump_sharpness_quotient {R : ℝ} (hR : 0 < R) :
    (∫ y in Ioi (0 : ℝ),
      (deriv (stretchedMode fixedBump R) y) ^ 2) /
      (∫ y : PositiveHeight,
        (stretchedMode fixedBump R (y : ℝ)) ^ 2 ∂heightMeasure) =
      (1 / 4 : ℝ) + R⁻² *
        ((∫ t : ℝ, (deriv (fixedBump : ℝ → ℝ) t) ^ 2) /
          (∫ t : ℝ, ((fixedBump : ℝ → ℝ) t) ^ 2)) := by
  have hmass := constantMode_height_energy
    (scaledLogProfile fixedBump R)
    (scaledLogProfile_contDiff fixedBump
      (fixedBump_smooth.of_le (by norm_num)) hR.ne').continuous
  have hmpos : 0 < ∫ y : PositiveHeight,
      (stretchedMode fixedBump R (y : ℝ)) ^ 2 ∂heightMeasure := by
    rw [hmass, scaledLogProfile_mass fixedBump hR]
    exact mul_pos hR fixedBump_mass_pos
  rw [stretchedMode_energy_exact fixedBump
    (fixedBump_smooth.of_le (by norm_num)) fixedBump_compact
    fixedBump_mass_pos hR]
  exact mul_div_cancel_right₀ _ hmpos.ne'

/-- Arbitrarily close compact smooth positive-height tests show that
`1/4` is the actual threshold for this chart core. -/
theorem exists_compact_test_below_quarter_add (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      ContDiff ℝ ∞ (stretchedMode fixedBump R) ∧
      HasCompactSupport (stretchedMode fixedBump R) ∧
      tsupport (stretchedMode fixedBump R) ⊆ Ioi (0 : ℝ) ∧
      (∫ y in Ioi (0 : ℝ),
        (deriv (stretchedMode fixedBump R) y) ^ 2) <
        ((1 / 4 : ℝ) + ε) *
          (∫ y : PositiveHeight,
            (stretchedMode fixedBump R (y : ℝ)) ^ 2 ∂heightMeasure) := by
  let M : ℝ := ∫ t : ℝ, ((fixedBump : ℝ → ℝ) t) ^ 2
  let D : ℝ := ∫ t : ℝ, (deriv (fixedBump : ℝ → ℝ) t) ^ 2
  have hM : 0 < M := fixedBump_mass_pos
  have hD : 0 ≤ D := integral_nonneg (fun t => sq_nonneg _)
  let R : ℝ := 2 + D / (ε * M)
  have hR : 0 < R := by
    dsimp [R]
    have hq : 0 ≤ D / (ε * M) := div_nonneg hD (mul_pos hε hM).le
    linarith
  have hRgt : 1 < R := by
    dsimp [R]
    have hq : 0 ≤ D / (ε * M) := div_nonneg hD (mul_pos hε hM).le
    linarith
  have hDlt : D < (ε * M) * R := by
    have hq : D / (ε * M) < R := by dsimp [R]; linarith
    exact (div_lt_iff₀ (mul_pos hε hM)).mp hq
  have hRsq : R ≤ R ^ 2 := by nlinarith
  have hDlt2 : D < ε * (M * R ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hRsq (mul_pos hε hM).le]
  have hcoef : R⁻² * (D / M) < ε := by
    have hden : 0 < M * R ^ 2 := mul_pos hM (sq_pos_of_pos hR)
    have heq : R⁻² * (D / M) = D / (M * R ^ 2) := by
      field_simp [hM.ne', hR.ne']
      ring
    rw [heq]
    exact (div_lt_iff₀ hden).2 (by nlinarith [hDlt2])
  refine ⟨R, hR, stretchedMode_contDiff fixedBump fixedBump_smooth
    fixedBump_compact hR, ?_, ?_, ?_⟩
  · exact (stretchedMode_compact_positive fixedBump fixedBump_compact hR).1
  · exact (stretchedMode_compact_positive fixedBump fixedBump_compact hR).2
  · have hexact := stretchedMode_energy_exact fixedBump
      (fixedBump_smooth.of_le (by norm_num)) fixedBump_compact
      fixedBump_mass_pos hR
    have hmass := constantMode_height_energy
      (scaledLogProfile fixedBump R)
      (scaledLogProfile_contDiff fixedBump
        (fixedBump_smooth.of_le (by norm_num)) hR.ne').continuous
    have hmpos : 0 < ∫ y : PositiveHeight,
        (stretchedMode fixedBump R (y : ℝ)) ^ 2 ∂heightMeasure := by
      rw [hmass, scaledLogProfile_mass fixedBump hR]
      exact mul_pos hR hM
    rw [hexact]
    exact (mul_lt_mul_right hmpos).mpr (by dsimp [M, D] at hcoef ⊢; linarith)

end

end ImbalancedChen.Part3.VerticalHardySharpness20261024zz
