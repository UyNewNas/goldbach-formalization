import ImbalancedChen.Part3ActualKFluxInfinity
import ImbalancedChen.Part3RadialCuspTailEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24. No acceptance credit.

This continues the actual-K finite radial identity and its proved vanishing
infinity flux. Both terms of the Green identity are separately integrable
on every positive half-line. The K' estimate is derived from its *actual*
cosh-weighted defining integral and the sibling's exponential K0 estimate.
The final equation uses genuine Bochner set integrals over Ioi a; it is not
merely an identity between formal improper limits.
-/

namespace ImbalancedChen.Part3.ActualKHalfLineEnergySourceOnly

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKZeroOrderPositivitySourceOnly
open ImbalancedChen.Part3.RadialCuspTailEnergySourceOnly
open ImbalancedChen.Part3.ActualKRadialEnergyIdentity20261024zz
open ImbalancedChen.Part3.ActualKFluxInfinitySourceOnly

def energyDensity (t q : ℝ) : ℝ :=
  q * (qDerivative t q) ^ 2 + q * (imaginaryOrderK t q) ^ 2

def weightedMassDensity (t q : ℝ) : ℝ :=
  (imaginaryOrderK t q) ^ 2 / q

/-- Exponential decay for the actual q derivative. The first inequality is
the root q-derivative integrand's cosh-exp bound; the second is the sibling's
genuine K0 exponential bound at q/2. -/
theorem qDerivative_exponential (t : ℝ) {q : ℝ} (hq : 0 < q) :
    |qDerivative t q| ≤ (16 / q ^ 2) * Real.exp (-q / 4) := by
  have hhalf : 0 < q / 2 := by linarith
  have hmajor : IntegrableOn
      (fun u : ℝ => (2 / q) * Real.exp (-(q / 2) * Real.cosh u))
      (Ioi 0) := by
    have hzero : IntegrableOn
        (fun u : ℝ => Real.exp (-(q / 2) * Real.cosh u))
        (Ioi 0) := by
      simpa [kIntegrand] using kIntegrand_integrable (0 : ℝ) hhalf
    exact hzero.const_mul (2 / q)
  have hpoint (u : ℝ) :
      ‖qDerivativeIntegrand t q u‖ ≤
        (2 / q) * Real.exp (-(q / 2) * Real.cosh u) := by
    calc
      ‖qDerivativeIntegrand t q u‖ =
          Real.cosh u * Real.exp (-q * Real.cosh u) *
            |Real.cos (2 * t * u)| := by
              simp only [qDerivativeIntegrand, Real.norm_eq_abs, abs_mul,
                abs_neg, abs_of_pos (Real.cosh_pos u),
                abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.cosh u * Real.exp (-q * Real.cosh u) := by
        have hcos := mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one (2 * t * u))
          (mul_nonneg (Real.cosh_pos u).le (Real.exp_pos _).le)
        simpa only [mul_one] using hcos
      _ ≤ (2 / q) * Real.exp (-(q / 2) * Real.cosh u) :=
        cosh_exp_bound hq u
  have hfirst : |qDerivative t q| ≤
      (2 / q) * imaginaryOrderK 0 (q / 2) := by
    calc
      |qDerivative t q| ≤
          ∫ u in Ioi (0 : ℝ),
            (2 / q) * Real.exp (-(q / 2) * Real.cosh u) := by
        simpa only [qDerivative, Real.norm_eq_abs] using
          norm_integral_le_of_norm_le hmajor
            (Filter.Eventually.of_forall hpoint)
      _ = (2 / q) * imaginaryOrderK 0 (q / 2) := by
        rw [integral_const_mul]
        simp [imaginaryOrderK, kIntegrand]
  have hzero := imaginaryOrderK_zero_exponential hhalf
  have hexp : Real.exp (-(q / 2) / 2) = Real.exp (-q / 4) := by
    congr 1
    ring
  calc
    |qDerivative t q| ≤ (2 / q) * imaginaryOrderK 0 (q / 2) := hfirst
    _ ≤ (2 / q) * ((4 / (q / 2)) * Real.exp (-(q / 2) / 2)) :=
      mul_le_mul_of_nonneg_left hzero (by positivity)
    _ = (16 / q ^ 2) * Real.exp (-q / 4) := by
      rw [hexp]
      field_simp [hq.ne']
      ring

private theorem invCube_integrableOn {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun q : ℝ => (q ^ 3)⁻¹) (Ioi a) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ))
    (by norm_num) ha
  simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast] using h

private theorem energyDensity_continuousOn (t : ℝ) :
    ContinuousOn (energyDensity t) (Ioi 0) := by
  have hK : ContinuousOn (imaginaryOrderK t) (Ioi 0) :=
    (imaginaryOrderK_differentiableOn_q t).continuousOn
  have hD := qDerivative_continuousOn t
  exact (continuousOn_id.mul (hD.pow 2)).add
    (continuousOn_id.mul (hK.pow 2))

private theorem weightedMassDensity_continuousOn (t : ℝ) :
    ContinuousOn (weightedMassDensity t) (Ioi 0) := by
  have hK : ContinuousOn (imaginaryOrderK t) (Ioi 0) :=
    (imaginaryOrderK_differentiableOn_q t).continuousOn
  exact (hK.pow 2).div continuousOn_id (fun q hq => hq.ne')

/-- Separate absolute integrability of the weighted K-square mass. -/
theorem weightedMass_integrableOn (t : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (weightedMassDensity t) (Ioi a) := by
  have hmajor : IntegrableOn (fun q : ℝ => 4 * (q ^ 3)⁻¹) (Ioi a) :=
    (invCube_integrableOn ha).const_mul 4
  apply hmajor.mono'
    ((weightedMassDensity_continuousOn t).mono
      (fun q hq => ha.trans hq)).aestronglyMeasurable measurableSet_Ioi
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have hq0 : 0 < q := ha.trans hq
  have hK := ImaginaryOrderKExplicitMajorantSourceOnly.imaginaryOrderK_abs_le t hq0
  have hsq : (imaginaryOrderK t q) ^ 2 ≤ (2 / q) ^ 2 := by
    nlinarith [sq_abs (imaginaryOrderK t q), abs_nonneg (imaginaryOrderK t q)]
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · dsimp [weightedMassDensity]
    calc
      (imaginaryOrderK t q) ^ 2 / q ≤ (2 / q) ^ 2 / q :=
        div_le_div_of_nonneg_right hsq hq0.le
      _ = 4 * (q ^ 3)⁻¹ := by field_simp [hq0.ne']; ring
  · exact div_nonneg (sq_nonneg _) hq0.le

/-- The derivative energy has an inverse-cubic majorant; its proof uses
the actual exponential q-derivative bound, whose exponential is <=1. -/
private theorem derivativeEnergy_integrableOn (t : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun q : ℝ => q * (qDerivative t q) ^ 2) (Ioi a) := by
  have hmajor : IntegrableOn (fun q : ℝ => 256 * (q ^ 3)⁻¹) (Ioi a) :=
    (invCube_integrableOn ha).const_mul 256
  have hcont : ContinuousOn (fun q : ℝ => q * (qDerivative t q) ^ 2)
      (Ioi a) := (continuousOn_id.mul ((qDerivative_continuousOn t).pow 2)).mono
        (fun q hq => ha.trans hq)
  apply hmajor.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have hq0 : 0 < q := ha.trans hq
  have hexp : Real.exp (-q / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hD : |qDerivative t q| ≤ 16 / q ^ 2 :=
    (qDerivative_exponential t hq0).trans (by
      have hcoef : 0 ≤ 16 / q ^ 2 := by positivity
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hcoef)
  have hsq : (qDerivative t q) ^ 2 ≤ (16 / q ^ 2) ^ 2 := by
    nlinarith [sq_abs (qDerivative t q), abs_nonneg (qDerivative t q)]
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      q * (qDerivative t q) ^ 2 ≤ q * (16 / q ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hq0.le
      _ = 256 * (q ^ 3)⁻¹ := by field_simp [hq0.ne']; ring
  · exact mul_nonneg hq0.le (sq_nonneg _)

/-- The K-square term is integrable because the actual zero-order
domination gains exp(-q); the coarse 2/q bound would not suffice here. -/
private theorem kEnergy_integrableOn (t : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun q : ℝ => q * (imaginaryOrderK t q) ^ 2) (Ioi a) := by
  have hmajor : IntegrableOn (fun q : ℝ => (16 / a) * Real.exp (-q))
      (Ioi a) := by
    have hexp : IntegrableOn (fun q : ℝ => Real.exp (-q)) (Ioi a) := by
      simpa only [neg_mul, one_mul] using
        (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) a)
    exact hexp.const_mul (16 / a)
  have hK : ContinuousOn (imaginaryOrderK t) (Ioi 0) :=
    (imaginaryOrderK_differentiableOn_q t).continuousOn
  have hcont : ContinuousOn (fun q : ℝ => q * (imaginaryOrderK t q) ^ 2)
      (Ioi a) := (continuousOn_id.mul (hK.pow 2)).mono
        (fun q hq => ha.trans hq)
  apply hmajor.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have hq0 : 0 < q := ha.trans hq
  have hKexp := imaginaryOrderK_exponential t hq0
  have he : Real.exp (-q / 2) ^ 2 = Real.exp (-q) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : (imaginaryOrderK t q) ^ 2 ≤
      ((4 / q) * Real.exp (-q / 2)) ^ 2 := by
    nlinarith [sq_abs (imaginaryOrderK t q),
      abs_nonneg (imaginaryOrderK t q)]
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      q * (imaginaryOrderK t q) ^ 2 ≤
          q * ((4 / q) * Real.exp (-q / 2)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hq0.le
      _ = (16 / q) * Real.exp (-q) := by
        rw [mul_pow, he]
        field_simp [hq0.ne'] <;> ring
      _ ≤ (16 / a) * Real.exp (-q) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        gcongr
  · exact mul_nonneg hq0.le (sq_nonneg _)

/-- Both actual terms of the radial Green equation are separately Bochner
integrable on every positive half-line. -/
theorem actual_K_energy_and_mass_integrableOn (t : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (energyDensity t) (Ioi a) ∧
      IntegrableOn (weightedMassDensity t) (Ioi a) := by
  exact ⟨(derivativeEnergy_integrableOn t ha).add
    (kEnergy_integrableOn t ha), weightedMass_integrableOn t ha⟩

/-- Half-infinite Green identity as an equality of genuine Bochner set
integrals. The flux at infinity has already been proved to vanish. -/
theorem actual_K_halfLine_Green (t : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ q in Ioi a, energyDensity t q) =
      -kFlux t a + 4 * t ^ 2 *
        (∫ q in Ioi a, weightedMassDensity t q) := by
  have hI := actual_K_energy_and_mass_integrableOn t ha
  have hE : Tendsto (fun b : ℝ => ∫ q in a..b, energyDensity t q)
      atTop (𝓝 (∫ q in Ioi a, energyDensity t q)) :=
    intervalIntegral_tendsto_integral_Ioi a hI.1 tendsto_id
  have hM : Tendsto (fun b : ℝ => ∫ q in a..b, weightedMassDensity t q)
      atTop (𝓝 (∫ q in Ioi a, weightedMassDensity t q)) :=
    intervalIntegral_tendsto_integral_Ioi a hI.2 tendsto_id
  have hEM : Tendsto
      (fun b : ℝ =>
        (∫ q in a..b, energyDensity t q) -
          4 * t ^ 2 * (∫ q in a..b, weightedMassDensity t q))
      atTop
      (𝓝 ((∫ q in Ioi a, energyDensity t q) -
        4 * t ^ 2 * (∫ q in Ioi a, weightedMassDensity t q))) :=
    hE.sub (hM.const_mul (4 * t ^ 2))
  have hflux : Tendsto
      (fun b : ℝ =>
        (∫ q in a..b, energyDensity t q) -
          4 * t ^ 2 * (∫ q in a..b, weightedMassDensity t q))
      atTop (𝓝 (-kFlux t a)) := by
    simpa only [energyDensity, weightedMassDensity] using
      (actual_K_halfLine_Green_limit t ha)
  have hlim := tendsto_nhds_unique hEM hflux
  linarith

end
end ImbalancedChen.Part3.ActualKHalfLineEnergySourceOnly
