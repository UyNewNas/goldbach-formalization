import ImbalancedChen.Part3RealBetaHalfLineGamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
The literal zero horizontal Fourier mode of the real power seed.
The square substitution on the positive halfline reduces the integral to
Beta(1/2,s-1/2). Reflection accounts for the negative halfline, and the
positive scale y accounts for the exact y^(1-s) factor. Integrability is
proved from the same Jacobian argument, not assumed as a mode formula.

SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED. No numerical replay.
-/

namespace ImbalancedChen.Part3RealPowerSeedConstantMode

noncomputable section

open Set MeasureTheory
open Part3RealBetaHalfLineGamma

/-- The normalized height-one horizontal seed. -/
def normalized (s x : ℝ) : ℝ := 1 / (1 + x ^ 2) ^ s

/-- The actual real height-y power seed, with real exponents. -/
def powerSeed (s y x : ℝ) : ℝ := y ^ s / (x ^ 2 + y ^ 2) ^ s

def constantFactor (s : ℝ) : ℝ :=
  Real.sqrt Real.pi * Real.Gamma (s - 1 / 2) / Real.Gamma s

private theorem square_injOn : InjOn (fun x : ℝ => x ^ 2) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have h := congrArg Real.sqrt hxy
  simpa only [Real.sqrt_sq hx.le, Real.sqrt_sq hy.le] using h

private theorem square_image : (fun x : ℝ => x ^ 2) '' Ioi (0 : ℝ) = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact pow_pos hx 2
  · intro ht
    exact ⟨Real.sqrt t, Real.sqrt_pos.mpr ht, Real.sq_sqrt ht.le⟩

private theorem square_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_id x).pow 2

/-- The absolute square-substitution Jacobian cancels the half-power
singularity of the actual positive-halfline Beta kernel. -/
private theorem square_beta_kernel (s : ℝ) {x : ℝ} (hx : 0 < x) :
    |2 * x| • ((x ^ 2) ^ ((1 / 2 : ℝ) - 1) /
      (1 + x ^ 2) ^ ((1 / 2 : ℝ) + (s - 1 / 2))) = 2 * normalized s x := by
  have hpow : (x ^ 2) ^ ((1 / 2 : ℝ) - 1) = x⁻¹ := by
    calc
      _ = (x ^ (2 : ℝ)) ^ (-1 / 2 : ℝ) := by
        rw [Real.rpow_two]
        congr 1
        norm_num
      _ = x ^ (-1 : ℝ) := by
        rw [← Real.rpow_mul hx.le]
        congr 1
        norm_num
      _ = x⁻¹ := Real.rpow_neg_one x
  have he : (1 / 2 : ℝ) + (s - 1 / 2) = s := by ring
  have hd : (1 + x ^ 2) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by positivity) s).ne'
  rw [abs_of_pos (mul_pos (by norm_num) hx), smul_eq_mul, hpow, he]
  unfold normalized
  field_simp [hx.ne', hd]
  <;> ring

/-- Integrability on the positive halfline is transported from the
proved Beta kernel with its actual square Jacobian. -/
theorem normalized_integrableOn_positive {s : ℝ} (hs : 1 / 2 < s) :
    IntegrableOn (normalized s) (Ioi (0 : ℝ)) := by
  have hb : 0 < s - 1 / 2 := sub_pos.mpr hs
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi (fun x _ => (square_hasDerivAt x).hasDerivWithinAt)
    square_injOn (fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) /
      (1 + t) ^ ((1 / 2 : ℝ) + (s - 1 / 2)))
  rw [square_image] at hchange
  have hJac := hchange.mp (integrableOn_beta_halfline (by norm_num : 0 < (1 / 2 : ℝ)) hb)
  have htwo : IntegrableOn (fun x : ℝ => 2 * normalized s x) (Ioi 0) :=
    hJac.congr_fun (fun x hx => square_beta_kernel s hx) measurableSet_Ioi
  have h := htwo.const_mul (1 / 2 : ℝ)
  exact h.congr_fun (fun x _ => by ring) measurableSet_Ioi

/-- The negative halfline contributes an integrable reflected copy. -/
theorem normalized_integrableOn_negative {s : ℝ} (hs : 1 / 2 < s) :
    IntegrableOn (normalized s) (Iic (0 : ℝ)) := by
  have hp := normalized_integrableOn_positive hs
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let m : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  rw [m.integrableOn_map_iff]
  simp_rw [Function.comp_def, normalized, neg_sq, neg_preimage, neg_Iic, neg_zero]
  exact integrableOn_Ici_iff_integrableOn_Ioi.mpr hp

theorem normalized_integrable {s : ℝ} (hs : 1 / 2 < s) : Integrable (normalized s) := by
  have h := (normalized_integrableOn_negative hs).union (normalized_integrableOn_positive hs)
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

/-- Exact square-substitution identity before evaluating the Gamma factors. -/
private theorem beta_eq_twice_positive_integral {s : ℝ} (hs : 1 / 2 < s) :
    (∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) /
      (1 + t) ^ ((1 / 2 : ℝ) + (s - 1 / 2))) =
        2 * ∫ x in Ioi (0 : ℝ), normalized s x := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi (fun x _ => (square_hasDerivAt x).hasDerivWithinAt)
    square_injOn (fun t : ℝ => t ^ ((1 / 2 : ℝ) - 1) /
      (1 + t) ^ ((1 / 2 : ℝ) + (s - 1 / 2)))
  rw [square_image] at hchange
  calc
    _ = ∫ x in Ioi (0 : ℝ), |2 * x| •
        ((x ^ 2) ^ ((1 / 2 : ℝ) - 1) /
          (1 + x ^ 2) ^ ((1 / 2 : ℝ) + (s - 1 / 2))) := hchange
    _ = ∫ x in Ioi (0 : ℝ), 2 * normalized s x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact square_beta_kernel s hx
    _ = _ := integral_const_mul _ _

/-- The height-one zero mode includes both real half axes, with no
missing factor of two. Its value is the literal Gamma quotient. -/
theorem integral_normalized {s : ℝ} (hs : 1 / 2 < s) :
    (∫ x : ℝ, normalized s x) = constantFactor s := by
  have hB := integral_beta_halfline_eq_gamma
    (a := (1 / 2 : ℝ)) (b := s - 1 / 2) (by norm_num) (sub_pos.mpr hs)
  have he : (1 / 2 : ℝ) + (s - 1 / 2) = s := by ring

  calc
    _ = ∫ x : ℝ, normalized s |x| := by
      congr 1
      funext x
      simp only [normalized, sq_abs]
    _ = 2 * ∫ x in Ioi (0 : ℝ), normalized s x := integral_comp_abs
    _ = _ := by
      rw [← beta_eq_twice_positive_integral hs]
      simpa only [constantFactor, he, Real.Gamma_one_half_eq] using hB

/-- Exact positive scaling of the horizontal power seed. -/
theorem powerSeed_mul {s y : ℝ} (hy : 0 < y) (x : ℝ) :
    powerSeed s y (y * x) = y ^ (-s) * normalized s x := by
  have hbase : (y * x) ^ 2 + y ^ 2 = y ^ 2 * (1 + x ^ 2) := by ring
  have hpow : (y ^ 2) ^ s = y ^ (2 * s) := by
    rw [Real.rpow_mul hy.le, Real.rpow_two]
  have hcancel : y ^ s / y ^ (2 * s) = y ^ (-s) := by
    rw [← Real.rpow_sub hy]
    congr 1
    ring
  unfold powerSeed normalized
  rw [hbase, Real.mul_rpow (sq_nonneg y) (by positivity), hpow]
  rw [div_mul_eq_div_div, hcancel]
  ring

/-- Absolute integrability of the actual height-y horizontal seed. -/
theorem powerSeed_integrable {s y : ℝ} (hs : 1 / 2 < s) (hy : 0 < y) :
    Integrable (powerSeed s y) := by
  have hscaled : Integrable (fun x : ℝ => powerSeed s y (y * x)) := by
    have h := (normalized_integrable hs).const_mul (y ^ (-s))
    exact h.congr (Filter.Eventually.of_forall (fun x => (powerSeed_mul hy x).symm))
  exact (integrable_comp_mul_left_iff (powerSeed s y) hy.ne').mp hscaled

/-- The actual zero Fourier mode, for every real s>1/2 and height y>0. -/
theorem integral_powerSeed {s y : ℝ} (hs : 1 / 2 < s) (hy : 0 < y) :
    (∫ x : ℝ, y ^ s / (x ^ 2 + y ^ 2) ^ s) =
      (Real.sqrt Real.pi * Real.Gamma (s - 1 / 2) / Real.Gamma s) * y ^ (1 - s) := by
  change (∫ x : ℝ, powerSeed s y x) = constantFactor s * y ^ (1 - s)
  have hchange := Measure.integral_comp_mul_left (powerSeed s y) y
  have hscaled : (∫ x : ℝ, powerSeed s y (y * x)) =
      y ^ (-s) * constantFactor s := by
    simp_rw [powerSeed_mul hy]
    rw [integral_const_mul, integral_normalized hs]
  have hyinv : |y⁻¹| = y⁻¹ := abs_of_pos (inv_pos.mpr hy)
  rw [hyinv, smul_eq_mul, hscaled] at hchange
  have hmul := congrArg (fun z : ℝ => y * z) hchange
  have hprod : y * y ^ (-s) = y ^ (1 - s) := by
    calc
      _ = y ^ (1 : ℝ) * y ^ (-s) := by rw [Real.rpow_one]
      _ = y ^ ((1 : ℝ) + (-s)) := (Real.rpow_add hy 1 (-s)).symm
      _ = y ^ (1 - s) := by congr 1; ring
  simp only [← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul, hprod] at hmul
  simpa only [mul_comm] using hmul.symm

end

end ImbalancedChen.Part3RealPowerSeedConstantMode



