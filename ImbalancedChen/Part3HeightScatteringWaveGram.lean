import ImbalancedChen.Part3HeightMellinUnitary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Physical zero-mode scattering-wave cross constants

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The waves below are generalized waves, not square-integrable eigenvectors.
Their pointwise Gram formula displays both direct terms and both cross
terms. For unit-modulus scattering the direct diagonal constant is 2.
The final even-integral identity states the DOMAIN explicitly: full real
line with 1/(4*pi), positive half-line with 1/(2*pi). It supplies no
Eisenstein expansion or completeness theorem.
-/
namespace ImbalancedChen.Part3.HeightScatteringWaveGram20261026b
noncomputable section
open Set MeasureTheory
open HeightMellinUnitary20261026b CuspCylinderMeasure20261024z

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def planeWave (t r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (r : ℂ))

@[simp] theorem planeWave_zero (r : ℝ) : planeWave 0 r = 1 := by
  simp [planeWave]

theorem planeWave_conj_mul (t s r : ℝ) :
    star (planeWave t r) * planeWave s r = planeWave (s - t) r := by
  unfold planeWave
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem heightWave_gram (t s : ℝ) (y : PositiveHeight) :
    star (heightWave t y) * heightWave s y / (y : ℂ) =
      planeWave (s - t) (Real.log (y : ℝ)) := by
  have hy : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr y.property.ne'
  have hsq : (Real.sqrt (y : ℝ) : ℂ) ^ 2 = (y : ℂ) := by
    norm_cast
    exact Real.sq_sqrt y.property.le
  change star ((Real.sqrt (y : ℝ) : ℂ) * planeWave t (Real.log (y : ℝ))) *
    ((Real.sqrt (y : ℝ) : ℂ) * planeWave s (Real.log (y : ℝ))) / (y : ℂ) = _
  rw [Complex.star_def, map_mul, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (y : ℝ) : ℂ) ^ 2 / (y : ℂ)) *
      (star (planeWave t (Real.log (y : ℝ))) *
        planeWave s (Real.log (y : ℝ))) := by ring
    _ = _ := by rw [hsq, div_self hy, one_mul, planeWave_conj_mul]

/-- Reflection interchanges the incoming and outgoing physical waves. -/
theorem heightWave_neg_eq_conj (t : ℝ) (y : PositiveHeight) :
    heightWave (-t) y = star (heightWave t y) := by
  unfold heightWave
  rw [Complex.star_def, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  apply congrArg (fun z : ℂ => (Real.sqrt (y : ℝ) : ℂ) * Complex.exp z)
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring
/-- The original dy/y^2 density leaves exactly dy/y after pairing two
physical sqrt(y) waves. -/
theorem heightWave_gram_density (t s : ℝ) (y : PositiveHeight) :
    (star (heightWave t y) * heightWave s y) * ((1 : ℂ) / (y : ℂ)) ^ 2 =
      planeWave (s - t) (Real.log (y : ℝ)) / (y : ℂ) := by
  rw [← heightWave_gram]
  ring

def scatteringWave (t : ℝ) (c : ℂ) (y : PositiveHeight) : ℂ :=
  heightWave (-t) y + c * heightWave t y

/-- All four terms, including the reflection cross terms. -/
theorem scatteringWave_gram (t s : ℝ) (c d : ℂ) (y : PositiveHeight) :
    star (scatteringWave t c y) * scatteringWave s d y / (y : ℂ) =
      planeWave (t - s) (Real.log (y : ℝ)) +
      d * planeWave (t + s) (Real.log (y : ℝ)) +
      star c * planeWave (-t - s) (Real.log (y : ℝ)) +
      star c * d * planeWave (s - t) (Real.log (y : ℝ)) := by
  have h1 := heightWave_gram (-t) (-s) y
  have h2 := heightWave_gram (-t) s y
  have h3 := heightWave_gram t (-s) y
  have h4 := heightWave_gram t s y
  have e1 : -s - -t = t - s := by ring
  have e2 : s - -t = t + s := by ring
  have e3 : -s - t = -t - s := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [← h1, ← h2, ← h3, ← h4]
  simp only [scatteringWave, Complex.star_def, map_add, map_mul]
  ring

/-- Unit-modulus scattering produces TWO direct diagonal terms. The two
oscillatory cross terms are retained exactly. -/
theorem scatteringWave_diagonal (t : ℝ) (c : ℂ) (hc : ‖c‖ = 1)
    (y : PositiveHeight) :
    star (scatteringWave t c y) * scatteringWave t c y / (y : ℂ) =
      2 + c * planeWave (2 * t) (Real.log (y : ℝ)) +
        star c * planeWave (-2 * t) (Real.log (y : ℝ)) := by
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [scatteringWave_gram]
  have e1 : t - t = 0 := sub_self t
  have e2 : t + t = 2 * t := by ring
  have e3 : -t - t = -2 * t := by ring
  rw [e1, e2, e3, planeWave_zero, hcc]
  ring

/-- Mathlib's period-one horizontal character uses 2*pi*n*x. The height
wave uses the angular variable t with exp(i*t*log y). -/
theorem addCircle_character_angular_frequency (n : ℤ) (x : ℝ) :
    AddCircle.fourier n (x : AddCircle (1 : ℝ)) =
      planeWave (2 * Real.pi * (n : ℝ)) x := by
  rw [AddCircle.fourier_coe_apply]
  unfold planeWave
  congr 1
  push_cast
  ring

/-- For even integrable data, 1/(4*pi) on the FULL real t-line is exactly
1/(2*pi) on t>0. No spectral completeness is used in this identity. -/
theorem full_line_quarter_pi_eq_positive_half_line (g : ℝ → ℝ)
    (hg : Integrable g) (heven : ∀ t, g (-t) = g t) :
    (4 * Real.pi)⁻¹ * (∫ t : ℝ, g t) =
      (2 * Real.pi)⁻¹ * (∫ t in Ioi (0 : ℝ), g t) := by
  let e : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  have hn : MeasurePreserving (fun t : ℝ => -t) volume volume := e.measurePreserving
  have hpre : (fun t : ℝ => -t) ⁻¹' Iio (0 : ℝ) = Ioi (0 : ℝ) := by
    ext t
    simp
  have hnr : MeasurePreserving (fun t : ℝ => -t)
      (volume.restrict (Ioi (0 : ℝ))) (volume.restrict (Iio (0 : ℝ))) := by
    simpa only [hpre] using hn.restrict_preimage measurableSet_Iio
  have hhalf : (∫ t in Iio (0 : ℝ), g t) = ∫ t in Ioi (0 : ℝ), g t := by
    have hh := hnr.integral_comp e.toHomeomorph.measurableEmbedding g
    simpa only [heven] using hh.symm
  have hsum := integral_Iic_add_Ioi (b := (0 : ℝ)) hg.integrableOn hg.integrableOn
  rw [integral_Iic_eq_integral_Iio, hhalf] at hsum
  rw [← hsum]
  field_simp [Real.pi_ne_zero]
  <;> ring

end
end ImbalancedChen.Part3.HeightScatteringWaveGram20261026b


