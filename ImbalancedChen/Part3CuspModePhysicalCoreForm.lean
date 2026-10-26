import ImbalancedChen.Part3CuspCylinderBesselMode
import ImbalancedChen.Part3RadialSmoothCoreDerivativeClosure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The physical compact-core part of the nonzero cusp-mode Liouville bridge.
The underlying height measure is the literal dy/y^2 measure. The coordinate
is r=log(2*pi*|n|*y), and the physical function is sqrt(y)*F(r).
Both the hyperbolic pairing and the physical Dirichlet pairing are evaluated
by the one-dimensional Jacobian theorem. Integration by parts cancels the
two mixed terms and produces the quarter shift.

This module does NOT assert a native completed Lp unitary or equality of
closed Friedrichs operators. Those are separate remaining obligations.
No excluded constant-mode or nonzero-mode Liouville supplier is imported.
-/

namespace ImbalancedChen.Part3.CuspModePhysicalCoreForm20261026a
noncomputable section
open Set MeasureTheory Filter
open CuspCylinderMeasure20261024z CuspCylinderBesselMode20261024z
open RadialSchrodingerL2Form20261025a
open scoped Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

def heightChart (a r : ℝ) : ℝ := Real.exp r / a

def physicalLift (a : ℝ) (F : ℝ → ℂ) (y : ℝ) : ℂ :=
  (Real.sqrt y : ℂ) * F (Real.log (a * y))

/-- Signed Fourier character; only the height scaling uses |n|. -/
def physicalMode (n : ℤ) (F : ℝ → ℂ) (z : CuspCylinder) : ℂ :=
  AddCircle.fourier n z.1 * physicalLift (frequencyScale n) F z.2

theorem physicalMode_horizontal_hasDerivAt (n : ℤ) (F : ℝ → ℂ)
    (y : PositiveHeight) (x : ℝ) :
    HasDerivAt (fun x : ℝ => physicalMode n F ((x : AddCircle 1), y))
      ((2 * Real.pi * Complex.I * n : ℂ) *
        physicalMode n F ((x : AddCircle 1), y)) x := by
  simpa [physicalMode, mul_assoc] using
    (AddCircle.hasDerivAt_fourier (1 : ℝ) n x).mul_const
      (physicalLift (frequencyScale n) F y)

theorem physicalMode_norm (n : ℤ) (F : ℝ → ℂ) (z : CuspCylinder) :
    ‖physicalMode n F z‖ = ‖physicalLift (frequencyScale n) F z.2‖ := by
  have h : ‖AddCircle.fourier n z.1‖ = 1 := by
    rw [AddCircle.fourier_apply]
    exact Circle.norm_coe _
  simp [physicalMode, norm_mul, h]

theorem frequencyScale_sq (n : ℤ) :
    frequencyScale n ^ 2 = (2 * Real.pi * (n : ℝ)) ^ 2 := by
  simp only [frequencyScale, mul_pow, sq_abs]

theorem signed_mode_log_coordinate {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    Real.log (frequencyScale n * y) =
      Real.log y + Real.log (2 * Real.pi * |(n : ℝ)|) := by
  rw [Real.log_mul (frequencyScale_pos hn).ne' hy.ne']
  exact add_comm _ _

theorem heightChart_pos {a : ℝ} (ha : 0 < a) (r : ℝ) :
    0 < heightChart a r := div_pos (Real.exp_pos r) ha

theorem heightChart_hasDerivAt {a : ℝ} (ha : 0 < a) (r : ℝ) :
    HasDerivAt (heightChart a) (heightChart a r) r := by
  exact (Real.hasDerivAt_exp r).div_const a

theorem log_heightChart {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Real.log (a * heightChart a r) = r := by
  have h : a * heightChart a r = Real.exp r := by
    unfold heightChart
    field_simp [ha.ne']
  rw [h, Real.log_exp]

theorem heightChart_range {a : ℝ} (ha : 0 < a) :
    heightChart a '' Set.univ = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨r, _, rfl⟩
    exact heightChart_pos ha r
  · intro hy
    refine ⟨Real.log (a * y), Set.mem_univ _, ?_⟩
    simp [heightChart, Real.exp_log (mul_pos ha hy), ha.ne']

theorem heightChart_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective (heightChart a) := by
  intro r s h
  apply Real.exp_injective
  have h' := congrArg (fun z : ℝ => z * a) h
  simpa [heightChart, ha.ne'] using h'

def heightHomeomorph (a : ℝ) (ha : 0 < a) : ℝ ≃ₜ PositiveHeight where
  toFun r := ⟨heightChart a r, heightChart_pos ha r⟩
  invFun y := Real.log (a * (y : ℝ))
  left_inv := log_heightChart ha
  right_inv y := by
    apply Subtype.ext
    simp [heightChart, Real.exp_log (mul_pos ha y.property), ha.ne']
  continuous_toFun := (Real.continuous_exp.div_const a).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).log
    (fun y => (mul_pos ha y.property).ne')

theorem physicalLift_continuous {a : ℝ} (ha : 0 < a) (T : RadialTest) :
    Continuous (fun y : PositiveHeight => physicalLift a T.function y) := by
  exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    continuous_subtype_val)).mul
      (T.smooth.continuous.comp (heightHomeomorph a ha).symm.continuous)

theorem physicalLift_compact {a : ℝ} (ha : 0 < a) (T : RadialTest) :
    HasCompactSupport (fun y : PositiveHeight => physicalLift a T.function y) :=
  (T.compact.comp_homeomorph (heightHomeomorph a ha).symm).mul_left

theorem physicalLift_memLp {a : ℝ} (ha : 0 < a) (T : RadialTest) :
    MemLp (fun y : PositiveHeight => physicalLift a T.function y) 2 heightMeasure :=
  (physicalLift_continuous ha T).memLp_of_hasCompactSupport (physicalLift_compact ha T)

abbrev PhysicalHeightL2 := Lp ℂ 2 heightMeasure

def physicalCoreL2 (a : ℝ) (ha : 0 < a) (T : RadialTest) : PhysicalHeightL2 :=
  (physicalLift_memLp ha T).toLp (fun y : PositiveHeight => physicalLift a T.function y)

/-- Genuine Jacobian substitution; no integrability or substitution premise. -/
theorem physical_height_substitution {a : ℝ} (ha : 0 < a) (g : ℝ → ℂ) :
    (∫ y in Ioi (0 : ℝ), g y) =
      ∫ r : ℝ, (heightChart a r : ℂ) * g (heightChart a r) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_univ
    (fun r _ => (heightChart_hasDerivAt ha r).hasDerivWithinAt)
    (heightChart_injective ha).injOn g
  rw [heightChart_range ha] at h
  simpa only [Measure.restrict_univ, abs_of_pos (heightChart_pos ha _),
    Complex.real_smul] using h

private theorem complex_sqrt_sq {y : ℝ} (hy : 0 < y) :
    (Real.sqrt y : ℂ) ^ 2 = (y : ℂ) := by
  exact_mod_cast Real.sq_sqrt hy.le

theorem physicalLift_hasDerivAt {a y : ℝ} (ha : 0 < a) (hy : 0 < y)
    (F : ℝ → ℂ) (hF : DifferentiableAt ℝ F (Real.log (a * y))) :
    HasDerivAt (physicalLift a F)
      ((Real.sqrt y : ℂ)⁻¹ *
        (deriv F (Real.log (a * y)) + (1 / 2 : ℂ) * F (Real.log (a * y)))) y := by
  have hl : HasDerivAt (fun z : ℝ => Real.log (a * z)) y⁻¹ y := by
    convert (Real.hasDerivAt_log (mul_pos ha hy).ne').comp y
      ((hasDerivAt_id y).const_mul a) using 1
    simp only [mul_one]
    field_simp [ha.ne', hy.ne']
  have h := (Real.hasDerivAt_sqrt hy.ne').ofReal_comp.mul (hF.hasDerivAt.scomp y hl)
  convert h using 1
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.real_smul, Complex.ofReal_inv]
  have hs : (Real.sqrt y : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hy).ne'
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hsq := complex_sqrt_sq hy
  rw [← hsq]
  field_simp [hs] <;> ring

theorem physicalLift_deriv_chart {a : ℝ} (ha : 0 < a) (T : RadialTest) (r : ℝ) :
    deriv (physicalLift a T.function) (heightChart a r) =
      (Real.sqrt (heightChart a r) : ℂ)⁻¹ *
        (deriv T.function r + (1 / 2 : ℂ) * T.function r) := by
  have h := physicalLift_hasDerivAt ha (heightChart_pos ha r) T.function
    (T.smooth.differentiable (by simp) _)
  rw [h.deriv, log_heightChart ha]

def physicalHeightPairing (a : ℝ) (F G : ℝ → ℂ) : ℂ :=
  ∫ y : PositiveHeight, star (physicalLift a F y) * physicalLift a G y ∂heightMeasure

/-- Exact physical hyperbolic inner product, including off-diagonal terms. -/
theorem physicalHeightPairing_eq {a : ℝ} (ha : 0 < a) (F G : ℝ → ℂ) :
    physicalHeightPairing a F G = ∫ r : ℝ, star (F r) * G r := by
  unfold physicalHeightPairing heightMeasure
  rw [integral_withDensity_eq_integral_smul heightDensity_continuous.measurable]
  simp only [NNReal.smul_def, Complex.real_smul, heightDensity_coe]
  rw [integral_subtype measurableSet_Ioi,
    physical_height_substitution ha]
  apply integral_congr_ae
  filter_upwards [] with r
  have hy := heightChart_pos ha r
  have hyc : (heightChart a r : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hsq := complex_sqrt_sq hy
  simp only [physicalLift, log_heightChart ha, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one]
  calc
    _ = ((heightChart a r : ℂ) * (1 / (heightChart a r : ℂ)) ^ 2 *
          (Real.sqrt (heightChart a r) : ℂ) ^ 2) *
        (star (F r) * G r) := by ring
    _ = star (F r) * G r := by rw [hsq]; field_simp [hyc] <;> ring

/-- The unweighted dy Dirichlet energy of the actual signed Fourier mode.
The square of its horizontal derivative is (2*pi*n)^2. -/
def physicalCoreEnergy (n : ℤ) (T U : RadialTest) : ℂ :=
  ∫ y in Ioi (0 : ℝ),
    star (deriv (physicalLift (frequencyScale n) T.function) y) *
      deriv (physicalLift (frequencyScale n) U.function) y +
    (((2 * Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) *
      star (physicalLift (frequencyScale n) T.function y) *
        physicalLift (frequencyScale n) U.function y

private theorem transformed_energy_integrand {n : ℤ} (hn : n ≠ 0)
    (T U : RadialTest) (r : ℝ) :
    let a := frequencyScale n
    let y := heightChart a r
    (y : ℂ) *
      (star (deriv (physicalLift a T.function) y) *
        deriv (physicalLift a U.function) y +
       (((2 * Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) *
        star (physicalLift a T.function y) * physicalLift a U.function y) =
      star (deriv T.function r + (1 / 2 : ℂ) * T.function r) *
        (deriv U.function r + (1 / 2 : ℂ) * U.function r) +
      star (exponentialProduct T.function r) * exponentialProduct U.function r := by
  dsimp only
  have ha := frequencyScale_pos hn
  have hy := heightChart_pos ha r
  rw [physicalLift_deriv_chart ha, physicalLift_deriv_chart ha]
  simp only [physicalLift, log_heightChart ha, exponentialProduct,
    star_mul, star_inv, Complex.star_def, Complex.conj_ofReal]
  rw [← frequencyScale_sq]
  have hsq := complex_sqrt_sq hy
  have hs : (Real.sqrt (heightChart (frequencyScale n) r) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hy).ne'
  have hay : (frequencyScale n : ℂ) * (heightChart (frequencyScale n) r : ℂ) =
      (Real.exp r : ℂ) := by
    norm_cast
    simp [heightChart, ha.ne']
  have hc : (heightChart (frequencyScale n) r : ℂ) *
      (Real.sqrt (heightChart (frequencyScale n) r) : ℂ)⁻¹ *
      (Real.sqrt (heightChart (frequencyScale n) r) : ℂ)⁻¹ = 1 := by
    rw [← hsq]
    field_simp [hs]
  have hp : (frequencyScale n : ℂ) ^ 2 *
      (heightChart (frequencyScale n) r : ℂ) ^ 2 = (Real.exp r : ℂ) ^ 2 := by
    rw [← mul_pow, hay]
  push_cast
  calc
    _ = ((heightChart (frequencyScale n) r : ℂ) *
          (Real.sqrt (heightChart (frequencyScale n) r) : ℂ)⁻¹ *
          (Real.sqrt (heightChart (frequencyScale n) r) : ℂ)⁻¹) *
          (star (deriv T.function r + (1 / 2 : ℂ) * T.function r) *
            (deriv U.function r + (1 / 2 : ℂ) * U.function r)) +
        ((frequencyScale n : ℂ) ^ 2 * (heightChart (frequencyScale n) r : ℂ) *
          (Real.sqrt (heightChart (frequencyScale n) r) : ℂ) ^ 2) *
          (star (T.function r) * U.function r) := by ring
    _ = _ := by
      rw [hc, hsq]
      linear_combination (star (T.function r) * U.function r) * hp

private theorem toLp_pairing (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 volume) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ r : ℝ, star (f r) * g r := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with r hr hg
  rw [hr, hg]
  simp only [RCLike.inner_apply', Complex.star_def]

/-- A native physical Lp identity, not only an equality of formal integrals. -/
theorem physicalCoreL2_inner {a : ℝ} (ha : 0 < a) (T U : RadialTest) :
    inner ℂ (physicalCoreL2 a ha T) (physicalCoreL2 a ha U) =
      inner ℂ (radialCoreL2 T) (radialCoreL2 U) := by
  rw [show inner ℂ (physicalCoreL2 a ha T) (physicalCoreL2 a ha U) =
      physicalHeightPairing a T.function U.function by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(physicalLift_memLp ha T).coeFn_toLp,
      (physicalLift_memLp ha U).coeFn_toLp] with y hT hU
    change inner ℂ ((physicalLift_memLp ha T).toLp _ y)
      ((physicalLift_memLp ha U).toLp _ y) = _
    rw [hT, hU]
    simp only [RCLike.inner_apply', Complex.star_def]]
  rw [physicalHeightPairing_eq ha]
  exact (toLp_pairing _ _ T.function_memLp U.function_memLp).symm

private theorem affine_pairing (T U : RadialTest) :
    (∫ r : ℝ,
      star (deriv T.function r + (1 / 2 : ℂ) * T.function r) *
        (deriv U.function r + (1 / 2 : ℂ) * U.function r)) =
      inner ℂ (radialDerivativeL2 T) (radialDerivativeL2 U) +
        (1 / 4 : ℂ) * inner ℂ (radialCoreL2 T) (radialCoreL2 U) := by
  let f := fun r => deriv T.function r + (1 / 2 : ℂ) * T.function r
  let g := fun r => deriv U.function r + (1 / 2 : ℂ) * U.function r
  have hf : MemLp f 2 volume :=
    T.derivative_memLp.add (T.function_memLp.const_mul _)
  have hg : MemLp g 2 volume :=
    U.derivative_memLp.add (U.function_memLp.const_mul _)
  have hfl : hf.toLp f = radialDerivativeL2 T + (1 / 2 : ℂ) • radialCoreL2 T := rfl
  have hgl : hg.toLp g = radialDerivativeL2 U + (1 / 2 : ℂ) • radialCoreL2 U := rfl
  rw [← toLp_pairing f g hf hg, hfl, hgl]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [radial_core_first_derivative_Green T U]
  norm_num
  ring

/-- Genuine compact-test form conjugacy. The quarter comes from the physical
sqrt(y) factor and actual compact integration by parts, not a supplied identity. -/
theorem physicalCoreEnergy_eq_radial_add_quarter {n : ℤ} (hn : n ≠ 0)
    (T U : RadialTest) :
    physicalCoreEnergy n T U =
      inner ℂ (radialDerivativeL2 T) (radialDerivativeL2 U) +
      inner ℂ (radialExponentialL2 T) (radialExponentialL2 U) +
      (1 / 4 : ℂ) * inner ℂ (radialCoreL2 T) (radialCoreL2 U) := by
  unfold physicalCoreEnergy
  rw [physical_height_substitution (frequencyScale_pos hn)]
  have he : (fun r : ℝ =>
      (heightChart (frequencyScale n) r : ℂ) *
        (star (deriv (physicalLift (frequencyScale n) T.function)
            (heightChart (frequencyScale n) r)) *
          deriv (physicalLift (frequencyScale n) U.function)
            (heightChart (frequencyScale n) r) +
         (((2 * Real.pi * (n : ℝ)) ^ 2 : ℝ) : ℂ) *
          star (physicalLift (frequencyScale n) T.function (heightChart (frequencyScale n) r)) *
          physicalLift (frequencyScale n) U.function (heightChart (frequencyScale n) r))) =
      (fun r =>
        star (deriv T.function r + (1 / 2 : ℂ) * T.function r) *
          (deriv U.function r + (1 / 2 : ℂ) * U.function r) +
        star (exponentialProduct T.function r) * exponentialProduct U.function r) :=
    funext (transformed_energy_integrand hn T U)
  rw [he]
  have hi : Integrable (fun r : ℝ =>
      star (deriv T.function r + (1 / 2 : ℂ) * T.function r) *
        (deriv U.function r + (1 / 2 : ℂ) * U.function r)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (T.derivative_continuous.add (continuous_const.mul T.smooth.continuous)).star.mul
        (U.derivative_continuous.add (continuous_const.mul U.smooth.continuous))
    · exact (U.compact.deriv.add U.compact.mul_left).mul_left
  have hj : Integrable (fun r : ℝ =>
      star (exponentialProduct T.function r) * exponentialProduct U.function r) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((Complex.continuous_ofReal.comp Real.continuous_exp).mul T.smooth.continuous).star.mul
        ((Complex.continuous_ofReal.comp Real.continuous_exp).mul U.smooth.continuous)
    · exact U.compact.mul_left.mul_left
  rw [integral_add hi hj, affine_pairing,
    ← toLp_pairing _ _ T.exponential_memLp U.exponential_memLp]
  change _ + _ = _
  ring

end
end ImbalancedChen.Part3.CuspModePhysicalCoreForm20261026a
