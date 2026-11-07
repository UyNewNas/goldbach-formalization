import ImbalancedChen.Part3ComplexContractionResolvent
import ImbalancedChen.Part3GenericComplexCFCScalarMeasure
import ImbalancedChen.Part3GenericResolventScalarMeasure
import ImbalancedChen.Part3ScalarStieltjesPoissonInversion
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
The normalized integrated imaginary part of the ACTUAL complex graph
resolvent is a genuine bounded continuous CFC primitive. Its r-coordinate
kernel is epsilon*r^2/((1-(1+x)r)^2+(epsilon*r)^2), so r=0 is handled
continuously as zero rather than by the false substitution 1/0-1.
Real-CFC continuous linearity proves the actual operator Bochner join.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3.GenericStoneCFCPrimitive20261025a
noncomputable section
open MeasureTheory
open scoped Topology
open ComplexContractionResolvent20261025a GenericComplexCFCScalarMeasure20261025a
open GenericResolventScalarMeasure20261025a ScalarStieltjesPoissonInversion20261025a

def denominator (epsilon x r : ℝ) : ℝ :=
  (1 - (1 + x) * r) ^ 2 + (epsilon * r) ^ 2

def imaginaryKernel (epsilon x r : ℝ) : ℝ := epsilon * r ^ 2 / denominator epsilon x r

theorem denominator_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) (x r : ℝ) :
    0 < denominator epsilon x r := by
  by_cases hr : r = 0
  · simp [denominator, hr]
  · have hs : 0 < (epsilon * r) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hepsilon.ne' hr)
    unfold denominator
    linarith [sq_nonneg (1 - (1 + x) * r)]

theorem imaginaryKernel_continuous {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Continuous (fun p : ℝ × ℝ => imaginaryKernel epsilon p.1 p.2) := by
  unfold imaginaryKernel denominator
  fun_prop (disch := exact (denominator_pos hepsilon _ _).ne')

theorem imaginaryKernel_zero (epsilon x : ℝ) : imaginaryKernel epsilon x 0 = 0 := by
  simp [imaginaryKernel]

/-- Exact imaginary part, including r=0; no spectral identity is a premise. -/
theorem ratio_imaginary {epsilon : ℝ} (hepsilon : 0 < epsilon) (x r : ℝ) :
    (complexResolventRatio ((x : ℂ) + (epsilon : ℂ) * Complex.I) (r : ℂ)).im =
      imaginaryKernel epsilon x r := by
  have hd := (denominator_pos hepsilon x r).ne'
  simp [complexResolventRatio, complexDenominator, imaginaryKernel, denominator,
    Complex.div_im, Complex.normSq_apply] <;> field_simp [hd] <;> ring

def primitiveWeight (a b epsilon r : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ x in a..b, imaginaryKernel epsilon x r

theorem primitiveWeight_continuous (a b : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Continuous (primitiveWeight a b epsilon) := by
  have hh : Continuous (fun p : ℝ × ℝ => imaginaryKernel epsilon p.2 p.1) :=
    (imaginaryKernel_continuous hepsilon).comp (continuous_snd.prodMk continuous_fst)
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r x => imaginaryKernel epsilon x r) hh a b)

theorem primitiveWeight_zero (a b epsilon : ℝ) : primitiveWeight a b epsilon 0 = 0 := by
  simp [primitiveWeight, imaginaryKernel_zero]

/-- The inverse coordinate is used only away from zero, where literal
algebra identifies the integrated kernel with the arctan Poisson weight. -/
theorem primitiveWeight_eq_intervalWeight (a b : ℝ) {epsilon r : ℝ}
    (hepsilon : 0 < epsilon) (hr : r ≠ 0) :
    primitiveWeight a b epsilon r = intervalWeight a b epsilon (r⁻¹ - 1) := by
  rw [primitiveWeight, ← intervalIntegral.integral_const_mul]
  calc
    _ = ∫ x in a..b, poissonKernel epsilon x (r⁻¹ - 1) := by
      apply intervalIntegral.integral_congr
      intro x _
      have hd := (denominator_pos hepsilon x r).ne'
      have hp : ((r⁻¹ - 1 - x) ^ 2 + epsilon ^ 2) ≠ 0 := by positivity
      dsimp only [imaginaryKernel, denominator, poissonKernel]
      field_simp [hr, Real.pi_ne_zero, hd, hp]
      ring
    _ = _ := poissonKernel_intervalIntegral a b hepsilon (r⁻¹ - 1)

theorem primitiveWeight_bounds {a b epsilon : ℝ} (hab : a ≤ b) (hepsilon : 0 < epsilon) (r : ℝ) :
    0 ≤ primitiveWeight a b epsilon r ∧ primitiveWeight a b epsilon r ≤ 1 := by
  by_cases hr : r = 0
  · simp [hr, primitiveWeight_zero]
  · rw [primitiveWeight_eq_intervalWeight a b hepsilon hr]
    exact intervalWeight_nonneg_le_one hab hepsilon _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def kernelMap (epsilon : ℝ) (hepsilon : 0 < epsilon) : C(ℝ × ResolventSpectrum R, ℝ) :=
  ⟨fun p => imaginaryKernel epsilon p.1 (p.2 : ℝ),
    (imaginaryKernel_continuous hepsilon).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩

def primitiveMap (a b epsilon : ℝ) (hepsilon : 0 < epsilon) : C(ResolventSpectrum R, ℝ) :=
  (1 / Real.pi) • ∫ x in a..b, (kernelMap R epsilon hepsilon).curry x

theorem primitiveMap_apply (a b epsilon : ℝ) (hepsilon : 0 < epsilon)
    (r : ResolventSpectrum R) :
    primitiveMap R a b epsilon hepsilon r = primitiveWeight a b epsilon (r : ℝ) := by
  have hi := (kernelMap R epsilon hepsilon).curry.continuous.intervalIntegrable a b
  have he := ((ContinuousMap.evalCLM ℝ r).intervalIntegral_comp_comm hi).symm
  change (1 / Real.pi) * (∫ x in a..b, (kernelMap R epsilon hepsilon).curry x) r = _
  rw [he]
  rfl

def realCFCCLM : C(ResolventSpectrum R, ℝ) →L[ℝ] (H →L[ℂ] H) :=
  (resolventCFC R hSA).toLinearMap.mkContinuous 1 (by
    intro phi
    simpa only [resolventCFC, one_mul] using (norm_cfcHom R phi hSA).le)

def operatorImaginary (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (-Complex.I / 2) • (T - star T)

theorem operatorImaginary_of_decomposition (A B : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    operatorImaginary (A + Complex.I • B) = B := by
  have hc : (-Complex.I / 2) * (Complex.I - -Complex.I) = (1 : ℂ) := by
    norm_num [div_eq_mul_inv, Complex.mul_re, Complex.mul_im]
  simp only [operatorImaginary, star_add, star_smul, hA.star_eq, hB.star_eq,
    Complex.star_def, Complex.conj_I, add_sub_add_left_eq_sub, ← sub_smul, smul_smul]
  rw [hc, one_smul]

theorem actual_resolvent_imaginary {epsilon : ℝ} (hepsilon : 0 < epsilon) (x : ℝ) :
    operatorImaginary (complexResolvent R ((x : ℂ) + (epsilon : ℂ) * Complex.I)) =
      resolventCFC R hSA ((kernelMap R epsilon hepsilon).curry x) := by
  let z : ℂ := (x : ℂ) + (epsilon : ℂ) * Complex.I
  have hz : z.im ≠ 0 := by simpa only [z, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, zero_add, add_zero] using hepsilon.ne'
  have hd : complexResolvent R z =
      cfc (fun t : ℝ => (complexResolventRatio z (t : ℂ)).re) R +
        Complex.I • cfc (fun t : ℝ => (complexResolventRatio z (t : ℂ)).im) R :=
    complex_cfc_eq_real_imag R hSA (complexResolventRatio z)
      (complexResolventRatio_continuousOn R hSA hz)
  rw [hd, operatorImaginary_of_decomposition _ _ (cfc_predicate _ _) (cfc_predicate _ _)]
  have hi : (fun t : ℝ => (complexResolventRatio z (t : ℂ)).im) = imaginaryKernel epsilon x := by
    funext t
    exact ratio_imaginary hepsilon x t
  have hcont : Continuous (imaginaryKernel epsilon x) :=
    (imaginaryKernel_continuous hepsilon).comp (continuous_const.prodMk continuous_id)
  rw [hi, cfc_apply _ R hSA hcont.continuousOn]
  rfl

/-- Actual operator Bochner integration commutes with the bounded real
CFC map; this is an identity, not an assumed operator-join hypothesis. -/
theorem actual_integrated_imaginary_eq_CFC (a b : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (1 / Real.pi : ℝ) • ∫ x in a..b,
      operatorImaginary (complexResolvent R ((x : ℂ) + (epsilon : ℂ) * Complex.I)) =
      resolventCFC R hSA (primitiveMap R a b epsilon hepsilon) := by
  have hi := (kernelMap R epsilon hepsilon).curry.continuous.intervalIntegrable a b
  have he := (realCFCCLM R hSA).intervalIntegral_comp_comm hi
  simp_rw [actual_resolvent_imaginary R hSA hepsilon]
  change (1 / Real.pi : ℝ) • (∫ x in a..b,
      realCFCCLM R hSA ((kernelMap R epsilon hepsilon).curry x)) =
    realCFCCLM R hSA ((1 / Real.pi : ℝ) • ∫ x in a..b, (kernelMap R epsilon hepsilon).curry x)
  rw [he, map_smul]

end
end ImbalancedChen.Part3.GenericStoneCFCPrimitive20261025a
