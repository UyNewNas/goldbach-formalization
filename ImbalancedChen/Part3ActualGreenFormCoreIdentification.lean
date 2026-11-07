import ImbalancedChen.Part3ActualGreenCompactForcing
import ImbalancedChen.Part3RadialClosedHilbertFormRiesz

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual closed radial Riesz inverse and the actual I/K integral agree
on the differential image of the smooth compact core. The Riesz identity
is proved against every completed energy vector using its genuine weak
derivative and exponential graph relations. No form-domain membership of
a general Green convolution is assumed.

The source class is explicitly L(C_c^infty). Density of this differential
image, a bounded Green extension, and equality on arbitrary L2 forcing are
not conclusions of this module.
-/
namespace ImbalancedChen.Part3.ActualGreenFormCoreIdentification20261025a
noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a
open GeneralActualRadialGreenSourceOnly ComplexCompactGreenGluingSourceOnly
open ActualGreenCompactForcing20261025a

def derivativeTest (T : RadialTest) : RadialTest where
  function := deriv T.function
  smooth := (contDiff_infty_iff_deriv.mp T.smooth).2
  compact := T.compact.deriv

def doubleExponentialFunction (T : RadialTest) (r : ℝ) : ℂ :=
  (Real.exp (2 * r) : ℂ) * T.function r

theorem doubleExponential_memLp (T : RadialTest) :
    MemLp (doubleExponentialFunction T) 2 (volume : Measure ℝ) := by
  have hc : Continuous (doubleExponentialFunction T) := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul T.smooth.continuous
  exact hc.memLp_of_hasCompactSupport T.compact.mul_left

def doubleExponentialL2 (T : RadialTest) : RadialL2 :=
  (doubleExponential_memLp T).toLp (doubleExponentialFunction T)

/-- Literal L2 differential forcing associated to a compact smooth test. -/
def radialCoreOperatorL2 (kappa : ℝ) (T : RadialTest) : RadialL2 :=
  (kappa ^ 2 : ℂ) • radialCoreL2 T - radialDerivativeL2 (derivativeTest T) +
    doubleExponentialL2 T

theorem radialCoreOperatorL2_coe (kappa : ℝ) (T : RadialTest) :
    (radialCoreOperatorL2 kappa T : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      operator (potential (kappa : ℂ)) T.function := by
  filter_upwards [Lp.coeFn_add
    ((kappa ^ 2 : ℂ) • radialCoreL2 T - radialDerivativeL2 (derivativeTest T))
    (doubleExponentialL2 T),
    Lp.coeFn_sub ((kappa ^ 2 : ℂ) • radialCoreL2 T)
      (radialDerivativeL2 (derivativeTest T)),
    Lp.coeFn_smul (kappa ^ 2 : ℂ) (radialCoreL2 T),
    T.function_memLp.coeFn_toLp,
    (derivativeTest T).derivative_memLp.coeFn_toLp,
    (doubleExponential_memLp T).coeFn_toLp] with r ha hs hm ht hd he
  change radialCoreOperatorL2 kappa T r = _
  unfold radialCoreOperatorL2
  rw [ha, hs, hm]
  change (kappa ^ 2 : ℂ) * radialCoreL2 T r -
    radialDerivativeL2 (derivativeTest T) r + doubleExponentialL2 T r = _
  rw [ht, hd, he]
  dsimp [derivativeTest, doubleExponentialFunction, operator, potential]
  ring

def radialCoreEnergy (kappa : ℝ) (T : RadialTest) : radialClosedEnergyDomain kappa :=
  ⟨radialEnergyCoreVector kappa T,
    (radialEnergyCoreSpan kappa).le_topologicalClosure
      (Submodule.subset_span ⟨T, rfl⟩)⟩

theorem radialCoreEnergy_physical (kappa : ℝ) (hkappa : 0 < kappa) (T : RadialTest) :
    radialPhysicalEmbedding kappa (radialCoreEnergy kappa T) = radialCoreL2 T :=
  energyPhysical_core kappa hkappa T

theorem radialCoreEnergy_derivative (kappa : ℝ) (T : RadialTest) :
    radialClosedDerivative kappa (radialCoreEnergy kappa T) = radialDerivativeL2 T := rfl

theorem radialCoreEnergy_exponential (kappa : ℝ) (T : RadialTest) :
    radialClosedExponential kappa (radialCoreEnergy kappa T) = radialExponentialL2 T := rfl

/-- Integration by parts holds against the completed energy domain,
because that domain lies in the actual closed weak derivative graph. -/
theorem core_derivative_pairing (kappa : ℝ) (hkappa : 0 < kappa)
    (T : RadialTest) (v : radialClosedEnergyDomain kappa) :
    inner ℂ (radialDerivativeL2 T) (radialClosedDerivative kappa v) =
      -inner ℂ (radialDerivativeL2 (derivativeTest T)) (radialPhysicalEmbedding kappa v) := by
  have h := (radialClosedEnergyDomain_le_good kappa hkappa v.2).1 (derivativeTest T)
  change inner ℂ (radialClosedDerivative kappa v) (radialDerivativeL2 T) =
    -inner ℂ (radialPhysicalEmbedding kappa v) (radialDerivativeL2 (derivativeTest T)) at h
  simpa only [map_neg, inner_conj_symm] using congrArg (starRingEnd ℂ) h

/-- Both exponential factors combine into the literal exp(2r) potential;
the factor on a general form-domain vector is justified by its graph. -/
theorem core_exponential_pairing (kappa : ℝ) (hkappa : 0 < kappa)
    (T : RadialTest) (v : radialClosedEnergyDomain kappa) :
    inner ℂ (radialExponentialL2 T) (radialClosedExponential kappa v) =
      inner ℂ (doubleExponentialL2 T) (radialPhysicalEmbedding kappa v) := by
  have hv := (radialClosedEnergyDomain_le_good kappa hkappa v.2).2
  change (radialClosedExponential kappa v : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
    exponentialProduct (radialPhysicalEmbedding kappa v) at hv
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv, T.exponential_memLp.coeFn_toLp,
    (doubleExponential_memLp T).coeFn_toLp] with r hr hT hD
  rw [hr, hT, hD]
  simp only [RCLike.inner_apply', exponentialProduct, doubleExponentialFunction]
  rw [show 2 * r = r + r by ring, Real.exp_add, Complex.ofReal_mul]
  simp only [map_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem radialCoreEnergy_operator_pairing (kappa : ℝ) (hkappa : 0 < kappa)
    (T : RadialTest) (v : radialClosedEnergyDomain kappa) :
    inner ℂ (radialCoreEnergy kappa T) v =
      inner ℂ (radialCoreOperatorL2 kappa T) (radialPhysicalEmbedding kappa v) := by
  rw [radialClosedEnergy_inner kappa hkappa, radialCoreEnergy_physical kappa hkappa,
    radialCoreEnergy_derivative, radialCoreEnergy_exponential,
    core_derivative_pairing kappa hkappa, core_exponential_pairing kappa hkappa]
  simp only [radialCoreOperatorL2, inner_add_left, inner_sub_left, inner_smul_left,
    map_pow, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The actual form solution of the literal differential forcing is the
actual compact core vector. Uniqueness uses the constructed adjoint Riesz map. -/
theorem radialFormRieszSolution_of_core_operator (kappa : ℝ) (hkappa : 0 < kappa)
    (T : RadialTest) :
    radialFormRieszSolution kappa (radialCoreOperatorL2 kappa T) = radialCoreEnergy kappa T := by
  exact (radialFormRieszSolution_unique kappa (radialCoreOperatorL2 kappa T)
    (radialCoreEnergy kappa T) (radialCoreEnergy_operator_pairing kappa hkappa T)).symm

theorem radialVariationalInverse_of_core_operator (kappa : ℝ) (hkappa : 0 < kappa)
    (T : RadialTest) :
    radialShiftedVariationalInverse kappa (radialCoreOperatorL2 kappa T) = radialCoreL2 T := by
  change radialPhysicalEmbedding kappa
    (radialFormRieszSolution kappa (radialCoreOperatorL2 kappa T)) = _
  rw [radialFormRieszSolution_of_core_operator kappa hkappa]
  exact radialCoreEnergy_physical kappa hkappa T

/-- Actual kernel/form identification on the explicit source class
L(C_c^infty). It does not presume that this source class is dense in L2. -/
theorem actualGreen_eq_form_inverse_on_core_image {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (T : RadialTest) :
    greenForcing (kappa : ℂ) (operator (potential (kappa : ℂ)) T.function) =ᵐ[volume]
      (radialShiftedVariationalInverse kappa (radialCoreOperatorL2 kappa T) : ℝ → ℂ) := by
  rw [radialVariationalInverse_of_core_operator kappa hkappa]
  have he : greenForcing (kappa : ℂ) (operator (potential (kappa : ℂ)) T.function) =
      T.function := by
    funext r
    exact greenForcing_of_operator (by simpa using hkappa) (by simpa using hkappaUpper)
      T.function (T.smooth.of_le (by simp)) T.compact r
  rw [he]
  exact T.function_memLp.coeFn_toLp.symm

end
end ImbalancedChen.Part3.ActualGreenFormCoreIdentification20261025a
