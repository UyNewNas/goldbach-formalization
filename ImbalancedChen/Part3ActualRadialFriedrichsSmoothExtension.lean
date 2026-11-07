import ImbalancedChen.Part3ActualRadialFriedrichsOperator
import ImbalancedChen.Part3CompactCrossGreenIdentity
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The constructed native radial Friedrichs operator extends the literal
compact smooth differential expression -f''+exp(2r)f. The expression is
the existing actual K-radial logarithmic operator, not a newly postulated
operator. Its L2 membership and compact Green identity are proved for
actual core functions. A continuous-linear residual kernel extends the
weak identity from core vectors to their entire actual Hilbert completion.
The constructed Riesz uniqueness then places the differential pair in the
actual native self-adjoint operator graph.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory Set
open ImbalancedChen.Part3.ActualKRadialLogConjugation20261025a

def radialOperatorFunction (T : RadialTest) : ℝ → ℂ := logSchrodinger T.function

theorem radialOperatorFunction_literal (T : RadialTest) (r : ℝ) :
    radialOperatorFunction T r =
      -deriv (deriv T.function) r + (Real.exp (2 * r) : ℂ) * T.function r := by
  simp only [radialOperatorFunction, logSchrodinger, Complex.real_smul]

theorem radialOperatorFunction_memLp (T : RadialTest) :
    MemLp (radialOperatorFunction T) 2 (volume : Measure ℝ) := by
  have hd : ContDiff ℝ ∞ (deriv T.function) := (contDiff_infty_iff_deriv.mp T.smooth).2
  have hdd : Continuous (deriv (deriv T.function)) :=
    (contDiff_infty_iff_deriv.mp hd).2.continuous
  have hM : MemLp (fun r : ℝ => (Real.exp (2 * r) : ℂ) * T.function r) 2 volume :=
    (((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        T.smooth.continuous).memLp_of_hasCompactSupport T.compact.mul_left)
  have hD : MemLp (deriv (deriv T.function)) 2 (volume : Measure ℝ) :=
    hdd.memLp_of_hasCompactSupport T.compact.deriv.deriv
  have heq : radialOperatorFunction T =
      -(deriv (deriv T.function)) +
        (fun r : ℝ => (Real.exp (2 * r) : ℂ) * T.function r) := by
    funext r
    exact radialOperatorFunction_literal T r
  rw [heq]
  exact hD.neg.add hM

def radialOperatorL2 (T : RadialTest) : RadialL2 :=
  (radialOperatorFunction_memLp T).toLp (radialOperatorFunction T)

private theorem actual_radial_toLp_inner (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 volume) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ r : ℝ, star (f r) * g r := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with r hrF hrG
  rw [hrF, hrG]
  simp only [RCLike.inner_apply', Complex.star_def]

private theorem radial_exp_two (r : ℝ) :
    (Real.exp (2 * r) : ℂ) = (Real.exp r : ℂ) ^ 2 := by
  rw [show 2 * r = r + r by ring, Real.exp_add]
  push_cast
  ring

/-- The real exponential potential and the derivative are paired on
the same actual compact functions, with all cross terms retained. -/
theorem actual_radial_operator_core_Green (T U : RadialTest) :
    inner ℂ (radialOperatorL2 T) (radialCoreL2 U) =
      inner ℂ (radialDerivativeL2 T) (radialDerivativeL2 U) +
        inner ℂ (radialExponentialL2 T) (radialExponentialL2 U) := by
  have hT2 : ContDiff ℝ 2 T.function := T.smooth.of_le (by simp)
  have hU2 : ContDiff ℝ 2 U.function := U.smooth.of_le (by simp)
  have hd := (contDiff_infty_iff_deriv.mp T.smooth).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2.continuous
  have hiD : Integrable (fun r : ℝ => star (deriv (deriv T.function) r) * U.function r) :=
    (hdd.star.mul U.smooth.continuous).integrable_of_hasCompactSupport U.compact.mul_left
  have hiE : Integrable (fun r : ℝ =>
      star (exponentialProduct T.function r) * exponentialProduct U.function r) :=
    ((((Complex.continuous_ofReal.comp Real.continuous_exp).mul T.smooth.continuous).star.mul
      ((Complex.continuous_ofReal.comp Real.continuous_exp).mul U.smooth.continuous)).
        integrable_of_hasCompactSupport U.compact.mul_left.mul_left)
  unfold radialOperatorL2 radialCoreL2 radialDerivativeL2 radialExponentialL2
  rw [actual_radial_toLp_inner, actual_radial_toLp_inner, actual_radial_toLp_inner]
  calc
    (∫ r : ℝ, star (radialOperatorFunction T r) * U.function r) =
        ∫ r : ℝ, -(star (deriv (deriv T.function) r) * U.function r) +
          star (exponentialProduct T.function r) * exponentialProduct U.function r := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r => by
        rw [radialOperatorFunction_literal, radial_exp_two]
        simp only [exponentialProduct, star_add, star_neg, star_mul, Complex.star_def,
          map_pow, Complex.conj_ofReal]
        ring
    _ = -(∫ r : ℝ, star (deriv (deriv T.function) r) * U.function r) +
        (∫ r : ℝ, star (exponentialProduct T.function r) * exponentialProduct U.function r) := by
      rw [integral_add hiD.neg hiE, integral_neg]
    _ = (∫ r : ℝ, star (deriv T.function r) * deriv U.function r) +
        (∫ r : ℝ, star (exponentialProduct T.function r) * exponentialProduct U.function r) := by
      rw [ImbalancedChen.Part3.CompactCrossGreenIdentity20261024zz.integral_secondDeriv_star_mul
        T.function U.function hT2 hU2 T.compact U.compact, neg_neg]

def radialCoreEnergyLift (T : RadialTest) : radialClosedEnergyDomain 1 :=
  ⟨radialEnergyCoreVector 1 T,
    (radialEnergyCoreSpan 1).le_topologicalClosure (Submodule.subset_span ⟨T, rfl⟩)⟩

theorem actual_radial_shifted_core_Green (T U : RadialTest) :
    inner ℂ (radialEnergyCoreVector 1 T) (radialEnergyCoreVector 1 U) =
      inner ℂ (radialCoreL2 T + radialOperatorL2 T) (radialCoreL2 U) := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_succ]
  change inner ℂ ((1 : ℂ) • radialCoreL2 T) ((1 : ℂ) • radialCoreL2 U) +
      (inner ℂ (radialDerivativeL2 T) (radialDerivativeL2 U) +
        (inner ℂ (radialExponentialL2 T) (radialExponentialL2 U) + 0)) = _
  simp only [one_smul, add_zero]
  rw [inner_add_left, actual_radial_operator_core_Green]
  ring

/-- A genuine ambient continuous-linear functional; its closed kernel
lets the compact Green identity pass to the completed form domain. -/
def radialCoreWeakResidual (T : RadialTest) : RadialEnergyHilbert →L[ℂ] ℂ :=
  innerSL ℂ (radialEnergyCoreVector 1 T) -
    (innerSL ℂ (radialCoreL2 T + radialOperatorL2 T)).comp (energyPhysicalCoordinate 1)

theorem radialCoreWeakResidual_zero_on_form (T : RadialTest)
    (v : radialClosedEnergyDomain 1) : radialCoreWeakResidual T v = 0 := by
  have hspan : radialEnergyCoreSpan 1 ≤ (radialCoreWeakResidual T).ker := by
    apply Submodule.span_le.2
    rintro _ ⟨U, rfl⟩
    change inner ℂ (radialEnergyCoreVector 1 T) (radialEnergyCoreVector 1 U) -
      inner ℂ (radialCoreL2 T + radialOperatorL2 T)
        (energyPhysicalCoordinate 1 (radialEnergyCoreVector 1 U)) = 0
    rw [energyPhysical_core 1 (by norm_num), actual_radial_shifted_core_Green, sub_self]
  exact (radialEnergyCoreSpan 1).topologicalClosure_minimal hspan
    (radialCoreWeakResidual T).isClosed_ker v.2

theorem radialCoreEnergyLift_is_actual_Riesz_solution (T : RadialTest) :
    radialCoreEnergyLift T = radialFormRieszSolution 1
      (radialCoreL2 T + radialOperatorL2 T) := by
  apply radialFormRieszSolution_unique
  intro v
  exact sub_eq_zero.mp (radialCoreWeakResidual_zero_on_form T v)

/-- Literal compact smooth core extension by the actual native
self-adjoint radial operator. No desired graph inclusion is a premise. -/
theorem actualRadialFriedrichs_extends_logSchrodinger (T : RadialTest) :
    (radialCoreL2 T, radialOperatorL2 T) ∈ actualRadialFriedrichs.graph := by
  apply (actualRadialFriedrichs_graph_iff _ _).2
  change radialPhysicalEmbedding 1
    (radialFormRieszSolution 1 (radialCoreL2 T + radialOperatorL2 T)) = radialCoreL2 T
  rw [← radialCoreEnergyLift_is_actual_Riesz_solution T]
  exact energyPhysical_core 1 (by norm_num) T

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
