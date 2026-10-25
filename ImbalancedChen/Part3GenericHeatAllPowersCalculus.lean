import ImbalancedChen.Part3HeatFactorialScalarBound
import ImbalancedChen.Part3GenericHeatPositiveTimeRegularization

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
All-order positive-time heat multipliers on the genuine generic resolvent.
The polynomial glued exponential proves continuity at the spectral endpoint;
the exponential-series factorial inequality proves every norm bound. The
actual CFC coordinate recurrence gives successive genuine native graph pairs.
The independent one-order smoothing supplier is retained as the n=1 case.
-/

namespace ImbalancedChen.Part3.GenericHeatAllPowersCalculus20261025a
noncomputable section
open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.GenericPositiveResolventHeatGenerator20261025a
open ImbalancedChen.Part3.GenericHeatPositiveTimeRegularization20261025a
open ImbalancedChen.Part3.GenericFriedrichsOperator20261025a
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a
open ImbalancedChen.Part3.HeatFactorialScalarBound20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : ResolventData H)

def heatPowerPolynomial (s : ℝ) (n : ℕ) : ℝ[X] :=
  (Polynomial.C s⁻¹ * Polynomial.X - 1) ^ n

def heatPowerScalar (s : ℝ) (n : ℕ) : C(Spectrum D, ℝ) where
  toFun t := Real.exp s *
    ((heatPowerPolynomial s n).eval (((t : ℝ) / s)⁻¹) * expNegInvGlue ((t : ℝ) / s))
  continuous_toFun := continuous_const.mul
    ((expNegInvGlue.continuous_polynomial_eval_inv_mul (heatPowerPolynomial s n)).comp
      (continuous_subtype_val.div_const s))

theorem heatPowerScalar_zero (s : ℝ) (n : ℕ) {t : Spectrum D} (ht : (t : ℝ) = 0) :
    heatPowerScalar D s n t = 0 := by simp [heatPowerScalar, ht]

theorem heatPowerScalar_apply {s : ℝ} (hs : 0 < s) (n : ℕ)
    {t : Spectrum D} (ht : 0 < (t : ℝ)) :
    heatPowerScalar D s n t = spectralLambda D t ^ n * heatScalar D s t := by
  have hp : (heatPowerPolynomial s n).eval (((t : ℝ) / s)⁻¹) = spectralLambda D t ^ n := by
    rw [heatPowerPolynomial, Polynomial.eval_pow]
    congr 1
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, spectralLambda]
    field_simp [hs.ne', ht.ne'] <;> ring
  change Real.exp s *
    ((heatPowerPolynomial s n).eval (((t : ℝ) / s)⁻¹) * expNegInvGlue ((t : ℝ) / s)) = _
  rw [hp, heatScalar_of_pos D hs]
  change Real.exp s * (spectralLambda D t ^ n * expNegInvGlue ((t : ℝ) / s)) =
    spectralLambda D t ^ n * (Real.exp s * expNegInvGlue ((t : ℝ) / s))
  ring

theorem heatPowerScalar_zero_order {s : ℝ} (hs : 0 < s) :
    heatPowerScalar D s 0 = heatScalar D s := by
  rw [heatScalar_of_pos D hs]
  ext t
  simp [heatPowerScalar, heatPowerPolynomial, positiveHeatScalar]

theorem heatPowerScalar_one_order (s : ℝ) :
    heatPowerScalar D s 1 = heatGeneratorScalar D s := by
  ext t
  simp [heatPowerScalar, heatPowerPolynomial, heatGeneratorScalar]

theorem heatPowerScalar_nonneg_le {s : ℝ} (hs : 0 < s) (n : ℕ) (t : Spectrum D) :
    heatPowerScalar D s n t ∈ Icc (0 : ℝ) ((n.factorial : ℝ) / s ^ n) := by
  by_cases ht : (t : ℝ) = 0
  · rw [heatPowerScalar_zero D s n ht]
    exact ⟨le_rfl, div_nonneg (Nat.cast_nonneg _) (pow_nonneg hs.le n)⟩
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)
    rw [heatPowerScalar_apply D hs n htp, heatScalar_apply_of_pos D hs htp]
    exact ⟨mul_nonneg (pow_nonneg (spectralLambda_nonneg D htp) n) (Real.exp_pos _).le,
      pow_mul_exp_neg_mul_le_factorial_div_pow hs (spectralLambda_nonneg D htp) n⟩

def heatPowerOperator (s : ℝ) (n : ℕ) : H →L[ℂ] H := cfcMap D (heatPowerScalar D s n)

theorem heatPowerOperator_zero_order {s : ℝ} (hs : 0 < s) :
    heatPowerOperator D s 0 = heatOperator D s := by
  unfold heatPowerOperator heatOperator
  rw [heatPowerScalar_zero_order D hs]

theorem heatPowerOperator_one_order (s : ℝ) :
    heatPowerOperator D s 1 = heatGeneratorOperator D s := by
  unfold heatPowerOperator heatGeneratorOperator
  rw [heatPowerScalar_one_order D s]

theorem heatPowerOperator_opNorm_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ‖heatPowerOperator D s n‖ ≤ (n.factorial : ℝ) / s ^ n := by
  change ‖cfcHom D.selfAdjoint (heatPowerScalar D s n)‖ ≤ _
  rw [norm_cfcHom D.R (heatPowerScalar D s n) D.selfAdjoint]
  apply (ContinuousMap.norm_le _ (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hs.le n))).2
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (heatPowerScalar_nonneg_le D hs n t).1]
  exact (heatPowerScalar_nonneg_le D hs n t).2

theorem heatPowerOperator_norm_le {s : ℝ} (hs : 0 < s) (n : ℕ) (f : H) :
    ‖heatPowerOperator D s n f‖ ≤ ((n.factorial : ℝ) / s ^ n) * ‖f‖ :=
  ((heatPowerOperator D s n).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (heatPowerOperator_opNorm_le D hs n) (norm_nonneg f))

/-- The exact recurrence is valid at the zero endpoint as well as every
positive actual spectral coordinate. -/
theorem coordinate_mul_heatPower_add_succ {s : ℝ} (hs : 0 < s) (n : ℕ) :
    coordinate D * (heatPowerScalar D s n + heatPowerScalar D s (n + 1)) =
      heatPowerScalar D s n := by
  ext t
  change (t : ℝ) * (heatPowerScalar D s n t + heatPowerScalar D s (n + 1) t) =
    heatPowerScalar D s n t
  by_cases ht : (t : ℝ) = 0
  · rw [ht, zero_mul, heatPowerScalar_zero D s n ht]
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)
    rw [heatPowerScalar_apply D hs n htp, heatPowerScalar_apply D hs (n + 1) htp]
    have hc : (t : ℝ) * (1 + spectralLambda D t) = 1 := by
      have h := coordinate_mul_spectralLambda D htp
      nlinarith
    calc
      _ = ((t : ℝ) * (1 + spectralLambda D t)) *
          (spectralLambda D t ^ n * heatScalar D s t) := by rw [pow_succ]; ring
      _ = _ := by rw [hc, one_mul]

theorem heatPower_resolvent_recurrence {s : ℝ} (hs : 0 < s) (n : ℕ) :
    D.R * (heatPowerOperator D s n + heatPowerOperator D s (n + 1)) =
      heatPowerOperator D s n := by
  unfold heatPowerOperator
  rw [← cfcMap_coordinate D, ← map_add, ← map_mul, coordinate_mul_heatPower_add_succ D hs n]

theorem heatPower_native_graph {s : ℝ} (hs : 0 < s) (n : ℕ) (f : H) :
    (heatPowerOperator D s n f, heatPowerOperator D s (n + 1) f) ∈ (friedrichsR D.R).graph := by
  apply (friedrichsR_mem_graph_iff D.R D.injective).2
  exact congrArg (fun B : H →L[ℂ] H => B f) (heatPower_resolvent_recurrence D hs n)

end
end ImbalancedChen.Part3.GenericHeatAllPowersCalculus20261025a
