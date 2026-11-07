import ImbalancedChen.Part3GenericPositiveResolventHeatGenerator
import ImbalancedChen.Part3GenericFriedrichsOperator

/-!
# Genuine positive-time heat regularization into the native operator domain

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

For primitive generic ResolventData H, construct the TRUE continuous
function eta_s(r)=lambda(r) exp(-s lambda(r)), with eta_s(0)=0. The pinned
smooth glued exponential times an inverse polynomial proves continuity at
the zero spectral endpoint. Actual exponential algebra bounds eta_s by
1/s for s>0. Its genuine real CFC is positive and self-adjoint and has norm
at most 1/s. The pointwise coordinate identity proves the actual resolvent
graph pair for EVERY f and hence native friedrichsR domain membership and
its actual output. No smoothing, domain or generator-image premise occurs.

No new heat semigroup, continuity-at-zero or generator-domain theorem is
introduced. Actual Gamma0 form dissipation is a separate binding.
-/

namespace ImbalancedChen.Part3.GenericHeatPositiveTimeRegularization20261025a
noncomputable section
open Set
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.GenericPositiveResolventHeatGenerator20261025a
open ImbalancedChen.Part3.GenericFriedrichsOperator20261025a
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : ResolventData H)

/-- A genuine continuous endpoint extension, built from the native smooth
glue-polynomial theorem rather than assuming continuity of lambda*heat. -/
def heatGeneratorScalar (s : ℝ) : C(Spectrum D, ℝ) where
  toFun t := Real.exp s *
    (((Polynomial.C s⁻¹ * Polynomial.X - 1 : ℝ[X]).eval (((t : ℝ) / s)⁻¹)) *
      expNegInvGlue ((t : ℝ) / s))
  continuous_toFun := continuous_const.mul
    ((expNegInvGlue.continuous_polynomial_eval_inv_mul
      (Polynomial.C s⁻¹ * Polynomial.X - 1)).comp (continuous_subtype_val.div_const s))

theorem heatGeneratorScalar_zero (s : ℝ) {t : Spectrum D} (ht : (t : ℝ) = 0) :
    heatGeneratorScalar D s t = 0 := by
  simp [heatGeneratorScalar,ht]

/-- The constructed continuous scalar is EXACTLY lambda times heat at
every positive coordinate, not merely a majorant. -/
theorem heatGeneratorScalar_apply {s : ℝ} (hs : 0 < s)
    {t : Spectrum D} (ht : 0 < (t : ℝ)) :
    heatGeneratorScalar D s t = spectralLambda D t * heatScalar D s t := by
  have hp : (Polynomial.C s⁻¹ * Polynomial.X - 1 : ℝ[X]).eval (((t : ℝ) / s)⁻¹) =
      spectralLambda D t := by
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_one,spectralLambda]
    field_simp [hs.ne',ht.ne'] <;> ring
  change Real.exp s *
    (((Polynomial.C s⁻¹ * Polynomial.X - 1 : ℝ[X]).eval (((t : ℝ) / s)⁻¹)) *
      expNegInvGlue ((t : ℝ) / s)) = _
  rw [hp,heatScalar_of_pos D hs]
  change Real.exp s * (spectralLambda D t * expNegInvGlue ((t : ℝ) / s)) =
    spectralLambda D t * (Real.exp s * expNegInvGlue ((t : ℝ) / s))
  ring

/-- Elementary scalar decay budget. It comes directly from x<=exp x,
with no assumed spectral or semigroup estimate. -/
theorem mul_exp_neg_mul_le_inv {s : ℝ} (hs : 0 < s) (x : ℝ) :
    x * Real.exp (-s * x) ≤ 1 / s := by
  have hx : s * x ≤ Real.exp (s * x) := by linarith [Real.add_one_le_exp (s * x)]
  have hmul := mul_le_mul_of_nonneg_right hx (Real.exp_pos (-(s * x))).le
  have hexp : Real.exp (s * x) * Real.exp (-(s * x)) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  rw [hexp] at hmul
  have harg : -(s * x) = -s * x := by ring
  rw [harg] at hmul
  apply (le_div_iff₀ hs).mpr
  nlinarith [hmul]

theorem heatGeneratorScalar_nonneg_le {s : ℝ} (hs : 0 < s) (t : Spectrum D) :
    heatGeneratorScalar D s t ∈ Icc (0 : ℝ) (1 / s) := by
  by_cases ht : (t : ℝ) = 0
  · rw [heatGeneratorScalar_zero D s ht]
    exact ⟨le_rfl,one_div_nonneg.mpr hs.le⟩
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)
    rw [heatGeneratorScalar_apply D hs htp,heatScalar_apply_of_pos D hs htp]
    exact ⟨mul_nonneg (spectralLambda_nonneg D htp) (Real.exp_pos _).le,
      mul_exp_neg_mul_le_inv hs (spectralLambda D t)⟩

def heatGeneratorOperator (s : ℝ) : H →L[ℂ] H := cfcMap D (heatGeneratorScalar D s)

theorem heatGeneratorOperator_selfAdjoint (s : ℝ) : IsSelfAdjoint (heatGeneratorOperator D s) :=
  cfcMap_selfAdjoint D (heatGeneratorScalar D s)

theorem heatGeneratorOperator_nonneg {s : ℝ} (hs : 0 < s) :
    (0 : H →L[ℂ] H) ≤ heatGeneratorOperator D s := by
  change 0 ≤ cfcHom D.selfAdjoint (heatGeneratorScalar D s)
  exact (cfcHom_nonneg_iff D.selfAdjoint).mpr (fun t => (heatGeneratorScalar_nonneg_le D hs t).1)

theorem heatGeneratorOperator_positive {s : ℝ} (hs : 0 < s) :
    (heatGeneratorOperator D s).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mp (heatGeneratorOperator_nonneg D hs)

theorem heatGeneratorOperator_opNorm_le {s : ℝ} (hs : 0 < s) :
    ‖heatGeneratorOperator D s‖ ≤ 1 / s := by
  change ‖cfcHom D.selfAdjoint (heatGeneratorScalar D s)‖ ≤ 1 / s
  rw [norm_cfcHom D.R (heatGeneratorScalar D s) D.selfAdjoint]
  apply (ContinuousMap.norm_le _ (one_div_nonneg.mpr hs.le)).mpr
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (heatGeneratorScalar_nonneg_le D hs t).1]
  exact (heatGeneratorScalar_nonneg_le D hs t).2

theorem heatGeneratorOperator_norm_le {s : ℝ} (hs : 0 < s) (f : H) :
    ‖heatGeneratorOperator D s f‖ ≤ ‖f‖ / s := by
  calc
    _ ≤ ‖heatGeneratorOperator D s‖ * ‖f‖ := (heatGeneratorOperator D s).le_opNorm f
    _ ≤ (1 / s) * ‖f‖ := mul_le_mul_of_nonneg_right (heatGeneratorOperator_opNorm_le D hs) (norm_nonneg f)
    _ = _ := by ring

/-- The exact coordinate equation includes the actual spectral endpoint
zero, where both continuous positive-time multipliers vanish. -/
theorem coordinate_mul_heat_plus_generator {s : ℝ} (hs : 0 < s) :
    coordinate D * (heatScalar D s + heatGeneratorScalar D s) = heatScalar D s := by
  ext t
  by_cases ht : (t : ℝ) = 0
  · simp only [ContinuousMap.mul_apply,ContinuousMap.add_apply]
    change (t : ℝ) * (heatScalar D s t + heatGeneratorScalar D s t) = heatScalar D s t
    rw [heatScalar_of_pos D hs,positiveHeatScalar_zero D s ht,ht,zero_mul]
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)
    change (t : ℝ) * (heatScalar D s t + heatGeneratorScalar D s t) = heatScalar D s t
    rw [heatGeneratorScalar_apply D hs htp]
    calc
      _ = ((t : ℝ) + (t : ℝ) * spectralLambda D t) * heatScalar D s t := by ring
      _ = _ := by rw [coordinate_mul_spectralLambda D htp]; ring

theorem heat_resolvent_generator_operator_eq {s : ℝ} (hs : 0 < s) :
    D.R * (heatOperator D s + heatGeneratorOperator D s) = heatOperator D s := by
  unfold heatOperator heatGeneratorOperator
  rw [← cfcMap_coordinate D,← map_add,← map_mul,coordinate_mul_heat_plus_generator D hs]

/-- The genuine positive-time smoothing graph pair for EVERY f. Domain
membership and the exact output are consequences of this equation. -/
theorem heatOperator_generator_graph {s : ℝ} (hs : 0 < s) (f : H) :
    (heatOperator D s f,heatGeneratorOperator D s f) ∈ resolventGraph D.R :=
  congrArg (fun A : H →L[ℂ] H => A f) (heat_resolvent_generator_operator_eq D hs)

theorem heatOperator_friedrichs_graph {s : ℝ} (hs : 0 < s) (f : H) :
    (heatOperator D s f,heatGeneratorOperator D s f) ∈ (friedrichsR D.R).graph :=
  (friedrichsR_mem_graph_iff D.R D.injective).mpr (heatOperator_generator_graph D hs f)

theorem heatOperator_mem_friedrichsDomain {s : ℝ} (hs : 0 < s) (f : H) :
    heatOperator D s f ∈ (friedrichsR D.R).domain :=
  LinearPMap.mem_domain_of_mem_graph (heatOperator_friedrichs_graph D hs f)

def heatDomainVector (s : ℝ) (hs : 0 < s) (f : H) : (friedrichsR D.R).domain :=
  ⟨heatOperator D s f,heatOperator_mem_friedrichsDomain D hs f⟩

theorem friedrichs_heatDomainVector_apply (s : ℝ) (hs : 0 < s) (f : H) :
    friedrichsR D.R (heatDomainVector D s hs f) = heatGeneratorOperator D s f :=
  LinearPMap.mem_graph_snd_inj (friedrichsR D.R)
    (LinearPMap.mem_graph _ (heatDomainVector D s hs f)) (heatOperator_friedrichs_graph D hs f) rfl

theorem friedrichs_heatDomainVector_norm_le (s : ℝ) (hs : 0 < s) (f : H) :
    ‖friedrichsR D.R (heatDomainVector D s hs f)‖ ≤ ‖f‖ / s := by
  rw [friedrichs_heatDomainVector_apply]
  exact heatGeneratorOperator_norm_le D hs f

end
end ImbalancedChen.Part3.GenericHeatPositiveTimeRegularization20261025a
