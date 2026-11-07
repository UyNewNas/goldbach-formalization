import ImbalancedChen.Part3ActualResolventZeroAtomPushforward
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual positive self-adjoint energy resolvent R constructs a heat
semigroup by real continuous functional calculus. For s>0 its continuous
spectral function is exp(s)*expNegInvGlue(t/s), equal to
exp(-s*(1/t-1)) for t>0 and zero at t=0. At s=0 the operator is the identity.
The semigroup law, positivity, self-adjointness and contraction bounds are
proved from these actual functions. Strong convergence to the identity uses
the actual RMK scalar measure, its proved zero endpoint atom, and dominated
convergence applied to the actual squared norm error.

No heat semigroup, strong limit, spectral measure or PDE supplier is an
input. This is the semigroup of the actual completed-energy construction;
no automorphic heat kernel or Gamma0 spectral decomposition is asserted.
-/

namespace ImbalancedChen.Part3.ActualFriedrichsHeatSemigroup20261025a

noncomputable section

open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventZeroAtomPushforward20261025a

/-- A globally continuous formula supplies the endpoint value zero without
assuming that zero lies outside the actual spectrum. -/
def positiveHeatScalar (s : ℝ) : C(ResolventSpectrum, ℝ) where
  toFun t := Real.exp s * expNegInvGlue ((t : ℝ) / s)
  continuous_toFun := continuous_const.mul
    ((expNegInvGlue.contDiff : ContDiff ℝ 0 expNegInvGlue).continuous.comp
      (continuous_subtype_val.div_const s))

theorem positiveHeatScalar_zero (s : ℝ) {t : ResolventSpectrum}
    (ht : (t : ℝ) = 0) : positiveHeatScalar s t = 0 := by
  simp [positiveHeatScalar, ht]

/-- The actual inverse-resolvent heat multiplier, with the zero endpoint
treated continuously at every strictly positive time. -/
theorem positiveHeatScalar_apply {s : ℝ} (hs : 0 < s)
    {t : ResolventSpectrum} (ht : 0 < (t : ℝ)) :
    positiveHeatScalar s t = Real.exp (-s * spectralLambda t) := by
  change Real.exp s * expNegInvGlue ((t : ℝ) / s) = _
  rw [expNegInvGlue, if_neg (not_le.mpr (div_pos ht hs)), ← Real.exp_add]
  congr 1
  unfold spectralLambda
  field_simp [ht.ne', hs.ne']
  <;> ring

def heatScalar (s : ℝ) : C(ResolventSpectrum, ℝ) :=
  if 0 < s then positiveHeatScalar s else 1

theorem heatScalar_zero : heatScalar 0 = 1 := by simp [heatScalar]

theorem heatScalar_of_pos {s : ℝ} (hs : 0 < s) :
    heatScalar s = positiveHeatScalar s := if_pos hs

theorem heatScalar_apply_of_pos {s : ℝ} (hs : 0 < s)
    {t : ResolventSpectrum} (ht : 0 < (t : ℝ)) :
    heatScalar s t = Real.exp (-s * spectralLambda t) := by
  rw [heatScalar_of_pos hs]
  exact positiveHeatScalar_apply hs ht

theorem heatScalar_mem_unitInterval (s : ℝ) (t : ResolventSpectrum) :
    heatScalar s t ∈ Icc (0 : ℝ) 1 := by
  by_cases hs : 0 < s
  · rw [heatScalar_of_pos hs]
    by_cases ht : (t : ℝ) = 0
    · rw [positiveHeatScalar_zero s ht]
      exact ⟨le_rfl, zero_le_one⟩
    · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
        (spectrum_coordinate_mem_unitInterval t).1 (Ne.symm ht)
      rw [positiveHeatScalar_apply hs htp]
      refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
      exact neg_nonpos.mpr (mul_nonneg hs.le (spectralLambda_nonneg htp))
  · simp only [heatScalar, if_neg hs, ContinuousMap.one_apply]
    exact ⟨zero_le_one, le_rfl⟩

/-- Pointwise multiplication at the possibly spectral endpoint zero is
also retained; the identity case s=0 is treated separately. -/
theorem heatScalar_add {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    heatScalar (s + r) = heatScalar s * heatScalar r := by
  by_cases hs0 : s = 0
  · subst s
    simp only [zero_add, heatScalar_zero, one_mul]
  by_cases hr0 : r = 0
  · subst r
    simp only [add_zero, heatScalar_zero, mul_one]
  have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rw [heatScalar_of_pos (add_pos hsp hrp), heatScalar_of_pos hsp, heatScalar_of_pos hrp]
  ext t
  by_cases ht : (t : ℝ) = 0
  · simp only [ContinuousMap.mul_apply, positiveHeatScalar_zero _ ht, zero_mul]
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval t).1 (Ne.symm ht)
    simp only [ContinuousMap.mul_apply, positiveHeatScalar_apply hsp htp,
      positiveHeatScalar_apply hrp htp, positiveHeatScalar_apply (add_pos hsp hrp) htp]
    rw [← Real.exp_add]
    congr 1
    ring

/-- The actual bounded heat operator on canonical hyperbolic L2. Negative
times are assigned the identity only to give an everywhere-defined map;
the semigroup theorem concerns nonnegative times. -/
def heatOperator (s : ℝ) : ResolventAlgebra := resolventCFC (heatScalar s)

theorem heatOperator_zero : heatOperator 0 = 1 := by
  rw [heatOperator, heatScalar_zero, map_one]

theorem heatOperator_add {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    heatOperator (s + r) = heatOperator s * heatOperator r := by
  unfold heatOperator
  rw [heatScalar_add hs hr, map_mul]

theorem heatOperator_selfAdjoint (s : ℝ) : IsSelfAdjoint (heatOperator s) :=
  resolventCFC_selfAdjoint (heatScalar s)

theorem heatOperator_nonneg (s : ℝ) : (0 : ResolventAlgebra) ≤ heatOperator s := by
  change 0 ≤ cfcHom actualWeakResolvent_selfAdjoint (heatScalar s)
  exact (cfcHom_nonneg_iff actualWeakResolvent_selfAdjoint).2
    (fun t => (heatScalar_mem_unitInterval s t).1)

theorem heatOperator_positive (s : ℝ) : (heatOperator s).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).1 (heatOperator_nonneg s)

theorem heatOperator_opNorm_le_one (s : ℝ) : ‖heatOperator s‖ ≤ 1 := by
  change ‖cfcHom actualWeakResolvent_selfAdjoint (heatScalar s)‖ ≤ 1
  rw [norm_cfcHom actualWeakResolvent (heatScalar s) actualWeakResolvent_selfAdjoint]
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (heatScalar_mem_unitInterval s t).1]
  exact (heatScalar_mem_unitInterval s t).2

theorem heatOperator_norm_le (s : ℝ) (f : HyperbolicL2) :
    ‖heatOperator s f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖heatOperator s‖ * ‖f‖ := (heatOperator s).le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (heatOperator_opNorm_le_one s) (norm_nonneg f)
    _ = _ := one_mul _

/-- Actual real CFC gives the true scalar-measure squared norm identity.
This is proved through the operator adjoint, not postulated as Plancherel. -/
theorem scalarMeasure_square_eq_norm (f : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℝ)) :
    (∫ t : ResolventSpectrum, (φ t) ^ 2 ∂scalarMeasure f) =
      ‖resolventCFC φ f‖ ^ 2 := by
  have hi := scalarMeasure_integral f (φ ^ 2)
  rw [map_pow] at hi
  have hAdj : (resolventCFC φ).adjoint = resolventCFC φ :=
    (resolventCFC_selfAdjoint φ).star_eq
  have hcomp : (resolventCFC φ).adjoint.comp (resolventCFC φ) = (resolventCFC φ) ^ 2 := by
    rw [hAdj, pow_two]
    rfl
  have hn := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (resolventCFC φ) f
  rw [hcomp] at hn
  exact hi.trans hn.symm

theorem heatOperator_error_norm_sq (s : ℝ) (f : HyperbolicL2) :
    ‖heatOperator s f - f‖ ^ 2 =
      ∫ t : ResolventSpectrum, (heatScalar s t - 1) ^ 2 ∂scalarMeasure f := by
  have h := scalarMeasure_square_eq_norm f (heatScalar s - 1)
  rw [map_sub, map_one] at h
  exact h.symm

/-- At every nonzero spectral coordinate the actual heat multiplier
approaches one. Zero is removed only by the proved actual zero-atom theorem. -/
theorem tendsto_heatScalar_at_zero {t : ResolventSpectrum} (ht : 0 < (t : ℝ)) :
    Tendsto (fun s : ℝ => heatScalar s t) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun s : ℝ => Real.exp (-s * spectralLambda t)) 0 := by fun_prop
  have hlim : Tendsto (fun s : ℝ => Real.exp (-s * spectralLambda t)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [neg_zero, zero_mul, Real.exp_zero] using hc.tendsto.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (heatScalar_apply_of_pos hs ht).symm

/-- Dominated convergence for the genuine scalar measure. The domination
is one, and the exceptional zero fiber has actual measure zero. -/
theorem tendsto_heat_error_integral (f : HyperbolicL2) :
    Tendsto (fun s : ℝ =>
      ∫ t : ResolventSpectrum, (heatScalar s t - 1) ^ 2 ∂scalarMeasure f)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun t : ResolventSpectrum => (heatScalar s t - 1) ^ 2) (scalarMeasure f) := by
    intro s
    exact (((heatScalar s).continuous.sub continuous_const).pow 2).aestronglyMeasurable
  have hbound : ∀ s : ℝ, ∀ᵐ t : ResolventSpectrum ∂scalarMeasure f,
      ‖(heatScalar s t - 1) ^ 2‖ ≤ (1 : ℝ) := by
    intro s
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ht := heatScalar_mem_unitInterval s t
      nlinarith
  have hlim : ∀ᵐ t : ResolventSpectrum ∂scalarMeasure f,
      Tendsto (fun s : ℝ => (heatScalar s t - 1) ^ 2) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [scalarMeasure_coordinate_pos_ae f] with t ht
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      ((tendsto_heatScalar_at_zero ht).sub tendsto_const_nhds).pow 2
  simpa only [integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence (μ := scalarMeasure f)
      (fun _ : ResolventSpectrum => (1 : ℝ))
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound)
      (integrable_const (1 : ℝ)) hlim)

/-- The actual heat semigroup tends strongly to the identity at zero.
No strong convergence or spectral expansion is a premise. -/
theorem tendsto_heatOperator_at_zero (f : HyperbolicL2) :
    Tendsto (fun s : ℝ => heatOperator s f) (𝓝[>] 0) (𝓝 f) := by
  have hsq : Tendsto (fun s : ℝ => ‖heatOperator s f - f‖ ^ 2) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_heat_error_integral f).congr'
      (Eventually.of_forall fun s => (heatOperator_error_norm_sq s f).symm)
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hn

/-- Scalar heat transform in the genuine unbounded nonnegative coordinate
lambda=1/t-1. No surrogate measure or automorphic identification is used. -/
theorem scalar_heat_integral {s : ℝ} (hs : 0 ≤ s) (f : HyperbolicL2) :
    (∫ lambda : ℝ, Real.exp (-s * lambda) ∂unboundedScalarMeasure f) =
      (inner ℂ f (heatOperator s f)).re := by
  have hm : Measurable (fun lambda : ℝ => Real.exp (-s * lambda)) := by fun_prop
  rw [unboundedScalarMeasure,
    integral_map_of_stronglyMeasurable measurable_spectralLambda hm.stronglyMeasurable]
  have heq : (fun t : ResolventSpectrum => Real.exp (-s * spectralLambda t)) =ᵐ[scalarMeasure f]
      (fun t => heatScalar s t) := by
    filter_upwards [scalarMeasure_coordinate_pos_ae f] with t ht
    by_cases hs0 : s = 0
    · subst s
      simp only [neg_zero, zero_mul, Real.exp_zero, heatScalar_zero, ContinuousMap.one_apply]
    · exact (heatScalar_apply_of_pos (lt_of_le_of_ne hs (Ne.symm hs0)) ht).symm
  rw [integral_congr_ae heq]
  exact scalarMeasure_integral f (heatScalar s)

end
end ImbalancedChen.Part3.ActualFriedrichsHeatSemigroup20261025a
