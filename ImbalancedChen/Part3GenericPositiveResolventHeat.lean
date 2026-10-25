import ImbalancedChen.Part3GenericResolventScalarMeasure
import ImbalancedChen.Part3GenericResolventScalarZeroAtom
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Heat functional calculus on an arbitrary complex Hilbert space. The data
contain only a bounded operator, self-adjointness, positivity, contraction
and injectivity. Generic RMK scalar measures and the generic proved zero
atom supply dominated convergence. No concrete whole-plane Hilbert space
or heat, strong-limit, domain or spectral-measure supplier occurs here.
-/

namespace ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a

noncomputable section
open MeasureTheory Set Filter Topology

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ResolventData where
  R : H →L[ℂ] H
  selfAdjoint : IsSelfAdjoint R
  nonneg : 0 ≤ R
  norm_le_one : ‖R‖ ≤ 1
  injective : Function.Injective R

variable {H} (D : ResolventData H)

abbrev Spectrum := GenericResolventScalarMeasure20261025a.ResolventSpectrum D.R

def cfcMap : C(Spectrum D, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H) :=
  GenericResolventScalarMeasure20261025a.resolventCFC D.R D.selfAdjoint

abbrev vectorMeasure (f : H) : Measure (Spectrum D) :=
  GenericResolventScalarMeasure20261025a.scalarMeasure D.R D.selfAdjoint f

theorem spectrum_coordinate_mem_unitInterval (t : Spectrum D) : (t : ℝ) ∈ Icc (0 : ℝ) 1 :=
  GenericResolventScalarMeasure20261025a.spectrum_coordinate_mem_unitInterval
    D.R D.nonneg D.norm_le_one t

theorem cfcMap_selfAdjoint (φ : C(Spectrum D, ℝ)) : IsSelfAdjoint (cfcMap D φ) :=
  GenericResolventScalarMeasure20261025a.resolventCFC_selfAdjoint D.R D.selfAdjoint φ

theorem scalarMeasure_integral (f : H) (φ : C(Spectrum D, ℝ)) :
    (∫ t : Spectrum D, φ t ∂vectorMeasure D f) = (inner ℂ f (cfcMap D φ f)).re :=
  GenericResolventScalarMeasure20261025a.scalarMeasure_integral D.R D.selfAdjoint f φ

theorem scalarMeasure_coordinate_pos_ae (f : H) :
    ∀ᵐ t : Spectrum D ∂vectorMeasure D f, 0 < (t : ℝ) := by
  filter_upwards [GenericResolventScalarZeroAtom20261025a.scalarMeasure_ae_coordinate_ne_zero
    D.R D.selfAdjoint D.injective f] with t ht
  exact lt_of_le_of_ne (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)

def coordinate : C(Spectrum D, ℝ) :=
  GenericResolventScalarMeasure20261025a.spectrumCoordinate D.R

theorem cfcMap_coordinate : cfcMap D (coordinate D) = D.R :=
  GenericResolventScalarMeasure20261025a.resolventCFC_coordinate D.R D.selfAdjoint

def spectralLambda (t : Spectrum D) : ℝ := (t : ℝ)⁻¹ - 1

theorem spectralLambda_nonneg {t : Spectrum D} (ht : 0 < (t : ℝ)) :
    0 ≤ spectralLambda D t := by
  have h : (1 : ℝ) ≤ 1 / (t : ℝ) :=
    (le_div_iff₀ ht).2 (by simpa using (spectrum_coordinate_mem_unitInterval D t).2)
  simpa only [spectralLambda, one_div, sub_nonneg] using h

def positiveHeatScalar (s : ℝ) : C(Spectrum D, ℝ) where
  toFun t := Real.exp s * expNegInvGlue ((t : ℝ) / s)
  continuous_toFun := continuous_const.mul
    ((expNegInvGlue.contDiff : ContDiff ℝ 0 expNegInvGlue).continuous.comp
      (continuous_subtype_val.div_const s))

theorem positiveHeatScalar_zero (s : ℝ) {t : Spectrum D}
    (ht : (t : ℝ) = 0) : positiveHeatScalar D s t = 0 := by
  simp [positiveHeatScalar, ht]

/-- The actual inverse-resolvent heat multiplier, with the zero endpoint
treated continuously at every strictly positive time. -/
theorem positiveHeatScalar_apply {s : ℝ} (hs : 0 < s)
    {t : Spectrum D} (ht : 0 < (t : ℝ)) :
    positiveHeatScalar D s t = Real.exp (-s * spectralLambda D t) := by
  change Real.exp s * expNegInvGlue ((t : ℝ) / s) = _
  rw [expNegInvGlue, if_neg (not_le.mpr (div_pos ht hs)), ← Real.exp_add]
  congr 1
  unfold spectralLambda
  field_simp [ht.ne', hs.ne']
  <;> ring

def heatScalar (s : ℝ) : C(Spectrum D, ℝ) :=
  if 0 < s then positiveHeatScalar D s else 1

theorem heatScalar_zero : heatScalar D 0 = 1 := by simp [heatScalar]

theorem heatScalar_of_pos {s : ℝ} (hs : 0 < s) :
    heatScalar D s = positiveHeatScalar D s := if_pos hs

theorem heatScalar_apply_of_pos {s : ℝ} (hs : 0 < s)
    {t : Spectrum D} (ht : 0 < (t : ℝ)) :
    heatScalar D s t = Real.exp (-s * spectralLambda D t) := by
  rw [heatScalar_of_pos D hs]
  exact positiveHeatScalar_apply D hs ht

theorem heatScalar_mem_unitInterval (s : ℝ) (t : Spectrum D) :
    heatScalar D s t ∈ Icc (0 : ℝ) 1 := by
  by_cases hs : 0 < s
  · rw [heatScalar_of_pos D hs]
    by_cases ht : (t : ℝ) = 0
    · rw [positiveHeatScalar_zero D s ht]
      exact ⟨le_rfl, zero_le_one⟩
    · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
        (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)
      rw [positiveHeatScalar_apply D hs htp]
      refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
      exact neg_nonpos.mpr (mul_nonneg hs.le (spectralLambda_nonneg D htp))
  · simp only [heatScalar, if_neg hs, ContinuousMap.one_apply]
    exact ⟨zero_le_one, le_rfl⟩

/-- Pointwise multiplication at the possibly spectral endpoint zero is
also retained; the identity case s=0 is treated separately. -/
theorem heatScalar_add {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    heatScalar D (s + r) = heatScalar D s * heatScalar D r := by
  by_cases hs0 : s = 0
  · subst s
    simp only [zero_add, heatScalar_zero D, one_mul]
  by_cases hr0 : r = 0
  · subst r
    simp only [add_zero, heatScalar_zero D, mul_one]
  have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rw [heatScalar_of_pos D (add_pos hsp hrp), heatScalar_of_pos D hsp, heatScalar_of_pos D hrp]
  ext t
  by_cases ht : (t : ℝ) = 0
  · simp only [ContinuousMap.mul_apply, positiveHeatScalar_zero D _ ht, zero_mul]
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)
    simp only [ContinuousMap.mul_apply, positiveHeatScalar_apply D hsp htp,
      positiveHeatScalar_apply D hrp htp, positiveHeatScalar_apply D (add_pos hsp hrp) htp]
    rw [← Real.exp_add]
    congr 1
    ring

/-- The actual bounded heat operator on the arbitrary Hilbert space H. Negative
times are assigned the identity only to give an everywhere-defined map;
the semigroup theorem concerns nonnegative times. -/
def heatOperator (s : ℝ) : (H →L[ℂ] H) := cfcMap D (heatScalar D s)

theorem heatOperator_zero : heatOperator D 0 = 1 := by
  rw [heatOperator, heatScalar_zero D, map_one]

theorem heatOperator_add {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    heatOperator D (s + r) = heatOperator D s * heatOperator D r := by
  unfold heatOperator
  rw [heatScalar_add D hs hr, map_mul]

theorem heatOperator_selfAdjoint (s : ℝ) : IsSelfAdjoint (heatOperator D s) :=
  cfcMap_selfAdjoint D (heatScalar D s)

theorem heatOperator_nonneg (s : ℝ) : (0 : (H →L[ℂ] H)) ≤ heatOperator D s := by
  change 0 ≤ cfcHom D.selfAdjoint (heatScalar D s)
  exact (cfcHom_nonneg_iff D.selfAdjoint).2
    (fun t => (heatScalar_mem_unitInterval D s t).1)

theorem heatOperator_positive (s : ℝ) : (heatOperator D s).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).1 (heatOperator_nonneg D s)

theorem heatOperator_opNorm_le_one (s : ℝ) : ‖heatOperator D s‖ ≤ 1 := by
  change ‖cfcHom D.selfAdjoint (heatScalar D s)‖ ≤ 1
  rw [norm_cfcHom D.R (heatScalar D s) D.selfAdjoint]
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (heatScalar_mem_unitInterval D s t).1]
  exact (heatScalar_mem_unitInterval D s t).2

theorem heatOperator_norm_le (s : ℝ) (f : H) :
    ‖heatOperator D s f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖heatOperator D s‖ * ‖f‖ := (heatOperator D s).le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right (heatOperator_opNorm_le_one D s) (norm_nonneg f)
    _ = _ := one_mul _

/-- Actual real CFC gives the true scalar-measure squared norm identity.
This is proved through the operator adjoint, not postulated as Plancherel. -/
theorem scalarMeasure_square_eq_norm (f : H)
    (φ : C(Spectrum D, ℝ)) :
    (∫ t : Spectrum D, (φ t) ^ 2 ∂vectorMeasure D f) =
      ‖cfcMap D φ f‖ ^ 2 := by
  have hi := scalarMeasure_integral D f (φ ^ 2)
  rw [map_pow] at hi
  have hAdj : (cfcMap D φ).adjoint = cfcMap D φ :=
    (cfcMap_selfAdjoint D φ).star_eq
  have hcomp : (cfcMap D φ).adjoint.comp (cfcMap D φ) = (cfcMap D φ) ^ 2 := by
    rw [hAdj, pow_two]
    rfl
  have hn := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (cfcMap D φ) f
  rw [hcomp] at hn
  exact hi.trans hn.symm

theorem heatOperator_error_norm_sq (s : ℝ) (f : H) :
    ‖heatOperator D s f - f‖ ^ 2 =
      ∫ t : Spectrum D, (heatScalar D s t - 1) ^ 2 ∂vectorMeasure D f := by
  have h := scalarMeasure_square_eq_norm D f (heatScalar D s - 1)
  rw [map_sub, map_one] at h
  exact h.symm

/-- At every nonzero spectral coordinate the actual heat multiplier
approaches one. Zero is removed only by the proved actual zero-atom theorem. -/
theorem tendsto_heatScalar_at_zero {t : Spectrum D} (ht : 0 < (t : ℝ)) :
    Tendsto (fun s : ℝ => heatScalar D s t) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun s : ℝ => Real.exp (-s * spectralLambda D t)) 0 := by fun_prop
  have hlim : Tendsto (fun s : ℝ => Real.exp (-s * spectralLambda D t)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [neg_zero, zero_mul, Real.exp_zero] using hc.tendsto.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (heatScalar_apply_of_pos D hs ht).symm

/-- Dominated convergence for the genuine scalar measure. The domination
is one, and the exceptional zero fiber has actual measure zero. -/
theorem tendsto_heat_error_integral (f : H) :
    Tendsto (fun s : ℝ =>
      ∫ t : Spectrum D, (heatScalar D s t - 1) ^ 2 ∂vectorMeasure D f)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun t : Spectrum D => (heatScalar D s t - 1) ^ 2) (vectorMeasure D f) := by
    intro s
    exact (((heatScalar D s).continuous.sub continuous_const).pow 2).aestronglyMeasurable
  have hbound : ∀ s : ℝ, ∀ᵐ t : Spectrum D ∂vectorMeasure D f,
      ‖(heatScalar D s t - 1) ^ 2‖ ≤ (1 : ℝ) := by
    intro s
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ht := heatScalar_mem_unitInterval D s t
      nlinarith
  have hlim : ∀ᵐ t : Spectrum D ∂vectorMeasure D f,
      Tendsto (fun s : ℝ => (heatScalar D s t - 1) ^ 2) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [scalarMeasure_coordinate_pos_ae D f] with t ht
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      ((tendsto_heatScalar_at_zero D ht).sub tendsto_const_nhds).pow 2
  simpa only [integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence (μ := vectorMeasure D f)
      (fun _ : Spectrum D => (1 : ℝ))
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound)
      (integrable_const (1 : ℝ)) hlim)

/-- The actual heat semigroup tends strongly to the identity at zero.
No strong convergence or spectral expansion is a premise. -/
theorem tendsto_heatOperator_at_zero (f : H) :
    Tendsto (fun s : ℝ => heatOperator D s f) (𝓝[>] 0) (𝓝 f) := by
  have hsq : Tendsto (fun s : ℝ => ‖heatOperator D s f - f‖ ^ 2) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_heat_error_integral D f).congr'
      (Eventually.of_forall fun s => (heatOperator_error_norm_sq D s f).symm)
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hn



end
end ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a

