import ImbalancedChen.Part3ActualFriedrichsHeatSemigroup
import ImbalancedChen.Part3ActualFriedrichsSelfAdjointOperator
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual heat semigroup has right generator -A on every pair of the
actual Friedrichs graph R(u+v)=u. The proof works on the actual range of R:
the scalar error is t*(exp(-s*(1/t-1))-1)/s+(1-t). Its bound is one,
uniform in s>0 and in the actual spectrum, because of the factor t.
Actual scalar-measure dominated convergence and the proved zero atom then
give the strong derivative. No uniform high-frequency operator-norm
derivative, derivative premise or domain supplier is assumed.

This proves the graph-to-generator inclusion. No converse domain
characterization, automorphic heat kernel or Gamma0 identification is claimed.
-/

namespace ImbalancedChen.Part3.ActualFriedrichsHeatGenerator20261025a

noncomputable section

open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventZeroAtomPushforward20261025a
open ImbalancedChen.Part3.ActualFriedrichsHeatSemigroup20261025a
open ImbalancedChen.Part3.ActualFriedrichsSelfAdjointOperator20261025a

/-- The resolvent-weighted derivative error remains a continuous
function of the actual bounded spectral coordinate, including t=0. -/
def generatorErrorScalar (s : ℝ) : C(ResolventSpectrum, ℝ) :=
  s⁻¹ • ((heatScalar s - 1) * spectrumCoordinate) + (1 - spectrumCoordinate)

theorem generatorErrorScalar_apply (s : ℝ) (t : ResolventSpectrum) :
    generatorErrorScalar s t =
      (t : ℝ) * (heatScalar s t - 1) / s + (1 - (t : ℝ)) := by
  change s⁻¹ * ((heatScalar s t - 1) * (t : ℝ)) + (1 - (t : ℝ)) = _
  ring

theorem coordinate_mul_spectralLambda {t : ResolventSpectrum} (ht : 0 < (t : ℝ)) :
    (t : ℝ) * spectralLambda t = 1 - (t : ℝ) := by
  unfold spectralLambda
  field_simp [ht.ne']
  <;> ring

/-- This bounded domination is for the resolvent-weighted error. The
unweighted heat derivative is not asserted uniformly bounded in frequency. -/
theorem generatorErrorScalar_mem_unitInterval {s : ℝ} (hs : 0 < s)
    (t : ResolventSpectrum) : generatorErrorScalar s t ∈ Icc (0 : ℝ) 1 := by
  rw [generatorErrorScalar_apply]
  by_cases ht : (t : ℝ) = 0
  · simp only [ht, zero_mul, zero_div, sub_zero, zero_add]
    exact ⟨zero_le_one, le_rfl⟩
  have ht0 := (spectrum_coordinate_mem_unitInterval t).1
  have ht1 := (spectrum_coordinate_mem_unitInterval t).2
  have htp : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht)
  have hexp : -s * spectralLambda t + 1 ≤ heatScalar s t := by
    rw [heatScalar_apply_of_pos hs htp]
    exact Real.add_one_le_exp _
  have hmul := mul_le_mul_of_nonneg_left hexp ht0
  have hid := coordinate_mul_spectralLambda htp
  have hrearrange : (t : ℝ) * (-s * spectralLambda t + 1) =
      -s * (1 - (t : ℝ)) + (t : ℝ) := by
    calc
      _ = -s * ((t : ℝ) * spectralLambda t) + (t : ℝ) := by ring
      _ = _ := by rw [hid]
  rw [hrearrange] at hmul
  have hlower : -(1 - (t : ℝ)) ≤ (t : ℝ) * (heatScalar s t - 1) / s := by
    apply (le_div_iff₀ hs).2
    nlinarith
  have hupper : (t : ℝ) * (heatScalar s t - 1) / s ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos ht0
        (sub_nonpos.mpr (heatScalar_mem_unitInterval s t).2)) hs.le
  constructor <;> linarith

/-- The scalar derivative is the actual derivative of the exponential.
No spectral derivative formula is supplied as a hypothesis. -/
theorem tendsto_scalar_heat_slope (lambda : ℝ) :
    Tendsto (fun s : ℝ => (Real.exp (-s * lambda) - 1) / s)
      (𝓝[>] 0) (𝓝 (-lambda)) := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-s * lambda)) (-lambda) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).neg.mul_const lambda).exp) using 1 <;> simp
  simpa only [zero_add, neg_zero, zero_mul, Real.exp_zero,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

theorem tendsto_generatorErrorScalar {t : ResolventSpectrum} (ht : 0 < (t : ℝ)) :
    Tendsto (fun s : ℝ => generatorErrorScalar s t) (𝓝[>] 0) (𝓝 0) := by
  have hlim := ((tendsto_scalar_heat_slope (spectralLambda t)).const_mul (t : ℝ)).add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => 1 - (t : ℝ)) (𝓝[>] 0) (𝓝 (1 - (t : ℝ))))
  have hz : (t : ℝ) * (-spectralLambda t) + (1 - (t : ℝ)) = 0 := by
    have h := coordinate_mul_spectralLambda ht
    nlinarith
  rw [hz] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [generatorErrorScalar_apply, heatScalar_apply_of_pos hs ht]
  ring

def generatorErrorOperator (s : ℝ) : ResolventAlgebra := resolventCFC (generatorErrorScalar s)

/-- Actual CFC multiplication by t is the actual resolvent R. The error
therefore acts on the true graph-domain vector Rf. -/
theorem generatorErrorOperator_apply (s : ℝ) (f : HyperbolicL2) :
    generatorErrorOperator s f =
      (s : ℂ)⁻¹ • (heatOperator s (actualWeakResolvent f) - actualWeakResolvent f) +
        (f - actualWeakResolvent f) := by
  unfold generatorErrorOperator generatorErrorScalar
  simp only [map_add, map_smul, map_mul, map_sub, map_one,
    resolventCFC_coordinate]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (((s⁻¹ : ℝ) : ℂ) •
      (heatOperator s (actualWeakResolvent f) - actualWeakResolvent f)) +
      (f - actualWeakResolvent f) = _
  rw [Complex.ofReal_inv]

/-- The genuine squared L2 error is represented by the actual RMK scalar
measure, preserving the resolvent weight before taking the time limit. -/
theorem generatorErrorOperator_norm_sq (s : ℝ) (f : HyperbolicL2) :
    ‖generatorErrorOperator s f‖ ^ 2 =
      ∫ t : ResolventSpectrum, (generatorErrorScalar s t) ^ 2 ∂scalarMeasure f :=
  (scalarMeasure_square_eq_norm f (generatorErrorScalar s)).symm

theorem tendsto_generatorError_integral (f : HyperbolicL2) :
    Tendsto (fun s : ℝ =>
      ∫ t : ResolventSpectrum, (generatorErrorScalar s t) ^ 2 ∂scalarMeasure f)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun t : ResolventSpectrum => (generatorErrorScalar s t) ^ 2) (scalarMeasure f) := by
    intro s
    exact ((generatorErrorScalar s).continuous.pow 2).aestronglyMeasurable
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ᵐ t : ResolventSpectrum ∂scalarMeasure f, ‖(generatorErrorScalar s t) ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ht := generatorErrorScalar_mem_unitInterval hs t
      nlinarith
  have hlim : ∀ᵐ t : ResolventSpectrum ∂scalarMeasure f,
      Tendsto (fun s : ℝ => (generatorErrorScalar s t) ^ 2) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [scalarMeasure_coordinate_pos_ae f] with t ht
    simpa only [zero_pow (by decide : 2 ≠ 0)] using (tendsto_generatorErrorScalar ht).pow 2
  simpa only [integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence (μ := scalarMeasure f)
      (fun _ : ResolventSpectrum => (1 : ℝ)) (Eventually.of_forall hmeas) hbound
      (integrable_const (1 : ℝ)) hlim)

theorem tendsto_generatorErrorOperator_zero (f : HyperbolicL2) :
    Tendsto (fun s : ℝ => generatorErrorOperator s f) (𝓝[>] 0) (𝓝 0) := by
  have hsq : Tendsto (fun s : ℝ => ‖generatorErrorOperator s f‖ ^ 2) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_generatorError_integral f).congr'
      (Eventually.of_forall fun s => (generatorErrorOperator_norm_sq s f).symm)
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [sub_zero, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hn

/-- The right strong derivative of the actual heat semigroup on the actual
Friedrichs graph is the negative actual operator output. The sole graph
input is the literal already proved equation R(u+v)=u. -/
theorem tendsto_heat_difference_quotient_on_friedrichsGraph
    {u v : HyperbolicL2} (huv : (u, v) ∈ friedrichsGraph) :
    Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (heatOperator s u - u))
      (𝓝[>] 0) (𝓝 (-v)) := by
  have hR := (mem_friedrichsGraph_iff (u, v)).1 huv
  have hlim := (tendsto_generatorErrorOperator_zero (u + v)).sub_const v
  simp only [zero_sub] at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun s => by
    rw [generatorErrorOperator_apply, hR]
    abel

end
end ImbalancedChen.Part3.ActualFriedrichsHeatGenerator20261025a
