import ImbalancedChen.Part3GenericPositiveResolventHeat
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Generic heat generator theorem on an arbitrary complex Hilbert space.
Only primitive positive self-adjoint contractive injective R is supplied.
The true generic scalar measure proves the strong graph derivative, and
commutation with R proves its converse. No concrete Hilbert-space alias,
heat derivative, generator domain or measure supplier is an assumption.
-/
namespace ImbalancedChen.Part3.GenericPositiveResolventHeatGenerator20261025a
noncomputable section
open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : ResolventData H)

theorem mem_resolventGraph_iff (p : H × H) :
    p ∈ resolventGraph D.R ↔ D.R (p.1 + p.2) = p.1 := Iff.rfl

theorem resolvent_pair (f : H) : (D.R f, f - D.R f) ∈ resolventGraph D.R := by
  change D.R (D.R f + (f - D.R f)) = D.R f
  congr 1
  abel
def generatorErrorScalar (s : ℝ) : C(Spectrum D, ℝ) :=
  s⁻¹ • ((heatScalar D s - 1) * coordinate D) + (1 - coordinate D)

theorem generatorErrorScalar_apply (s : ℝ) (t : Spectrum D) :
    generatorErrorScalar D s t =
      (t : ℝ) * (heatScalar D s t - 1) / s + (1 - (t : ℝ)) := by
  change s⁻¹ * ((heatScalar D s t - 1) * (t : ℝ)) + (1 - (t : ℝ)) = _
  ring

theorem coordinate_mul_spectralLambda {t : Spectrum D} (ht : 0 < (t : ℝ)) :
    (t : ℝ) * spectralLambda D t = 1 - (t : ℝ) := by
  unfold spectralLambda
  field_simp [ht.ne']
  <;> ring

/-- This bounded domination is for the resolvent-weighted error. The
unweighted heat derivative is not asserted uniformly bounded in frequency. -/
theorem generatorErrorScalar_mem_unitInterval {s : ℝ} (hs : 0 < s)
    (t : Spectrum D) : generatorErrorScalar D s t ∈ Icc (0 : ℝ) 1 := by
  rw [generatorErrorScalar_apply D]
  by_cases ht : (t : ℝ) = 0
  · simp only [ht, zero_mul, zero_div, sub_zero, zero_add]
    exact ⟨zero_le_one, le_rfl⟩
  have ht0 := (spectrum_coordinate_mem_unitInterval D t).1
  have ht1 := (spectrum_coordinate_mem_unitInterval D t).2
  have htp : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht)
  have hexp : -s * spectralLambda D t + 1 ≤ heatScalar D s t := by
    rw [heatScalar_apply_of_pos D hs htp]
    exact Real.add_one_le_exp _
  have hmul := mul_le_mul_of_nonneg_left hexp ht0
  have hid := coordinate_mul_spectralLambda D htp
  have hrearrange : (t : ℝ) * (-s * spectralLambda D t + 1) =
      -s * (1 - (t : ℝ)) + (t : ℝ) := by
    calc
      _ = -s * ((t : ℝ) * spectralLambda D t) + (t : ℝ) := by ring
      _ = _ := by rw [hid]
  rw [hrearrange] at hmul
  have hlower : -(1 - (t : ℝ)) ≤ (t : ℝ) * (heatScalar D s t - 1) / s := by
    apply (le_div_iff₀ hs).2
    nlinarith
  have hupper : (t : ℝ) * (heatScalar D s t - 1) / s ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos ht0
        (sub_nonpos.mpr (heatScalar_mem_unitInterval D s t).2)) hs.le
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

theorem tendsto_generatorErrorScalar {t : Spectrum D} (ht : 0 < (t : ℝ)) :
    Tendsto (fun s : ℝ => generatorErrorScalar D s t) (𝓝[>] 0) (𝓝 0) := by
  have hlim := ((tendsto_scalar_heat_slope (spectralLambda D t)).const_mul (t : ℝ)).add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => 1 - (t : ℝ)) (𝓝[>] 0) (𝓝 (1 - (t : ℝ))))
  have hz : (t : ℝ) * (-spectralLambda D t) + (1 - (t : ℝ)) = 0 := by
    have h := coordinate_mul_spectralLambda D ht
    nlinarith
  rw [hz] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [generatorErrorScalar_apply D, heatScalar_apply_of_pos D hs ht]
  ring

def generatorErrorOperator (s : ℝ) : (H →L[ℂ] H) := cfcMap D (generatorErrorScalar D s)

/-- Actual CFC multiplication by t is the actual resolvent R. The error
therefore acts on the true graph-domain vector Rf. -/
theorem generatorErrorOperator_apply (s : ℝ) (f : H) :
    generatorErrorOperator D s f =
      (s : ℂ)⁻¹ • (heatOperator D s (D.R f) - D.R f) +
        (f - D.R f) := by
  unfold generatorErrorOperator generatorErrorScalar
  simp only [map_add, map_smul, map_mul, map_sub, map_one,
    cfcMap_coordinate D]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (((s⁻¹ : ℝ) : ℂ) •
      (heatOperator D s (D.R f) - D.R f)) +
      (f - D.R f) = _
  rw [Complex.ofReal_inv]

/-- The genuine squared L2 error is represented by the actual RMK scalar
measure, preserving the resolvent weight before taking the time limit. -/
theorem generatorErrorOperator_norm_sq (s : ℝ) (f : H) :
    ‖generatorErrorOperator D s f‖ ^ 2 =
      ∫ t : Spectrum D, (generatorErrorScalar D s t) ^ 2 ∂vectorMeasure D f :=
  (scalarMeasure_square_eq_norm D f (generatorErrorScalar D s)).symm

theorem tendsto_generatorError_integral (f : H) :
    Tendsto (fun s : ℝ =>
      ∫ t : Spectrum D, (generatorErrorScalar D s t) ^ 2 ∂vectorMeasure D f)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun t : Spectrum D => (generatorErrorScalar D s t) ^ 2) (vectorMeasure D f) := by
    intro s
    exact ((generatorErrorScalar D s).continuous.pow 2).aestronglyMeasurable
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ᵐ t : Spectrum D ∂vectorMeasure D f, ‖(generatorErrorScalar D s t) ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ht := generatorErrorScalar_mem_unitInterval D hs t
      nlinarith
  have hlim : ∀ᵐ t : Spectrum D ∂vectorMeasure D f,
      Tendsto (fun s : ℝ => (generatorErrorScalar D s t) ^ 2) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [scalarMeasure_coordinate_pos_ae D f] with t ht
    simpa only [zero_pow (by decide : 2 ≠ 0)] using (tendsto_generatorErrorScalar D ht).pow 2
  simpa only [integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence (μ := vectorMeasure D f)
      (fun _ : Spectrum D => (1 : ℝ)) (Eventually.of_forall hmeas) hbound
      (integrable_const (1 : ℝ)) hlim)

theorem tendsto_generatorErrorOperator_zero (f : H) :
    Tendsto (fun s : ℝ => generatorErrorOperator D s f) (𝓝[>] 0) (𝓝 0) := by
  have hsq : Tendsto (fun s : ℝ => ‖generatorErrorOperator D s f‖ ^ 2) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_generatorError_integral D f).congr'
      (Eventually.of_forall fun s => (generatorErrorOperator_norm_sq D s f).symm)
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [sub_zero, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hn

/-- The right strong derivative of the actual heat semigroup on the actual
Friedrichs graph is the negative actual operator output. The sole graph
input is the literal already proved equation R(u+v)=u. -/
theorem tendsto_heat_difference_quotient_on_resolventGraph
    {u v : H} (huv : (u, v) ∈ resolventGraph D.R) :
    Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (heatOperator D s u - u))
      (𝓝[>] 0) (𝓝 (-v)) := by
  have hR := (mem_resolventGraph_iff D (u, v)).1 huv
  have hlim := (tendsto_generatorErrorOperator_zero D (u + v)).sub_const v
  simp only [zero_sub] at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun s => by
    rw [generatorErrorOperator_apply D, hR]
    abel

theorem heatOperator_mul_resolvent (s : ℝ) :
    heatOperator D s * D.R = D.R * heatOperator D s := by
  calc
    _ = cfcMap D (heatScalar D s * coordinate D) := by
      rw [map_mul, cfcMap_coordinate D]
      rfl
    _ = cfcMap D (coordinate D * heatScalar D s) := by rw [mul_comm]
    _ = _ := by
      rw [map_mul, cfcMap_coordinate D]
      rfl

theorem heatOperator_resolvent_apply (s : ℝ) (u : H) :
    heatOperator D s (D.R u) = D.R (heatOperator D s u) :=
  congrArg (fun T : (H →L[ℂ] H) => T u) (heatOperator_mul_resolvent D s)

theorem resolvent_heat_difference_quotient (s : ℝ) (u : H) :
    D.R ((s : ℂ)⁻¹ • (heatOperator D s u - u)) =
      (s : ℂ)⁻¹ • (heatOperator D s (D.R u) - D.R u) := by
  rw [map_smul, map_sub, ← heatOperator_resolvent_apply D]

/-- A strong heat derivative at an arbitrary actual L2 vector forces
membership in the actual Friedrichs domain, with the actual operator value. -/
theorem mem_resolventGraph_of_heat_difference_quotient
    {u v : H}
    (hderiv : Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (heatOperator D s u - u))
      (𝓝[>] 0) (𝓝 (-v))) : (u, v) ∈ resolventGraph D.R := by
  have hRlim := (D.R.continuous.tendsto (-v)).comp hderiv
  have hquot : Tendsto
      (fun s : ℝ => (s : ℂ)⁻¹ •
        (heatOperator D s (D.R u) - D.R u))
      (𝓝[>] 0) (𝓝 (-D.R v)) := by
    simpa only [Function.comp_def, resolvent_heat_difference_quotient D, map_neg] using hRlim
  have hactual := tendsto_heat_difference_quotient_on_resolventGraph D
    (resolvent_pair D u)
  have hvalue : D.R v = u - D.R u :=
    neg_injective (tendsto_nhds_unique hquot hactual)
  apply (mem_resolventGraph_iff D (u, v)).2
  rw [map_add, hvalue]
  abel

/-- Full actual domain-and-value identification, in both directions. -/
theorem mem_resolventGraph_iff_heat_difference_quotient (u v : H) :
    (u, v) ∈ resolventGraph D.R ↔
      Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (heatOperator D s u - u))
        (𝓝[>] 0) (𝓝 (-v)) :=
  ⟨tendsto_heat_difference_quotient_on_resolventGraph D,
    mem_resolventGraph_of_heat_difference_quotient D⟩

/-- The genuine strong right-generator graph of the actual heat family. -/
def heatRightGeneratorGraph : Set (H × H) :=
  {p | Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (heatOperator D s p.1 - p.1))
    (𝓝[>] 0) (𝓝 p.2)}

/-- Equality of actual graphs, including domain equality; the negative
sign is the usual heat-generator convention. -/
theorem heatRightGeneratorGraph_eq_negative_resolventGraph :
    heatRightGeneratorGraph D =
      {p : H × H | (p.1, -p.2) ∈ resolventGraph D.R} := by
  ext p
  simpa only [heatRightGeneratorGraph, mem_setOf_eq, neg_neg] using
    (mem_resolventGraph_iff_heat_difference_quotient D p.1 (-p.2)).symm

end
end ImbalancedChen.Part3.GenericPositiveResolventHeatGenerator20261025a


