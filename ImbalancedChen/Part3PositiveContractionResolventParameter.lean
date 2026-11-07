import ImbalancedChen.Part3PositiveContractionResolventCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
The first resolvent identity and operator-norm parameter derivative for the
generic positive-contraction CFC family. The family is total in the real
parameter; every conclusion below is proved on its actual positive region.
No concrete Hilbert space, resolvent identity or differentiability premise
is supplied by the caller.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.PositiveContractionResolventParameter20261025a

noncomputable section

open Filter Topology Set
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem scalar_resolvent_identity {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    resolventRatio a t - resolventRatio b t =
      (b - a) * (resolventRatio a t * resolventRatio b t) := by
  have hda := (denominator_pos ha ht).ne'
  have hdb := (denominator_pos hb ht).ne'
  unfold resolventRatio
  field_simp [hda, hdb]
  unfold denominator
  ring

/-- The genuine generic first resolvent identity, derived pointwise in
the same actual CFC, not assumed as a resolvent supplier property. -/
theorem first_resolvent_identity (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    shiftedResolvent R a - shiftedResolvent R b =
      (b - a) • (shiftedResolvent R a * shiftedResolvent R b) := by
  have hca := continuousOn_resolventRatio R hpos hnorm ha
  have hcb := continuousOn_resolventRatio R hpos hnorm hb
  have heq : (spectrum ℝ R).EqOn
      (fun t => resolventRatio a t - resolventRatio b t)
      (fun t => (b - a) * (resolventRatio a t * resolventRatio b t)) := by
    intro t ht
    exact scalar_resolvent_identity ha hb (spectrum_mem_unitInterval R hpos hnorm ht)
  unfold shiftedResolvent
  rw [← cfc_sub (resolventRatio a) (resolventRatio b) R hca hcb, cfc_congr heq,
    cfc_const_mul (b - a) (fun t => resolventRatio a t * resolventRatio b t) R (hca.mul hcb),
    cfc_mul (resolventRatio a) (resolventRatio b) R hca hcb]

theorem shiftedResolvents_commute (R : HilbertEnd (H := H)) (a b : ℝ) :
    Commute (shiftedResolvent R a) (shiftedResolvent R b) :=
  cfc_commute_cfc (resolventRatio a) (resolventRatio b) R

/-- Quantitative parameter stability, in the actual bounded-operator
norm, with no supplied Lipschitz constant or continuity premise. -/
theorem norm_shiftedResolvent_sub_le (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖shiftedResolvent R a - shiftedResolvent R b‖ ≤ |b - a| / (a * b) := by
  rw [first_resolvent_identity R hSA hpos hnorm ha hb, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |b - a| * (‖shiftedResolvent R a‖ * ‖shiftedResolvent R b‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (abs_nonneg _)
    _ ≤ |b - a| * ((1 / a) * (1 / b)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (shiftedResolvent_norm_le R hpos hnorm ha)
          (shiftedResolvent_norm_le R hpos hnorm hb) (norm_nonneg _) (by positivity)) (abs_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem continuousAt_shiftedResolvent (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) : ContinuousAt (shiftedResolvent R) a := by
  have hnum : Tendsto (fun b : ℝ => |a - b|) (𝓝 a) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, abs_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => a) (𝓝 a) (𝓝 a)).sub tendsto_id).abs
  have hden : Tendsto (fun b : ℝ => a * b) (𝓝 a) (𝓝 (a * a)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => a) (𝓝 a) (𝓝 a)).mul tendsto_id
  have hmajor : Tendsto (fun b : ℝ => |a - b| / (a * b)) (𝓝 a) (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using hnum.div hden (mul_ne_zero ha.ne' ha.ne')
  have hbound : ∀ᶠ b : ℝ in 𝓝 a,
      ‖shiftedResolvent R b - shiftedResolvent R a‖ ≤ |a - b| / (a * b) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    simpa only [mul_comm] using norm_shiftedResolvent_sub_le R hSA hpos hnorm hb ha
  have hnorm : Tendsto (fun b : ℝ => ‖shiftedResolvent R b - shiftedResolvent R a‖)
      (𝓝 a) (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall fun b => norm_nonneg _) hbound hmajor
  change Tendsto (shiftedResolvent R) (𝓝 a) (𝓝 (shiftedResolvent R a))
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm

theorem slope_shiftedResolvent (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≠ a) :
    slope (shiftedResolvent R) a b = -(shiftedResolvent R b * shiftedResolvent R a) := by
  rw [slope_def_module, first_resolvent_identity R hSA hpos hnorm hb ha, smul_smul]
  have hc : (b - a)⁻¹ * (a - b) = (-1 : ℝ) := by
    rw [show a - b = -(b - a) by ring, mul_neg,
      inv_mul_cancel₀ (sub_ne_zero.mpr hba)]
    ring
  rw [hc, neg_one_smul]

/-- The positive-parameter family has the genuine norm derivative -Ra².
The proof uses the derived resolvent identity and continuity, not an
assumed differentiable functional-calculus family. -/
theorem hasDerivAt_shiftedResolvent (R : HilbertEnd (H := H))
    (hSA : IsSelfAdjoint R) (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    {a : ℝ} (ha : 0 < a) :
    HasDerivAt (shiftedResolvent R) (-(shiftedResolvent R a * shiftedResolvent R a)) a := by
  apply hasDerivAt_iff_tendsto_slope.2
  have hlim : Tendsto (fun b : ℝ => -(shiftedResolvent R b * shiftedResolvent R a))
      (𝓝[≠] a) (𝓝 (-(shiftedResolvent R a * shiftedResolvent R a))) :=
    (((continuousAt_shiftedResolvent R hSA hpos hnorm ha).tendsto.mono_left
      nhdsWithin_le_nhds).mul tendsto_const_nhds).neg
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha)] with b hbne hbpos
  have hba : b ≠ a := by simpa using hbne
  exact (slope_shiftedResolvent R hSA hpos hnorm ha hbpos hba).symm

end

end ImbalancedChen.Part3.PositiveContractionResolventParameter20261025a
