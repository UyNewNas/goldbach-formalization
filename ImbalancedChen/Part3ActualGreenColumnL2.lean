import ImbalancedChen.Part3GeneralActualRadialGreen
import ImbalancedChen.Part3GeneralIRealPositiveEndpoint
import ImbalancedChen.Part3GeneralKRightEndpoint
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
Actual general real-positive-order Green columns have finite L2 mass and
finite first-derivative L2 mass on the whole logarithmic line. The actual
I left estimate and actual K right estimate supply both remote endpoints;
compact pieces are paid by the proved C2 regularity. No column norm or
endpoint hypothesis is supplied. SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualGreenColumnL220261025a

noncomputable section
open Set MeasureTheory Filter Topology
open GeneralActualRadialGreenSourceOnly ComplexCompactGreenGluingSourceOnly
open ComplexOrderKRadialRegularitySourceOnly
open GeneralIRealPositiveEndpoint20261025a GeneralKRightEndpoint20261025a

private theorem order_legal {nu : ℝ} (hnu : 0 < nu) : -1 < (nu : ℂ).re := by
  simp only [Complex.ofReal_re]
  linarith

private theorem left_extend (f : ℝ → ℂ) (hf : Continuous f)
    {R : ℝ} (htail : MemLp f 2 (volume.restrict (Iic R))) (s : ℝ) :
    MemLp f 2 (volume.restrict (Iic s)) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp htail
  have hc : IntegrableOn (fun r : ℝ => ‖f r‖ ^ 2) (Icc R s) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hsub : Iic s ⊆ Iic R ∪ Icc R s := by
    intro r hr
    by_cases h : r ≤ R
    · exact Or.inl h
    · exact Or.inr ⟨(lt_of_not_ge h).le, hr⟩
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
    ((hi.union hc).mono_set hsub)

private theorem right_extend (f : ℝ → ℂ) (hf : Continuous f)
    (htail : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) (s : ℝ) :
    MemLp f 2 (volume.restrict (Ioi s)) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp htail
  have hc : IntegrableOn (fun r : ℝ => ‖f r‖ ^ 2) (Icc s 0) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hsub : Ioi s ⊆ Ioi (0 : ℝ) ∪ Icc s 0 := by
    intro r hr
    by_cases h : 0 < r
    · exact Or.inl h
    · exact Or.inr ⟨hr.le, le_of_not_gt h⟩
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
    ((hi.union hc).mono_set hsub)

private theorem radialI_all_left_L2 {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    MemLp (radialI (nu : ℂ)) 2 (volume.restrict (Iic s)) ∧
      MemLp (deriv (radialI (nu : ℂ))) 2 (volume.restrict (Iic s)) := by
  obtain ⟨R, hI, hD⟩ := exists_left_log_L2 hnu
  have hi : MemLp (radialI (nu : ℂ)) 2 (volume.restrict (Iic R)) := by
    simpa only [radialI, realILogMode] using hI
  have hd : MemLp (deriv (radialI (nu : ℂ))) 2 (volume.restrict (Iic R)) := by
    simpa only [radialI, realILogMode] using hD
  exact ⟨left_extend _ (radialI_C2 (order_legal hnu)).continuous hi s,
    left_extend _ ((radialI_C2 (order_legal hnu)).continuous_deriv (by norm_num)) hd s⟩

private theorem radialK_all_right_L2 (nu : ℂ) (s : ℝ) :
    MemLp (radialK nu) 2 (volume.restrict (Ioi s)) ∧
      MemLp (deriv (radialK nu)) 2 (volume.restrict (Ioi s)) := by
  exact ⟨right_extend _ (radialK_C2 nu).continuous (radialK_memLp_two_Ioi nu) s,
    right_extend _ ((radialK_C2 nu).continuous_deriv (by norm_num))
      (radialK_deriv_memLp_two_Ioi nu) s⟩

/-- The explicit two-branch first derivative. Its value at the source is
the left value; changing that singleton does not change its L2 class. -/
def actualGreenColumnFirst (nu : ℝ) (s r : ℝ) : ℂ :=
  if r ≤ s then deriv (radialI (nu : ℂ)) r * radialK (nu : ℂ) s
  else radialI (nu : ℂ) s * deriv (radialK (nu : ℂ)) r

/-- Every actual general positive-order Green column is in whole-line L2.
The statement holds for all nu>0, beyond the normalized Green strip. -/
theorem actualRadialGreen_memLp_two {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    MemLp (actualRadialGreen (nu : ℂ) s) 2 (volume : Measure ℝ) := by
  have hL := ((radialI_all_left_L2 hnu s).1).mul_const (radialK (nu : ℂ) s)
  have hR := ((radialK_all_right_L2 (nu : ℂ) s).1).const_mul (radialI (nu : ℂ) s)
  have hp := MemLp.piecewise (s := Iic s) measurableSet_Iic hL
    (by simpa only [compl_Iic] using hR)
  have heq : (Iic s).piecewise
      (fun r => radialI (nu : ℂ) r * radialK (nu : ℂ) s)
      (fun r => radialI (nu : ℂ) s * radialK (nu : ℂ) r) =
        actualRadialGreen (nu : ℂ) s := by
    funext r
    by_cases hr : r ≤ s
    · simp only [Set.piecewise, mem_Iic, if_pos hr, actualRadialGreen, kernel,
        min_eq_left hr, max_eq_right hr]
    · have hs : s ≤ r := (lt_of_not_ge hr).le
      simp only [Set.piecewise, mem_Iic, if_neg hr, actualRadialGreen, kernel,
        min_eq_right hs, max_eq_left hs]
  rwa [heq] at hp

/-- The actual piecewise first derivative also has whole-line L2 mass. -/
theorem actualGreenColumnFirst_memLp_two {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    MemLp (actualGreenColumnFirst nu s) 2 (volume : Measure ℝ) := by
  have hL := ((radialI_all_left_L2 hnu s).2).mul_const (radialK (nu : ℂ) s)
  have hR := ((radialK_all_right_L2 (nu : ℂ) s).2).const_mul (radialI (nu : ℂ) s)
  simpa only [actualGreenColumnFirst, Set.piecewise, mem_Iic] using
    (MemLp.piecewise (s := Iic s) measurableSet_Iic hL
      (by simpa only [compl_Iic] using hR))

/-- Away from the actual source, the piecewise function is the native
real derivative of the same min/max Green kernel. -/
theorem actualRadialGreen_deriv_eq_columnFirst {nu : ℝ} (hnu : 0 < nu)
    {s r : ℝ} (hrs : r ≠ s) :
    deriv (actualRadialGreen (nu : ℂ) s) r = actualGreenColumnFirst nu s r := by
  rcases lt_or_gt_of_ne hrs with hleft | hright
  · have hd := ((radialI_C2 (order_legal hnu)).differentiable (by norm_num) r).hasDerivAt.mul_const
      (radialK (nu : ℂ) s)
    have he : actualRadialGreen (nu : ℂ) s =ᶠ[𝓝 r]
        (fun x => radialI (nu : ℂ) x * radialK (nu : ℂ) s) := by
      filter_upwards [Iio_mem_nhds hleft] with x hx
      simp only [actualRadialGreen, kernel, min_eq_left hx.le, max_eq_right hx.le]
    simpa only [actualGreenColumnFirst, if_pos hleft.le] using
      (hd.congr_of_eventuallyEq he).deriv
  · have hd := ((radialK_C2 (nu : ℂ)).differentiable (by norm_num) r).hasDerivAt.const_mul
      (radialI (nu : ℂ) s)
    have he : actualRadialGreen (nu : ℂ) s =ᶠ[𝓝 r]
        (fun x => radialI (nu : ℂ) s * radialK (nu : ℂ) x) := by
      filter_upwards [Ioi_mem_nhds hright] with x hx
      simp only [actualRadialGreen, kernel, min_eq_right hx.le, max_eq_left hx.le]
    simpa only [actualGreenColumnFirst, if_neg (not_le.mpr hright)] using
      (hd.congr_of_eventuallyEq he).deriv

/-- The native totalized derivative represents exactly the same L2
vector, since the single source point has zero Lebesgue measure. -/
theorem actualRadialGreen_deriv_memLp_two {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    MemLp (deriv (actualRadialGreen (nu : ℂ) s)) 2 (volume : Measure ℝ) := by
  apply (memLp_congr_ae (show actualGreenColumnFirst nu s =ᵐ[volume]
      deriv (actualRadialGreen (nu : ℂ) s) from ?_)).mp
    (actualGreenColumnFirst_memLp_two hnu s)
  filter_upwards [ae_neq s] with r hr
  exact (actualRadialGreen_deriv_eq_columnFirst hnu hr).symm

private theorem radialI_left_zero {nu : ℝ} (hnu : 0 < nu) :
    Tendsto (radialI (nu : ℂ)) atBot (𝓝 0) ∧
      Tendsto (deriv (radialI (nu : ℂ))) atBot (𝓝 0) := by
  obtain ⟨C, R, hC, hb⟩ := exists_left_exponential_bound hnu
  have he : Tendsto (fun r : ℝ => C * Real.exp (nu * r)) atBot (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hnu)).const_mul C
  constructor
  · apply squeeze_zero_norm' (by
      filter_upwards [eventually_le_atBot R] with r hr
      exact (hb r hr).1) he
  · apply squeeze_zero_norm' (by
      filter_upwards [eventually_le_atBot R] with r hr
      exact (hb r hr).2) he

theorem actualRadialGreen_tendsto_left_zero {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Tendsto (actualRadialGreen (nu : ℂ) s) atBot (𝓝 0) := by
  have ht := (radialI_left_zero hnu).1.mul_const (radialK (nu : ℂ) s)
  have he : (fun r => radialI (nu : ℂ) r * radialK (nu : ℂ) s) =ᶠ[atBot]
      actualRadialGreen (nu : ℂ) s := by
    filter_upwards [eventually_le_atBot s] with r hr
    simp only [actualRadialGreen, kernel, min_eq_left hr, max_eq_right hr]
  apply Filter.Tendsto.congr' he
  simpa only [zero_mul] using ht

theorem actualRadialGreen_tendsto_right_zero {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Tendsto (actualRadialGreen (nu : ℂ) s) atTop (𝓝 0) := by
  have ht := (radialK_tendsto_zero (nu : ℂ)).const_mul (radialI (nu : ℂ) s)
  have he : (fun r => radialI (nu : ℂ) s * radialK (nu : ℂ) r) =ᶠ[atTop]
      actualRadialGreen (nu : ℂ) s := by
    filter_upwards [eventually_ge_atTop s] with r hr
    simp only [actualRadialGreen, kernel, min_eq_right hr, max_eq_left hr]
  apply Filter.Tendsto.congr' he
  simpa only [mul_zero] using ht

theorem actualGreenColumnFirst_tendsto_left_zero {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Tendsto (actualGreenColumnFirst nu s) atBot (𝓝 0) := by
  have ht := (radialI_left_zero hnu).2.mul_const (radialK (nu : ℂ) s)
  have he : (fun r => deriv (radialI (nu : ℂ)) r * radialK (nu : ℂ) s) =ᶠ[atBot]
      actualGreenColumnFirst nu s := by
    filter_upwards [eventually_le_atBot s] with r hr
    exact (if_pos hr).symm
  apply Filter.Tendsto.congr' he
  simpa only [zero_mul] using ht

theorem actualGreenColumnFirst_tendsto_right_zero {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Tendsto (actualGreenColumnFirst nu s) atTop (𝓝 0) := by
  have ht := (radialK_deriv_tendsto_zero (nu : ℂ)).const_mul (radialI (nu : ℂ) s)
  have he : (fun r => radialI (nu : ℂ) s * deriv (radialK (nu : ℂ)) r) =ᶠ[atTop]
      actualGreenColumnFirst nu s := by
    filter_upwards [eventually_gt_atTop s] with r hr
    exact (if_neg (not_le.mpr hr)).symm
  apply Filter.Tendsto.congr' he
  simpa only [mul_zero] using ht

/-- The native column derivative has the same actual left endpoint as
its two-branch representative; the source is eventually avoided. -/
theorem actualRadialGreen_deriv_tendsto_left_zero {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Tendsto (deriv (actualRadialGreen (nu : ℂ) s)) atBot (𝓝 0) := by
  have he : actualGreenColumnFirst nu s =ᶠ[atBot]
      deriv (actualRadialGreen (nu : ℂ) s) := by
    filter_upwards [eventually_lt_atBot s] with r hr
    exact (actualRadialGreen_deriv_eq_columnFirst hnu hr.ne).symm
  exact (actualGreenColumnFirst_tendsto_left_zero hnu s).congr' he

/-- The same actual native-derivative zero endpoint at positive infinity. -/
theorem actualRadialGreen_deriv_tendsto_right_zero {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Tendsto (deriv (actualRadialGreen (nu : ℂ) s)) atTop (𝓝 0) := by
  have he : actualGreenColumnFirst nu s =ᶠ[atTop]
      deriv (actualRadialGreen (nu : ℂ) s) := by
    filter_upwards [eventually_gt_atTop s] with r hr
    exact (actualRadialGreen_deriv_eq_columnFirst hnu hr.ne').symm
  exact (actualGreenColumnFirst_tendsto_right_zero hnu s).congr' he
end
end ImbalancedChen.Part3.ActualGreenColumnL220261025a