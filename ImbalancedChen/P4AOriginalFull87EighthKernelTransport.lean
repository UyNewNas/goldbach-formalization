import ImbalancedChen.P4AOriginalFull87EighthKernelControl

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Quantitative one-sided transport of the manuscript's eighth residual
kernel through the EXISTING finiteCap and original trim. This module
supplies integrability of the actual weight and pays its REAL integral
omission/rounding error. It does not identify that integral with a changed
arithmetic frontier or certify a saved numerical gain.
-/
namespace ImbalancedChen.P4AOriginalFull87EighthKernelTransport
noncomputable section
open scoped Classical BigOperators Topology ENNReal
open Set Filter MeasureTheory
open P4AOriginalFull87SourceDictionary P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87FiniteEighthCap P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P4AOriginalFull87TrimOmission

def roundedKernel (n : ℕ) (c : Cell) (t : Point) : ℝ :=
  residual (total t) (product t) (comparison c t) (finiteCap n c t : ℝ)

/-- A comparison integral, NOT a redefinition or filter of the policy's
state list. The retained domain is the literal original action trim. -/
def retainedKernel (r n : ℕ) (c : Cell) : Point → ℝ :=
  (trim c (width r)).indicator (roundedKernel n c)

theorem rounded_kernel_loss (r n : ℕ) (hn : 4 * width n < width r)
    {c : Cell} {t : Point} (ht : t ∈ trim c (width r)) :
    0 ≤ roundedKernel n c t ∧
    0 ≤ kernel c t - roundedKernel n c t ∧
    kernel c t - roundedKernel n c t ≤ roundingConstant * width n := by
  have hs := trim_subset_source c (width_pos r) ht
  have hr := source_residual_range hs
  have hlic := finiteCap_licensed n (width_pos r) hn ht
  have hRL : comparison c t < (finiteCap n c t : ℝ) := by
    have hd := width_pos r
    linarith [hlic.2.1]
  have he := downCap_error n (newCap c t)
  change newCap c t - 2 * width n < (finiteCap n c t : ℝ) ∧
    (finiteCap n c t : ℝ) ≤ newCap c t - width n at he
  have hLM : (finiteCap n c t : ℝ) ≤ newCap c t := by linarith [width_pos n]
  have hgap : newCap c t - (finiteCap n c t : ℝ) ≤ 2 * width n := by linarith
  have hp : 0 < comparison c t - total t := cutoff_pos.trans (hr.1.trans hr.2.1)
  exact ⟨residual_nonneg _ _ _ _ hp (source_product_lower hs).2 hRL.le,
    residual_rounding_loss _ _ _ _ _ _ (width_pos n).le
      (hr.1.trans hr.2.1).le hRL hLM hgap (source_product_lower hs).1⟩

theorem retained_bounds (r n : ℕ) (hn : 4 * width n < width r)
    {c : Cell} {t : Point} (hs : Source c t) :
    0 ≤ retainedKernel r n c t ∧ retainedKernel r n c t ≤ kernel c t := by
  by_cases ht : t ∈ trim c (width r)
  · rw [retainedKernel,indicator_of_mem ht]
    have h := rounded_kernel_loss r n hn ht
    exact ⟨h.1,by linarith [h.2.1]⟩
  · rw [retainedKernel,indicator_of_notMem ht]
    exact ⟨le_rfl,(kernel_bounds hs).1⟩

theorem measurable_roundedKernel (n : ℕ) (c : Cell) : Measurable (roundedKernel n c) := by
  have hM := (newCap_continuous c).measurable
  have hf : Measurable (fun t : Point => ⌊((n : ℝ) + 1) * newCap c t⌋) :=
    (measurable_const.mul hM).floor
  have hc : Measurable (fun t : Point => (⌊((n : ℝ) + 1) * newCap c t⌋ : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hf
  have hL : Measurable (fun t : Point => (finiteCap n c t : ℝ)) := by
    simp only [finiteCap,downCap_cast]
    exact (hc.sub measurable_const).div measurable_const
  have hR := (comparison_continuous c).measurable
  have hS : Measurable total := by unfold total; fun_prop
  have hJ : Measurable product := by unfold product; fun_prop
  exact (measurable_const.mul (hL.sub hR)).div
    (((hR.sub hS).mul (hL.sub hS)).mul hJ)

theorem measurable_retainedKernel (r n : ℕ) (c : Cell) :
    Measurable (retainedKernel r n c) :=
  (measurable_roundedKernel n c).indicator (isClosed_trim c (width r)).measurableSet

theorem integrableOn_retainedKernel (r n : ℕ) (hn : 4 * width n < width r)
    (c : Cell) : IntegrableOn (retainedKernel r n c) (sourceSet c) := by
  apply (integrableOn_kernel c).mono' (measurable_retainedKernel r n c).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
  have hb := retained_bounds r n hn ht
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

def sourceMass (c : Cell) : ℝ := ∫ t in sourceSet c, (1 : ℝ)
def totalSourceMass : ℝ := ∑ c : Cell, sourceMass c

theorem sourceMass_nonneg (c : Cell) : 0 ≤ sourceMass c :=
  integral_nonneg (fun _ => zero_le_one)
theorem totalSourceMass_nonneg : 0 ≤ totalSourceMass :=
  Finset.sum_nonneg (fun c _ => sourceMass_nonneg c)

def kernelLoss (r n : ℕ) (c : Cell) : ℝ :=
  ∫ t in sourceSet c, kernel c t - retainedKernel r n c t
def totalKernelLoss (r n : ℕ) : ℝ := ∑ c : Cell, kernelLoss r n c

theorem totalKernelLoss_eq (r n : ℕ) (hn : 4 * width n < width r) :
    totalKernelLoss r n = (∑ c : Cell, ∫ t in sourceSet c, kernel c t) -
      ∑ c : Cell, ∫ t in sourceSet c, retainedKernel r n c t := by
  calc
    totalKernelLoss r n = ∑ c : Cell,
        ((∫ t in sourceSet c, kernel c t) - ∫ t in sourceSet c, retainedKernel r n c t) := by
      apply Finset.sum_congr rfl
      intro c _
      exact integral_sub (integrableOn_kernel c) (integrableOn_retainedKernel r n hn c)
    _ = _ := Finset.sum_sub_distrib

theorem kernelLoss_budget (r n : ℕ) (hn : 4 * width n < width r) (c : Cell) :
    0 ≤ kernelLoss r n c ∧
    kernelLoss r n c ≤ omitted c r (kernel c) + roundingConstant * width n * sourceMass c := by
  have hK := integrableOn_kernel c
  have hF := integrableOn_retainedKernel r n hn c
  have hO := hK.norm.indicator (isClosed_trim c (width r)).measurableSet.compl
  have hC : IntegrableOn (fun _ : Point => roundingConstant * width n) (sourceSet c) :=
    integrableOn_const (source_volume_lt_top c).ne
  have hnonneg : 0 ≤ kernelLoss r n c := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
    exact sub_nonneg.mpr (retained_bounds r n hn ht).2
  refine ⟨hnonneg,?_⟩
  have hpoint : ∀ t, Source c t → kernel c t - retainedKernel r n c t ≤
      (trim c (width r))ᶜ.indicator (fun t => ‖kernel c t‖) t + roundingConstant * width n := by
    intro t hs
    by_cases ht : t ∈ trim c (width r)
    · rw [retainedKernel,indicator_of_mem ht,indicator_of_notMem (by simpa using ht),zero_add]
      exact (rounded_kernel_loss r n hn ht).2.2
    · rw [retainedKernel,indicator_of_notMem ht,indicator_of_mem (show t ∈ (trim c (width r))ᶜ from ht)]
      rw [Real.norm_eq_abs,abs_of_nonneg (kernel_bounds hs).1]
      have hc : 0 ≤ roundingConstant * width n := mul_nonneg roundingConstant_pos.le (width_pos n).le
      linarith
  have hi := integral_mono_ae (hK.sub hF) (hO.add hC) (show
      ∀ᵐ t ∂volume.restrict (sourceSet c),
      kernel c t - retainedKernel r n c t ≤
        (trim c (width r))ᶜ.indicator (fun t => ‖kernel c t‖) t + roundingConstant * width n from by
    filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
    exact hpoint t ht)
  rw [integral_add hO hC] at hi
  have hconst : (∫ t in sourceSet c, roundingConstant * width n) =
      roundingConstant * width n * sourceMass c := by
    simpa only [sourceMass,mul_one] using
      integral_const_mul (μ := volume.restrict (sourceSet c))
        (roundingConstant * width n) (fun _ : Point => (1 : ℝ))
  rw [hconst] at hi
  exact hi

theorem totalKernelLoss_budget (r n : ℕ) (hn : 4 * width n < width r) :
    0 ≤ totalKernelLoss r n ∧ totalKernelLoss r n ≤
      totalOmitted r kernel + roundingConstant * width n * totalSourceMass := by
  constructor
  · exact Finset.sum_nonneg (fun c _ => (kernelLoss_budget r n hn c).1)
  · calc
      totalKernelLoss r n ≤ ∑ c : Cell,
          (omitted c r (kernel c) + roundingConstant * width n * sourceMass c) :=
        Finset.sum_le_sum (fun c _ => (kernelLoss_budget r n hn c).2)
      _ = _ := by simp [totalOmitted,totalSourceMass,Finset.sum_add_distrib,Finset.mul_sum]

/-- Bounded kernel loss may be charged to an EXISTING volume trim, rather
than selecting an incompatible new source history schedule. -/
theorem totalOmitted_kernel_le_volume (r : ℕ) :
    totalOmitted r kernel ≤ kernelBound * totalOmitted r (fun _ _ => (1 : ℝ)) := by
  have hcell (c : Cell) : omitted c r (kernel c) ≤ kernelBound * omitted c r (fun _ => 1) := by
    have hK := (integrableOn_kernel c).norm.indicator
      (isClosed_trim c (width r)).measurableSet.compl
    have hOne : IntegrableOn (fun _ : Point => (1 : ℝ)) (sourceSet c) :=
      integrableOn_const (source_volume_lt_top c).ne
    have hO := hOne.indicator (isClosed_trim c (width r)).measurableSet.compl
    have hi := integral_mono_ae hK (hO.const_mul kernelBound) (show
      ∀ᵐ t ∂volume.restrict (sourceSet c),
        (trim c (width r))ᶜ.indicator (fun t => ‖kernel c t‖) t ≤
          kernelBound * (trim c (width r))ᶜ.indicator (fun _ => (1 : ℝ)) t from by
      filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
      by_cases hin : t ∈ (trim c (width r))ᶜ
      · simp only [indicator_of_mem hin,mul_one,Real.norm_eq_abs,
          abs_of_nonneg (kernel_bounds ht).1]
        exact (kernel_bounds ht).2
      · simp only [indicator_of_notMem hin,mul_zero,le_refl])
    rw [integral_const_mul] at hi
    simpa only [omitted,norm_one] using hi
  calc
    totalOmitted r kernel ≤ ∑ c : Cell, kernelBound * omitted c r (fun _ => (1 : ℝ)) :=
      Finset.sum_le_sum (fun c _ => hcell c)
    _ = _ := by simp [totalOmitted,Finset.mul_sum]

theorem exists_rounding_budget (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ n0 : ℕ, ∀ n ≥ n0, roundingConstant * width n * totalSourceMass < epsilon := by
  have ht : Tendsto (fun n => roundingConstant * width n * totalSourceMass) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using
      (width_tendsto.const_mul roundingConstant).mul_const totalSourceMass
  exact Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds he))

/-- No integrability, assumed error budget, parent, or saving endpoint is
an input: the actual original kernels supply their own analytic transport. -/
theorem exists_common_eighth_kernel_transport (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ r0 : ℕ, ∀ r ≥ r0, ∃ n0 : ℕ, ∀ n ≥ n0,
      4 * width n < width r ∧ 0 ≤ totalKernelLoss r n ∧ totalKernelLoss r n < epsilon := by
  obtain ⟨r0,hr0⟩ := exists_common_L1_trim kernel integrableOn_kernel (epsilon / 2) (by positivity)
  obtain ⟨nLoss,hnLoss⟩ := exists_rounding_budget (epsilon / 2) (by positivity)
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨nCap,hnCap⟩ := exists_uniform_cap_resolution (width r) (width_pos r)
  refine ⟨max nLoss nCap,?_⟩
  intro n hn
  have hcap := hnCap n ((le_max_right _ _).trans hn)
  have hloss := hnLoss n ((le_max_left _ _).trans hn)
  have homit := hr0 r hr
  have hb := totalKernelLoss_budget r n hcap
  exact ⟨hcap,hb.1,by linarith [hb.2]⟩

end
end ImbalancedChen.P4AOriginalFull87EighthKernelTransport
