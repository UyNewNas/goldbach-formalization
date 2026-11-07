import ImbalancedChen.Part3ActualKLHeatKernelRepresentation
import ImbalancedChen.Part3ActualKLIntegrablePhysicalForward

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
Actual positive-time kernel action on nonsmooth compact physical L2 data.
More generally, L1 physical inputs supported above a finite lower bound
have an absolutely convergent continuous kernel output. If also L2, this
output represents the original radial heat operator under the original KL
unitary and measure. No smoothness, inverse, heat or density hypothesis.
-/
namespace ImbalancedChen.Part3.ActualKLCompactL2HeatAction20261026a
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open RadialSchrodingerL2Form20261025a ActualKLCoreTransform20261025a
open ActualKLCoordinateMeasures20261025a ActualKLOntoUnitary20261025a
open ActualKLHeatTransport20261026a ActualKLHeatKernelAbsolute20261026a
open ActualKLIntegrableSpectralInverse20261026a ActualKLIntegrablePhysicalForward20261026a
open ImaginaryOrderKZeroOrderPositivitySourceOnly

local instance : SigmaFinite tauMeasure := by
  unfold tauMeasure positiveDensityMeasure
  infer_instance

theorem compact_memLp_integrable {f : ℝ → ℂ} (hf2 : MemLp f 2 volume)
    (hc : HasCompactSupport f) : Integrable f := by
  obtain ⟨a, ha⟩ := hc.bddBelow
  obtain ⟨b, hb⟩ := hc.bddAbove
  have hs : Function.support f ⊆ Icc a b := fun r hr =>
    ⟨ha (subset_tsupport f hr), hb (subset_tsupport f hr)⟩
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (MemLp.integrable (by norm_num) (hf2.restrict (Icc a b)))

theorem compact_zero_below {f : ℝ → ℂ} (hc : HasCompactSupport f) :
    ∃ a : ℝ, ∀ r : ℝ, r < a → f r = 0 := by
  obtain ⟨a, ha⟩ := hc.bddBelow
  refine ⟨a, fun r hr => ?_⟩
  by_contra hz
  exact (not_le_of_gt hr) (ha (subset_tsupport f hz))

theorem Kzero_le_of_le {a r : ℝ} (hr : a ≤ r) : Kzero r ≤ Kzero a :=
  imaginaryOrderK_zero_antitone (Real.exp_pos a) (Real.exp_pos r)
    (Real.exp_le_exp.mpr hr)

/-- Uniform order budget, with the true lower spatial support retained. -/
theorem supported_K_budget {f : ℝ → ℂ} {a : ℝ}
    (ha : ∀ r : ℝ, r < a → f r = 0) (τ r : ℝ) :
    ‖K τ r‖ * ‖f r‖ ≤ Kzero a * ‖f r‖ := by
  by_cases hr : r < a
  · simp [ha r hr]
  · exact mul_le_mul_of_nonneg_right
      ((K_norm_le τ r).trans (Kzero_le_of_le (le_of_not_gt hr))) (norm_nonneg _)

theorem supported_forward_norm_le {f : ℝ → ℂ} (hf : Integrable f)
    {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) (τ : ℝ) :
    ‖physicalL1Forward f τ‖ ≤ Kzero a * ∫ r, ‖f r‖ := by
  calc
    ‖physicalL1Forward f τ‖ ≤ ∫ r, Kzero a * ‖f r‖ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul _)
      exact Eventually.of_forall fun r => by
        simpa only [norm_mul, mul_comm] using supported_K_budget ha τ r
    _ = _ := integral_const_mul _ _

def dampedForward (t : ℝ) (f : ℝ → ℂ) (τ : ℝ) : ℂ :=
  (Real.exp (-t*τ^2) : ℂ) * physicalL1Forward f τ

theorem dampedForward_integrable {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf : Integrable f) {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) :
    Integrable (dampedForward t f) tauMeasure := by
  apply ((gaussian_integrable ht).mul_const (Kzero a * ∫ r, ‖f r‖)).mono'
  · exact ((by fun_prop : Continuous (fun τ : ℝ => (Real.exp (-t*τ^2) : ℂ))).mul
      (physicalL1Forward_continuous hf ha)).aestronglyMeasurable
  · exact Eventually.of_forall fun τ => by
      simp only [dampedForward, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (supported_forward_norm_le hf ha τ) (Real.exp_pos _).le

/-- Absolute two-variable budget for nonsmooth data; all compact L2 inputs
satisfy the L1/support hypotheses below by the first two theorems. -/
theorem supported_heat_joint_integrable {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf : Integrable f) {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ => (Real.exp (-t*p.1^2) : ℂ) *
      K p.1 r * K p.1 p.2 * f p.2) (tauMeasure.prod volume) := by
  apply (((gaussian_integrable ht).mul_const (Kzero r)).mul_prod
    (hf.norm.const_mul (Kzero a))).mono'
  · exact ((((by fun_prop : Measurable (fun p : ℝ × ℝ =>
        (Real.exp (-t*p.1^2) : ℂ))).mul
        ((K_measurable_order r).comp measurable_fst)).mul
        K_joint_measurable).aestronglyMeasurable).mul
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)
  · exact Eventually.of_forall fun p => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-t*p.1^2)*‖K p.1 r‖*‖K p.1 p.2‖*‖f p.2‖ =
            (Real.exp (-t*p.1^2)*‖K p.1 r‖)*(‖K p.1 p.2‖*‖f p.2‖) := by ring
        _ ≤ (Real.exp (-t*p.1^2)*Kzero r)*(Kzero a*‖f p.2‖) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (K_norm_le _ _) (Real.exp_pos _).le
          · exact supported_K_budget ha _ _
          · positivity
          · exact mul_nonneg (Real.exp_pos _).le (Kzero_pos r).le

/-- The literal spatial kernel action, defined independently of the heat CLM. -/
def kernelAction (t : ℝ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s, heatKernel t r s * f s

theorem supported_kernel_integrable {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf : Integrable f) {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) (r : ℝ) :
    Integrable (fun s => heatKernel t r s * f s) := by
  have h := (supported_heat_joint_integrable ht hf ha r).integral_prod_right
  apply h.congr
  exact Eventually.of_forall fun s => by
    change (∫ τ, (Real.exp (-t*τ^2) : ℂ)*K τ r*K τ s*f s ∂tauMeasure) = _
    rw [integral_mul_const]
    rfl

theorem supported_kernel_eq_inverse {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf : Integrable f) {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) :
    kernelAction t f = spectralL1Inverse (dampedForward t f) := by
  funext r
  calc
    kernelAction t f r = ∫ s, ∫ τ,
        (Real.exp (-t*τ^2) : ℂ)*K τ r*K τ s*f s ∂tauMeasure := by
      simp only [kernelAction, heatKernel, integral_mul_const]
    _ = ∫ τ, ∫ s, (Real.exp (-t*τ^2) : ℂ)*K τ r*K τ s*f s ∂tauMeasure :=
      (integral_integral_swap (supported_heat_joint_integrable ht hf ha r)).symm
    _ = spectralL1Inverse (dampedForward t f) r := by
      apply integral_congr_ae
      exact Eventually.of_forall fun τ => by
        dsimp [spectralL1Inverse, dampedForward, physicalL1Forward]
        rw [← integral_mul_const, ← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by dsimp [K, inverseKKernel]; ring

theorem supported_kernel_continuous {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf : Integrable f) {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) :
    Continuous (kernelAction t f) := by
  rw [supported_kernel_eq_inverse ht hf ha]
  exact spectralL1Inverse_continuous (dampedForward_integrable ht hf ha)

theorem dampedForward_eq_heat_transform {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2 volume)
    {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) :
    dampedForward t f =ᵐ[tauMeasure]
      (actualKLUnitary (actualRadialHeat t (hf2.toLp f)) : ℝ → ℂ) := by
  filter_upwards [physicalL1Forward_eq_actualKL_ae hf hf2 ha,
    actualKL_heat_ae t ht.le (hf2.toLp f)] with τ hfwd hheat
  simp only [dampedForward, hfwd, hheat]

/-- Identification uses the actual nonsmooth forward unitary theorem and
actual heat intertwining. No smooth approximation premise is supplied. -/
theorem supported_kernel_eq_actualHeat_ae {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2 volume)
    {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) :
    kernelAction t f =ᵐ[(volume : Measure ℝ)] (actualRadialHeat t (hf2.toLp f) : RadialL2) := by
  have he := dampedForward_eq_heat_transform ht hf hf2 ha
  have h2 : MemLp (dampedForward t f) 2 tauMeasure :=
    (Lp.memLp (actualKLUnitary (actualRadialHeat t (hf2.toLp f)))).congr he.symm
  have hlp : h2.toLp (dampedForward t f) =
      actualKLUnitary (actualRadialHeat t (hf2.toLp f)) := by
    apply Lp.ext
    exact h2.coeFn_toLp.trans he
  rw [supported_kernel_eq_inverse ht hf ha]
  have hi := spectralL1Inverse_eq_unitary_inverse_ae (dampedForward_integrable ht hf ha) h2
  simpa only [hlp, actualKLUnitary.symm_apply_apply] using hi

/-- Every compactly supported physical L2 function, with no continuity or
smoothness assumption, has this continuous literal heat representative. -/
theorem compactL2_heat_kernel {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf2 : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (∀ r, Integrable (fun s => heatKernel t r s * f s)) ∧
      Continuous (kernelAction t f) ∧
      kernelAction t f =ᵐ[(volume : Measure ℝ)] (actualRadialHeat t (hf2.toLp f) : RadialL2) := by
  obtain ⟨a, ha⟩ := compact_zero_below hc
  have hf := compact_memLp_integrable hf2 hc
  exact ⟨supported_kernel_integrable ht hf ha, supported_kernel_continuous ht hf ha,
    supported_kernel_eq_actualHeat_ae ht hf hf2 ha⟩

theorem compactL2_kernel_memLp {t : ℝ} (ht : 0 < t) {f : ℝ → ℂ}
    (hf2 : MemLp f 2 volume) (hc : HasCompactSupport f) :
    MemLp (kernelAction t f) 2 volume :=
  (Lp.memLp (actualRadialHeat t (hf2.toLp f))).congr (compactL2_heat_kernel ht hf2 hc).2.2.symm

end
end ImbalancedChen.Part3.ActualKLCompactL2HeatAction20261026a
