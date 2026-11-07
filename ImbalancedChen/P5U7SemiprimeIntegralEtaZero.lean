import ImbalancedChen.P5U7ActualComponentCollars
import ImbalancedChen.P5U7PrimeIntegralEtaZero

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Genuine DCT for the separate ordered-semiprime leading kernel. Its sample
is the difference of the genuine full and prime samples, with an explicit
integrable domination. On every nonnegative eta domain this difference is
proved equal to the literal ordered terminal-pair kernel, not postulated
as an arithmetic semiprime density. Analytic collar positivity is separate
from the actual arithmetic collar estimate in the predecessor.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7SemiprimeEtaSample (eta : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  p5U7EtaSample eta x-p5U7PrimeEtaSample eta x

def p5U7SemiprimeEtaDomination (x : Fin 2 → ℝ) : ℝ :=
  p5U7EtaDomination x+p5U7PrimeEtaDomination x

theorem p5U7ComponentSemiprimeKernel_nonneg {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) : 0 ≤ p5U7ComponentSemiprimeKernel t u := by
  unfold p5U7ComponentSemiprimeKernel
  split_ifs with hcut
  · exact p5U7Mass_semiprime_integral_slice_nonneg (p5U7Omega_closed_geometry h).1 h.2.1 hcut.le
  · exact le_rfl

theorem p5U7SemiprimeEtaSample_eq (eta : ℝ) (heta : 0 ≤ eta) (x : Fin 2 → ℝ) :
    p5U7SemiprimeEtaSample eta x =
      (p5U7EtaDomain eta).indicator (fun x => p5U7ComponentSemiprimeKernel (x 0) (x 1)) x := by
  by_cases hx : x ∈ p5U7EtaDomain eta
  · rw [indicator_of_mem hx]
    dsimp only [p5U7SemiprimeEtaSample]
    rw [p5U7EtaSample,indicator_of_mem hx,p5U7Eta_extension_eq hx.1,
      p5U7PrimeEtaSample,indicator_of_mem hx,p5U7PrimeEtaExtension_eq heta hx]
    have hsplit := p5U7Component_kernel_split (p5U7PrimeLeading_domain_geometry heta hx).1
    linarith only [hsplit]
  · simp only [p5U7SemiprimeEtaSample,p5U7EtaSample,p5U7PrimeEtaSample,
      indicator_of_notMem hx,sub_self]

theorem p5U7SemiprimeEtaSample_aestronglyMeasurable (eta : ℝ) :
    AEStronglyMeasurable (p5U7SemiprimeEtaSample eta) :=
  (p5U7EtaSample_aestronglyMeasurable eta).sub (p5U7PrimeEtaSample_aestronglyMeasurable eta)

theorem p5U7SemiprimeEtaDomination_integrable : Integrable p5U7SemiprimeEtaDomination :=
  p5U7EtaDomination_integrable.add p5U7PrimeEtaDomination_integrable

theorem p5U7SemiprimeEtaSample_dominated {eta : ℝ} (heta : 0 ≤ eta) (x : Fin 2 → ℝ) :
    ‖p5U7SemiprimeEtaSample eta x‖ ≤ p5U7SemiprimeEtaDomination x := by
  exact (norm_sub_le _ _).trans (add_le_add
    (p5U7EtaSample_dominated heta x) (p5U7PrimeEtaSample_dominated eta x))

theorem p5U7SemiprimeEtaSample_integrable {eta : ℝ} (heta : 0 ≤ eta) :
    Integrable (p5U7SemiprimeEtaSample eta) :=
  p5U7SemiprimeEtaDomination_integrable.mono'
    (p5U7SemiprimeEtaSample_aestronglyMeasurable eta)
    (Eventually.of_forall (p5U7SemiprimeEtaSample_dominated heta))

theorem tendsto_p5U7SemiprimeEtaSample (x : Fin 2 → ℝ) :
    Tendsto (fun eta : ℝ => p5U7SemiprimeEtaSample eta x) (𝓝[Ici 0] 0)
      (𝓝 (p5U7SemiprimeEtaSample 0 x)) :=
  (tendsto_p5U7EtaSample x).sub (tendsto_p5U7PrimeEtaSample x)

theorem integral_p5U7SemiprimeEtaSample (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ x, p5U7SemiprimeEtaSample eta x) = p5U7SemiprimeLeadingIntegral eta := by
  calc
    _ = ∫ x, (p5U7EtaDomain eta).indicator
        (fun x => p5U7ComponentSemiprimeKernel (x 0) (x 1)) x := by
      apply integral_congr_ae
      exact Eventually.of_forall (p5U7SemiprimeEtaSample_eq eta heta)
    _ = _ := integral_indicator (measurableSet_p5U7EtaDomain eta)

/-- The separate ordered-semiprime integral has its own genuine DCT,
with literal pointwise strict-gate convergence and integrable domination. -/
theorem tendsto_p5U7SemiprimeLeadingIntegral_eta_zero :
    Tendsto p5U7SemiprimeLeadingIntegral (𝓝[Ici (0 : ℝ)] 0)
      (𝓝 (p5U7SemiprimeLeadingIntegral 0)) := by
  have hnonneg : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0, 0 ≤ eta := self_mem_nhdsWithin
  have h := tendsto_integral_filter_of_dominated_convergence p5U7SemiprimeEtaDomination
    (Eventually.of_forall p5U7SemiprimeEtaSample_aestronglyMeasurable)
    (hnonneg.mono (fun eta heta => Eventually.of_forall (p5U7SemiprimeEtaSample_dominated heta)))
    p5U7SemiprimeEtaDomination_integrable (Eventually.of_forall tendsto_p5U7SemiprimeEtaSample)
  rw [integral_p5U7SemiprimeEtaSample 0 (by norm_num)] at h
  apply h.congr'
  filter_upwards [hnonneg] with eta heta
  exact integral_p5U7SemiprimeEtaSample eta heta

theorem p5U7SemiprimeEtaSample_nonneg {eta : ℝ} (heta : 0 ≤ eta) (x : Fin 2 → ℝ) :
    0 ≤ p5U7SemiprimeEtaSample eta x := by
  rw [p5U7SemiprimeEtaSample_eq eta heta]
  by_cases hx : x ∈ p5U7EtaDomain eta
  · rw [indicator_of_mem hx]
    exact p5U7ComponentSemiprimeKernel_nonneg (p5U7PrimeLeading_domain_geometry heta hx).1
  · rw [indicator_of_notMem hx]

theorem p5U7SemiprimeEtaSample_le_zero {eta : ℝ} (heta : 0 ≤ eta) (x : Fin 2 → ℝ) :
    p5U7SemiprimeEtaSample eta x ≤ p5U7SemiprimeEtaSample 0 x := by
  rw [p5U7SemiprimeEtaSample_eq eta heta,p5U7SemiprimeEtaSample_eq 0 (by norm_num)]
  by_cases hx : x ∈ p5U7EtaDomain eta
  · rw [indicator_of_mem hx,indicator_of_mem (p5U7EtaDomain_mono_zero heta hx)]
  · rw [indicator_of_notMem hx]
    by_cases hx0 : x ∈ p5U7EtaDomain 0
    · rw [indicator_of_mem hx0]
      exact p5U7ComponentSemiprimeKernel_nonneg
        (p5U7PrimeLeading_domain_geometry (by norm_num : (0 : ℝ) ≤ 0) hx0).1
    · rw [indicator_of_notMem hx0]

/-- The genuine analytic ordered-semiprime collar has nonnegative mass.
Its smallness below is an analytic statement, not deletion of arithmetic labels. -/
theorem p5U7SemiprimeLeadingIntegral_collar_nonneg {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ p5U7SemiprimeLeadingIntegral 0-p5U7SemiprimeLeadingIntegral eta := by
  rw [← integral_p5U7SemiprimeEtaSample 0 (by norm_num),
    ← integral_p5U7SemiprimeEtaSample eta heta]
  exact sub_nonneg.mpr (integral_mono (p5U7SemiprimeEtaSample_integrable heta)
    (p5U7SemiprimeEtaSample_integrable (by norm_num))
    (p5U7SemiprimeEtaSample_le_zero heta))

theorem p5U7SemiprimeLeadingIntegral_collar_eventually_small (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ eta : ℝ in 𝓝[Ioi (0 : ℝ)] 0,
      0 ≤ p5U7SemiprimeLeadingIntegral 0-p5U7SemiprimeLeadingIntegral eta ∧
      p5U7SemiprimeLeadingIntegral 0-p5U7SemiprimeLeadingIntegral eta < epsilon := by
  have hI := tendsto_p5U7SemiprimeLeadingIntegral_eta_zero.mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hnear := hI.eventually (Ioi_mem_nhds
    (show p5U7SemiprimeLeadingIntegral 0-epsilon < p5U7SemiprimeLeadingIntegral 0 by linarith))
  filter_upwards [hnear,self_mem_nhdsWithin : ∀ᶠ eta : ℝ in 𝓝[Ioi 0] 0, 0 < eta] with eta hi hp
  exact ⟨p5U7SemiprimeLeadingIntegral_collar_nonneg hp.le,by linarith only [hi]⟩

end
end ImbalancedChen
