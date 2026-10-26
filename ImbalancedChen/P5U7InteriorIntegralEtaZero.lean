import ImbalancedChen.P5U7OriginalFullIntegralDictionary
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Literal U7 interior-integral right continuity at eta=0. The actual strict
gate indicators converge POINTWISE from nonnegative margins, including
their strict zero boundary; no arithmetic prime wall is removed. A proved
positive extension and explicit compact domination supply filter DCT.
-/

namespace ImbalancedChen

noncomputable section

open Set MeasureTheory Filter Topology
open scoped BigOperators
open Classical

def p5U7EtaCube : Set (Fin 2 → ℝ) := logPrimeBox
  (fun _ : Fin 2 => (59 / 250 : ℝ)) (fun _ => (1 / 2 : ℝ))
def p5U7EtaDomain (eta : ℝ) : Set (Fin 2 → ℝ) := p5U7EtaCube ∩ p5U7InteriorRegion eta
def p5U7EtaExtension (x : Fin 2 → ℝ) : ℝ := p5U7OmegaPositiveExtension 1 (x 0) (x 1)
def p5U7EtaSample (eta : ℝ) : (Fin 2 → ℝ) → ℝ := (p5U7EtaDomain eta).indicator p5U7EtaExtension
def p5U7EtaDomination : (Fin 2 → ℝ) → ℝ := p5U7EtaCube.indicator (fun _ => p5U7OmegaFiniteBound 1)

theorem measurableSet_p5U7EtaDomain (eta : ℝ) : MeasurableSet (p5U7EtaDomain eta) :=
  (measurableSet_logPrimeBox _ _).inter
    (measurableSet_primeAffineGateRegion (p5U7InteriorForms eta) p5U7InteriorBounds)

theorem continuous_p5U7EtaExtension : Continuous p5U7EtaExtension :=
  (p5U7Omega_extension_continuous 1).comp ((continuous_apply 0).prodMk (continuous_apply 1))

theorem p5U7EtaSample_aestronglyMeasurable (eta : ℝ) : AEStronglyMeasurable (p5U7EtaSample eta) :=
  (continuous_p5U7EtaExtension.stronglyMeasurable.indicator (measurableSet_p5U7EtaDomain eta)).aestronglyMeasurable

theorem p5U7Eta_extension_eq {x : Fin 2 → ℝ} (hx : x ∈ p5U7EtaCube) :
    p5U7EtaExtension x = p5U7OmegaKernel 1 (x 0) (x 1) :=
  p5U7Omega_extension_eq ((mem_logPrimeBox.mp hx) 0).1 ((mem_logPrimeBox.mp hx) 1).1

theorem integral_p5U7EtaSample (eta : ℝ) : (∫ x, p5U7EtaSample eta x) = p5U7InteriorOmegaIntegral eta := by
  rw [p5U7EtaSample, integral_indicator (measurableSet_p5U7EtaDomain eta)]
  apply setIntegral_congr_fun (measurableSet_p5U7EtaDomain eta)
  intro x hx
  exact p5U7Eta_extension_eq hx.1

theorem p5U7EtaDomination_integrable : Integrable p5U7EtaDomination := by
  have hc : IntegrableOn (fun _ : Fin 2 → ℝ => p5U7OmegaFiniteBound 1)
      (Icc (fun _ : Fin 2 => (59 / 250 : ℝ)) (fun _ => (1 / 2 : ℝ))) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hsub : p5U7EtaCube ⊆ Icc (fun _ : Fin 2 => (59 / 250 : ℝ)) (fun _ => (1 / 2 : ℝ)) := by
    intro x hx
    have hh := mem_logPrimeBox.mp hx
    exact ⟨fun i => (hh i).1, fun i => (hh i).2.le⟩
  exact (hc.mono_set hsub).integrable_indicator (measurableSet_logPrimeBox _ _)

theorem p5U7EtaSample_dominated {eta : ℝ} (heta : 0 ≤ eta) (x : Fin 2 → ℝ) :
    ‖p5U7EtaSample eta x‖ ≤ p5U7EtaDomination x := by
  have hB : 0 ≤ p5U7OmegaFiniteBound 1 := by unfold p5U7OmegaFiniteBound; positivity
  by_cases hc : x ∈ p5U7EtaCube
  · rw [p5U7EtaDomination, indicator_of_mem hc]
    by_cases hd : x ∈ p5U7EtaDomain eta
    · rw [p5U7EtaSample, indicator_of_mem hd, p5U7Eta_extension_eq hc]
      have hs := p5U7Interior_subset_original heta hd.1 hd.2
      exact p5U7Omega_kernel_norm_le_explicit 1 ⟨hs.1, hs.2.1, hs.2.2.le⟩
    · rw [p5U7EtaSample, indicator_of_notMem hd, norm_zero]
      exact hB
  · have hd : x ∉ p5U7EtaDomain eta := fun h => hc h.1
    rw [p5U7EtaSample, indicator_of_notMem hd, norm_zero,
      p5U7EtaDomination, indicator_of_notMem hc]

theorem p5U7EtaDomain_mono_zero {eta : ℝ} (heta : 0 ≤ eta) :
    p5U7EtaDomain eta ⊆ p5U7EtaDomain 0 := by
  intro x hx
  obtain ⟨ho, hcap⟩ := (p5U7InteriorRegion_iff eta x).mp hx.2
  have hx1 : 0 < x 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250)
    ((mem_logPrimeBox.mp hx.1) 1).1
  refine ⟨hx.1, (p5U7InteriorRegion_iff 0 x).mpr ⟨ho, ?_⟩⟩
  nlinarith only [hcap, mul_nonneg heta hx1.le]

/-- At every point the literal strict indicators become constant as the
nonnegative margin tends to zero. Boundary atoms here stay strictly out. -/
theorem tendsto_p5U7EtaSample (x : Fin 2 → ℝ) :
    Tendsto (fun eta : ℝ => p5U7EtaSample eta x) (𝓝[Ici 0] 0) (𝓝 (p5U7EtaSample 0 x)) := by
  have hnonneg : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0, 0 ≤ eta := self_mem_nhdsWithin
  have hEq : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0, p5U7EtaSample eta x = p5U7EtaSample 0 x := by
    by_cases hx : x ∈ p5U7EtaDomain 0
    · obtain ⟨ho, hcap⟩ := (p5U7InteriorRegion_iff 0 x).mp hx.2
      have hx1 : 0 < x 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250)
        ((mem_logPrimeBox.mp hx.1) 1).1
      let r : ℝ := (1 - x 0 - 2 * x 1) / (2 * x 1)
      have hr : 0 < r := by dsimp only [r]; apply div_pos <;> linarith only [hcap, hx1]
      have hsmall : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0, eta < r :=
        nhdsWithin_le_nhds (Iio_mem_nhds hr)
      filter_upwards [hsmall, hnonneg] with eta heta _
      have hprod := mul_lt_mul_of_pos_right heta hx1
      have heq : r * x 1 = (1 - x 0 - 2 * x 1) / 2 := by
        dsimp only [r]
        field_simp [hx1.ne']
        <;> ring
      rw [heq] at hprod
      have hxe : x ∈ p5U7EtaDomain eta := ⟨hx.1, (p5U7InteriorRegion_iff eta x).mpr
        ⟨ho, by nlinarith only [hprod, hcap]⟩⟩
      simp only [p5U7EtaSample, indicator_of_mem hxe, indicator_of_mem hx]
    · filter_upwards [hnonneg] with eta heta
      have hxe : x ∉ p5U7EtaDomain eta := fun h => hx (p5U7EtaDomain_mono_zero heta h)
      simp only [p5U7EtaSample, indicator_of_notMem hxe, indicator_of_notMem hx]
  exact tendsto_const_nhds.congr' hEq.symm

/-- Actual eta-to-zero Buchstab integral transport. Dominating kernel
and integrability are proved explicitly, not supplied as hypotheses. -/
theorem tendsto_p5U7InteriorOmegaIntegral_eta_zero :
    Tendsto p5U7InteriorOmegaIntegral (𝓝[Ici (0 : ℝ)] 0) (𝓝 (p5U7InteriorOmegaIntegral 0)) := by
  have hnonneg : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0, 0 ≤ eta := self_mem_nhdsWithin
  have hh := tendsto_integral_filter_of_dominated_convergence p5U7EtaDomination
    (Eventually.of_forall p5U7EtaSample_aestronglyMeasurable)
    (hnonneg.mono (fun eta heta => Eventually.of_forall (p5U7EtaSample_dominated heta)))
    p5U7EtaDomination_integrable (Eventually.of_forall tendsto_p5U7EtaSample)
  simpa only [integral_p5U7EtaSample] using hh

end

end ImbalancedChen
