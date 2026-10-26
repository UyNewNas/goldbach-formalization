import ImbalancedChen.P5U7ActualInteriorComponentMeans
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Genuine eta-to-zero convergence of the prime component integral. The
literal strict gate stabilizes pointwise, including its excluded walls.
A globally continuous positive extension and explicit compact integrable
domination supply DCT. No arithmetic target exclusion or endpoint is erased.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7PrimeEtaExtension (x : Fin 2 → ℝ) : ℝ :=
  1 / (max (59/250 : ℝ) (x 0) * max (59/250 : ℝ) (x 1) *
    max (59/250 : ℝ) (1-x 0-x 1))

def p5U7PrimeEtaSample (eta : ℝ) : (Fin 2 → ℝ) → ℝ :=
  (p5U7EtaDomain eta).indicator p5U7PrimeEtaExtension

def p5U7PrimeEtaDomination : (Fin 2 → ℝ) → ℝ :=
  p5U7EtaCube.indicator (fun _ => 1 / (59/250 : ℝ)^3)

theorem continuous_p5U7PrimeEtaExtension : Continuous p5U7PrimeEtaExtension := by
  apply continuous_const.div
    (((continuous_const.max (continuous_apply 0)).mul
      (continuous_const.max (continuous_apply 1))).mul
        (continuous_const.max ((continuous_const.sub (continuous_apply 0)).sub (continuous_apply 1))))
  intro x
  exact (mul_pos (mul_pos
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250) (le_max_left _ _))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250) (le_max_left _ _)))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250) (le_max_left _ _))).ne'

/-- A global explicit bound for the continuous prime extension. -/
theorem p5U7PrimeEtaExtension_norm_le (x : Fin 2 → ℝ) :
    ‖p5U7PrimeEtaExtension x‖ ≤ 1 / (59/250 : ℝ)^3 := by
  let d : ℝ := 59/250
  let a := max d (x 0)
  let b := max d (x 1)
  let c := max d (1-x 0-x 1)
  have hd : 0 < d := by norm_num [d]
  have ha : d ≤ a := le_max_left _ _
  have hb : d ≤ b := le_max_left _ _
  have hc : d ≤ c := le_max_left _ _
  have ha0 : 0 < a := hd.trans_le ha
  have hb0 : 0 < b := hd.trans_le hb
  have hc0 : 0 < c := hd.trans_le hc
  have hden : d^3 ≤ a*b*c := by
    calc
      d^3 = (d*d)*d := by ring
      _ ≤ (a*b)*c := mul_le_mul (mul_le_mul ha hb hd.le ha0.le) hc hd.le
        (mul_nonneg ha0.le hb0.le)
  change ‖1/(a*b*c)‖ ≤ 1/d^3
  rw [Real.norm_eq_abs,abs_of_nonneg (one_div_nonneg.mpr (by positivity))]
  exact one_div_le_one_div_of_le (by positivity) hden

theorem p5U7PrimeEtaExtension_eq {eta : ℝ} (heta : 0 ≤ eta)
    {x : Fin 2 → ℝ} (hx : x ∈ p5U7EtaDomain eta) :
    p5U7PrimeEtaExtension x = p5U7ComponentPrimeKernel (x 0) (x 1) := by
  have h0 := ((mem_logPrimeBox.mp hx.1) 0).1
  have h1 := ((mem_logPrimeBox.mp hx.1) 1).1
  have hgap := (p5U7PrimeLeading_domain_geometry heta hx).2
  simp only [p5U7PrimeEtaExtension,p5U7ComponentPrimeKernel,
    max_eq_right h0,max_eq_right h1,max_eq_right hgap]

theorem p5U7PrimeEtaSample_aestronglyMeasurable (eta : ℝ) :
    AEStronglyMeasurable (p5U7PrimeEtaSample eta) :=
  (continuous_p5U7PrimeEtaExtension.stronglyMeasurable.indicator
    (measurableSet_p5U7EtaDomain eta)).aestronglyMeasurable

theorem p5U7PrimeEtaDomination_integrable : Integrable p5U7PrimeEtaDomination := by
  have hc : IntegrableOn (fun _ : Fin 2 → ℝ => 1/(59/250 : ℝ)^3)
      (Icc (fun _ : Fin 2 => (59/250 : ℝ)) (fun _ => (1/2 : ℝ))) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hsub : p5U7EtaCube ⊆ Icc (fun _ : Fin 2 => (59/250 : ℝ))
      (fun _ => (1/2 : ℝ)) := by
    intro x hx
    exact ⟨fun i => ((mem_logPrimeBox.mp hx) i).1,
      fun i => ((mem_logPrimeBox.mp hx) i).2.le⟩
  exact (hc.mono_set hsub).integrable_indicator (measurableSet_logPrimeBox _ _)

theorem p5U7PrimeEtaSample_dominated (eta : ℝ) (x : Fin 2 → ℝ) :
    ‖p5U7PrimeEtaSample eta x‖ ≤ p5U7PrimeEtaDomination x := by
  by_cases hc : x ∈ p5U7EtaCube
  · rw [p5U7PrimeEtaDomination,indicator_of_mem hc]
    by_cases hd : x ∈ p5U7EtaDomain eta
    · rw [p5U7PrimeEtaSample,indicator_of_mem hd]
      exact p5U7PrimeEtaExtension_norm_le x
    · rw [p5U7PrimeEtaSample,indicator_of_notMem hd,norm_zero]
      positivity
  · have hd : x ∉ p5U7EtaDomain eta := fun h => hc h.1
    rw [p5U7PrimeEtaSample,indicator_of_notMem hd,norm_zero,
      p5U7PrimeEtaDomination,indicator_of_notMem hc]

/-- Literal gate membership eventually stabilizes at EVERY point.
Points on a strict wall stay excluded for every nonnegative eta. -/
theorem p5U7EtaDomain_eventually_membership (x : Fin 2 → ℝ) :
    ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0,
      (x ∈ p5U7EtaDomain eta ↔ x ∈ p5U7EtaDomain 0) := by
  have hnonneg : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0, 0 ≤ eta := self_mem_nhdsWithin
  by_cases hx : x ∈ p5U7EtaDomain 0
  · obtain ⟨ho,hcap⟩ := (p5U7InteriorRegion_iff 0 x).mp hx.2
    have hx1 : 0 < x 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250)
      ((mem_logPrimeBox.mp hx.1) 1).1
    let r : ℝ := (1-x 0-2*x 1)/(2*x 1)
    have hr : 0 < r := by dsimp only [r]; apply div_pos <;> linarith only [hcap,hx1]
    have hsmall : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0, eta < r :=
      nhdsWithin_le_nhds (Iio_mem_nhds hr)
    filter_upwards [hsmall] with eta heta
    have hprod := mul_lt_mul_of_pos_right heta hx1
    have heq : r*x 1 = (1-x 0-2*x 1)/2 := by
      dsimp only [r]
      field_simp [hx1.ne']
      <;> ring
    rw [heq] at hprod
    have hxe : x ∈ p5U7EtaDomain eta := ⟨hx.1,(p5U7InteriorRegion_iff eta x).mpr
      ⟨ho,by nlinarith only [hprod,hcap]⟩⟩
    exact ⟨fun _ => hx,fun _ => hxe⟩
  · filter_upwards [hnonneg] with eta heta
    have hxe : x ∉ p5U7EtaDomain eta := fun h => hx (p5U7EtaDomain_mono_zero heta h)
    exact ⟨fun h => (hxe h).elim,fun h => (hx h).elim⟩

theorem tendsto_p5U7PrimeEtaSample (x : Fin 2 → ℝ) :
    Tendsto (fun eta : ℝ => p5U7PrimeEtaSample eta x) (𝓝[Ici 0] 0)
      (𝓝 (p5U7PrimeEtaSample 0 x)) := by
  have heq : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0,
      p5U7PrimeEtaSample eta x = p5U7PrimeEtaSample 0 x := by
    filter_upwards [p5U7EtaDomain_eventually_membership x] with eta heta
    by_cases hx : x ∈ p5U7EtaDomain 0
    · simp only [p5U7PrimeEtaSample,indicator_of_mem hx,indicator_of_mem (heta.mpr hx)]
    · have hxe : x ∉ p5U7EtaDomain eta := fun h => hx (heta.mp h)
      simp only [p5U7PrimeEtaSample,indicator_of_notMem hx,indicator_of_notMem hxe]
  exact tendsto_const_nhds.congr' heq.symm

theorem integral_p5U7PrimeEtaSample (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ x, p5U7PrimeEtaSample eta x) = p5U7PrimeLeadingIntegral eta := by
  rw [p5U7PrimeEtaSample,integral_indicator (measurableSet_p5U7EtaDomain eta)]
  exact setIntegral_congr_fun (measurableSet_p5U7EtaDomain eta)
    (fun x hx => p5U7PrimeEtaExtension_eq heta hx)

/-- Genuine DCT for the literal prime leading integral, with proved
compact integrable domination and pointwise gate convergence. -/
theorem tendsto_p5U7PrimeLeadingIntegral_eta_zero :
    Tendsto p5U7PrimeLeadingIntegral (𝓝[Ici (0 : ℝ)] 0)
      (𝓝 (p5U7PrimeLeadingIntegral 0)) := by
  have hh := tendsto_integral_filter_of_dominated_convergence p5U7PrimeEtaDomination
    (Eventually.of_forall p5U7PrimeEtaSample_aestronglyMeasurable)
    (Eventually.of_forall (fun eta => Eventually.of_forall (p5U7PrimeEtaSample_dominated eta)))
    p5U7PrimeEtaDomination_integrable (Eventually.of_forall tendsto_p5U7PrimeEtaSample)
  rw [integral_p5U7PrimeEtaSample 0 (by norm_num)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin : ∀ᶠ eta : ℝ in 𝓝[Ici 0] 0, 0 ≤ eta] with eta heta
  exact integral_p5U7PrimeEtaSample eta heta
end
end ImbalancedChen

