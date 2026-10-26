import ImbalancedChen.P5U7PrimeIntegralEtaZero
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Density-independent zero-cutoff coordinate dictionary and genuine prime
triangle Fubini. Only analytic Lebesgue-null graphs are used to compare
strict and closed integration domains. Arithmetic endpoint atoms remain
in the terminal/window estimates imported by the component mean.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

/-- The zero eta domain and the closed original triangle differ only on
these two analytic graphs; no finite prime selector is identified here. -/
theorem p5U7EtaZero_walls_ae :
    ∀ᵐ p : ℝ × ℝ, p.2 ≠ p.1 ∧ p.2 ≠ (1-p.1)/2 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.2 ≠ p.1 ∧ p.2 ≠ (1-p.1)/2} :=
    (isClosed_eq continuous_snd continuous_fst).measurableSet.compl.inter
      (isClosed_eq continuous_snd
        ((continuous_const.sub continuous_fst).div_const 2)).measurableSet.compl
  rw [Measure.volume_eq_prod]
  apply (ae_prod_iff_ae_ae hm).mpr
  filter_upwards [] with t
  filter_upwards [volume.ae_ne t,volume.ae_ne ((1-t)/2)] with u htu hcap
  exact ⟨htu,hcap⟩

theorem p5U7EtaZero_domain_iff {t u : ℝ} (hne : u ≠ t)
    (hcapne : u ≠ (1-t)/2) :
    ![t,u] ∈ p5U7EtaDomain 0 ↔ (t,u) ∈ p5U7OmegaTriangle := by
  constructor
  · rintro ⟨hb,hi⟩
    have ht := (mem_logPrimeBox.mp hb) (0 : Fin 2)
    obtain ⟨horder,hcap⟩ := (p5U7InteriorRegion_iff 0 ![t,u]).mp hi
    change t < u at horder
    change t+(2+(0 : ℝ))*u < 1 at hcap
    change p5U7OmegaClosedSupport t u
    exact ⟨ht.1,horder.le,by linarith⟩
  · intro h
    change p5U7OmegaClosedSupport t u at h
    have horder : t < u := lt_of_le_of_ne h.2.1 hne.symm
    have hcap : u < (1-t)/2 := lt_of_le_of_ne h.2.2 hcapne
    refine ⟨mem_logPrimeBox.mpr ?_,(p5U7InteriorRegion_iff 0 ![t,u]).mpr ?_⟩
    · intro i
      fin_cases i
      · change 59/250 ≤ t ∧ t < (1/2 : ℝ)
        exact ⟨h.1,by linarith⟩
      · change 59/250 ≤ u ∧ u < (1/2 : ℝ)
        exact ⟨h.1.trans h.2.1,by linarith [h.1]⟩
    · change t < u ∧ t+(2+(0 : ℝ))*u < 1
      exact ⟨horder,by linarith⟩

/-- A density-independent coordinate dictionary for the literal zero
cutoff. The integral identity does not assume integrability of f. -/
theorem p5U7EtaZero_integral_coordinate_dictionary (f : (Fin 2 → ℝ) → ℝ) :
    (∫ x in p5U7EtaDomain 0, f x) =
      ∫ p in p5U7OmegaTriangle, f ![p.1,p.2] := by
  let S := p5U7EtaDomain 0
  let F := S.indicator f
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hS : MeasurableSet S := measurableSet_p5U7EtaDomain 0
  have hT : MeasurableSet p5U7OmegaTriangle :=
    ((isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_snd).inter
        (isClosed_le continuous_snd ((continuous_const.sub continuous_fst).div_const 2)))).measurableSet
  have hvec (t u : ℝ) : E.symm (t,u) = ![t,u] := by
    ext i
    fin_cases i <;> rfl
  have hae : (fun p : ℝ × ℝ => F (E.symm p)) =ᵐ[volume]
      p5U7OmegaTriangle.indicator (fun p => f ![p.1,p.2]) := by
    filter_upwards [p5U7EtaZero_walls_ae] with p hp
    have hm : E.symm p ∈ S ↔ p ∈ p5U7OmegaTriangle := by
      rw [show p = (p.1,p.2) from rfl,hvec]
      exact p5U7EtaZero_domain_iff hp.1 hp.2
    by_cases ht : p ∈ p5U7OmegaTriangle
    · have hs := hm.mpr ht
      change S.indicator f (E.symm p) = _
      rw [indicator_of_mem hs,indicator_of_mem ht]
      rw [show p = (p.1,p.2) from rfl,hvec]
    · have hs : E.symm p ∉ S := fun hs => ht (hm.mp hs)
      change S.indicator f (E.symm p) = _
      rw [indicator_of_notMem hs,indicator_of_notMem ht]
  calc
    _ = ∫ x, F x := (integral_indicator hS).symm
    _ = ∫ p : ℝ × ℝ, F (E.symm p) := (hE.symm.integral_comp' F).symm
    _ = ∫ p : ℝ × ℝ, p5U7OmegaTriangle.indicator (fun p => f ![p.1,p.2]) p :=
      integral_congr_ae hae
    _ = _ := integral_indicator hT

/-- The bounded continuous extension agrees on the CLOSED triangle,
including the order wall and t=1/3 zero-width endpoint. -/
theorem p5U7PrimeEtaExtension_eq_triangle {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) :
    p5U7PrimeEtaExtension ![t,u] = p5U7ComponentPrimeKernel t u := by
  have hu : (59/250 : ℝ) ≤ u := h.1.trans h.2.1
  have hgap : (59/250 : ℝ) ≤ 1-t-u := by linarith [h.2.2]
  change 1/(max (59/250 : ℝ) t * max (59/250 : ℝ) u *
    max (59/250 : ℝ) (1-t-u)) = 1/(t*u*(1-t-u))
  rw [max_eq_right h.1,max_eq_right hu,max_eq_right hgap]

/-- Product-triangle Fubini for the actual prime component. The global
extension supplies integrability on the bounding rectangle despite the
raw kernel's pole outside the genuine triangle. -/
theorem p5U7ComponentPrime_triangle_integral_eq_nested :
    (∫ p in p5U7OmegaTriangle, p5U7ComponentPrimeKernel p.1 p.2) =
      p5U7ComponentPrimeIntegral := by
  let B : Set (ℝ × ℝ) := Icc (59/250 : ℝ) (1/3) ×ˢ Icc (59/250 : ℝ) 1
  let O : Set (ℝ × ℝ) := {p | p.1 ≤ p.2 ∧ p.2 ≤ (1-p.1)/2}
  let g : ℝ × ℝ → ℝ := fun p => p5U7PrimeEtaExtension ![p.1,p.2]
  have hg : Continuous g := by
    apply continuous_p5U7PrimeEtaExtension.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have hO : MeasurableSet O :=
    ((isClosed_le continuous_fst continuous_snd).inter
      (isClosed_le continuous_snd ((continuous_const.sub continuous_fst).div_const 2))).measurableSet
  have hT : MeasurableSet p5U7OmegaTriangle :=
    ((isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_snd).inter
        (isClosed_le continuous_snd ((continuous_const.sub continuous_fst).div_const 2)))).measurableSet
  have hset : B ∩ O = p5U7OmegaTriangle := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1.1.1,hp.2⟩
    · intro hp
      have ht := (p5U7Omega_closed_geometry hp).2.2.2.1
      exact ⟨⟨⟨hp.1,ht⟩,⟨hp.1.trans hp.2.1,by linarith [hp.1,hp.2.2]⟩⟩,hp.2⟩
  have hiB : IntegrableOn g B := hg.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hfubini : (∫ p in p5U7OmegaTriangle, g p) =
      ∫ t in Icc (59/250 : ℝ) (1/3),
        ∫ u in Icc (59/250 : ℝ) 1, O.indicator g (t,u) := by
    calc
      _ = ∫ p in B, O.indicator g p := by rw [setIntegral_indicator hO,hset]
      _ = _ := by
        rw [B,Measure.volume_eq_prod]
        exact setIntegral_prod _ (by
          simpa only [B,Measure.volume_eq_prod] using hiB.indicator hO)
  have hinner : ∀ t ∈ Icc (59/250 : ℝ) (1/3),
      (∫ u in Icc (59/250 : ℝ) 1, O.indicator g (t,u)) = p5U7ComponentPrimeRow t := by
    intro t ht
    have heq : (fun u => O.indicator g (t,u)) =
        (Icc t ((1-t)/2)).indicator (fun u => g (t,u)) := by
      funext u
      by_cases h : t ≤ u ∧ u ≤ (1-t)/2 <;> simp [O,h]
    rw [heq,setIntegral_indicator measurableSet_Icc]
    have hsub : Icc (59/250 : ℝ) 1 ∩ Icc t ((1-t)/2) = Icc t ((1-t)/2) := by
      apply inter_eq_right.mpr
      intro u hu
      exact ⟨ht.1.trans hu.1,by linarith [hu.2,ht.1]⟩
    rw [hsub,integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [ht.2] : t ≤ (1-t)/2)]
    unfold p5U7ComponentPrimeRow
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by linarith [ht.2] : t ≤ (1-t)/2)] at hu
    exact p5U7PrimeEtaExtension_eq_triangle ⟨ht.1,hu.1,hu.2⟩
  calc
    _ = ∫ p in p5U7OmegaTriangle, g p := by
      apply setIntegral_congr_fun hT
      intro p hp
      exact (p5U7PrimeEtaExtension_eq_triangle hp).symm
    _ = ∫ t in Icc (59/250 : ℝ) (1/3), p5U7ComponentPrimeRow t :=
      hfubini.trans (setIntegral_congr_fun measurableSet_Icc hinner)
    _ = p5U7ComponentPrimeIntegral := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (59/250 : ℝ) ≤ 1/3)]
      rfl

/-- Literal zero-cutoff prime integral identified with the independent
nested integral constant; endpoint handling is an analytic dictionary. -/
theorem p5U7PrimeLeadingIntegral_zero_eq_component :
    p5U7PrimeLeadingIntegral 0 = p5U7ComponentPrimeIntegral := by
  unfold p5U7PrimeLeadingIntegral
  rw [p5U7EtaZero_integral_coordinate_dictionary]
  exact p5U7ComponentPrime_triangle_integral_eq_nested

/-- Continuous removal of the positive prime cutoff to the original
one-dimensional prime leading integral. -/
theorem tendsto_p5U7PrimeLeadingIntegral_to_component :
    Tendsto p5U7PrimeLeadingIntegral (𝓝[Ici (0 : ℝ)] 0)
      (𝓝 p5U7ComponentPrimeIntegral) := by
  rw [← p5U7PrimeLeadingIntegral_zero_eq_component]
  exact tendsto_p5U7PrimeLeadingIntegral_eta_zero
end
end ImbalancedChen
