import ImbalancedChen.P5U7PrimeIntegralZeroDictionary

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact fixed-cutoff Fubini for the prime leading component. A clamped
inner endpoint retains empty rows when eta is large. Analytic graph
endpoints are treated explicitly; no arithmetic selector is altered.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7PrimeCutoffTriangle (eta : ℝ) : Set (ℝ × ℝ) :=
  {p | (59/250 : ℝ) ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ (1-p.1)/(2+eta)}

def p5U7PrimeCutoffRow (eta t : ℝ) : ℝ :=
  ∫ u in t..max t ((1-t)/(2+eta)), p5U7PrimeEtaExtension ![t,u]

theorem p5U7PrimeCutoffTriangle_subset {eta : ℝ} (heta : 0 ≤ eta) :
    p5U7PrimeCutoffTriangle eta ⊆ p5U7OmegaTriangle := by
  intro p hp
  have hden : 0 < 2+eta := by linarith
  have hu : 0 < p.2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250)
    (hp.1.trans hp.2.1)
  have hmul := (le_div_iff₀ hden).mp hp.2.2
  refine ⟨hp.1,hp.2.1,?_⟩
  nlinarith [mul_nonneg heta hu.le]

theorem p5U7PrimeCutoff_cap_le {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    (1-t)/(2+eta) ≤ (1-t)/2 := by
  exact div_le_div_of_nonneg_left (by linarith [ht.2]) (by norm_num)
    (by linarith : (2 : ℝ) ≤ 2+eta)

theorem p5U7PrimeCutoff_domain_iff {eta t u : ℝ} (heta : 0 ≤ eta)
    (hne : u ≠ t) (hcapne : u ≠ (1-t)/(2+eta)) :
    ![t,u] ∈ p5U7EtaDomain eta ↔ (t,u) ∈ p5U7PrimeCutoffTriangle eta := by
  have hden : 0 < 2+eta := by linarith
  constructor
  · rintro ⟨hb,hi⟩
    have ht := ((mem_logPrimeBox.mp hb) 0).1
    obtain ⟨ho,hcap⟩ := (p5U7InteriorRegion_iff eta ![t,u]).mp hi
    change t < u at ho
    change t+(2+eta)*u < 1 at hcap
    exact ⟨ht,ho.le,((lt_div_iff₀ hden).mpr (by nlinarith only [hcap])).le⟩
  · intro h
    have hs := p5U7PrimeCutoffTriangle_subset heta h
    have ho : t < u := lt_of_le_of_ne h.2.1 hne.symm
    have hcap : u < (1-t)/(2+eta) := lt_of_le_of_ne h.2.2 hcapne
    refine ⟨mem_logPrimeBox.mpr ?_,(p5U7InteriorRegion_iff eta ![t,u]).mpr ?_⟩
    · intro i
      fin_cases i
      · change 59/250 ≤ t ∧ t < (1/2 : ℝ)
        exact ⟨h.1,by linarith [hs.2.1,hs.2.2]⟩
      · change 59/250 ≤ u ∧ u < (1/2 : ℝ)
        exact ⟨h.1.trans h.2.1,by linarith [h.1,hs.2.2]⟩
    · change t < u ∧ t+(2+eta)*u < 1
      exact ⟨ho,by have hm := (lt_div_iff₀ hden).mp hcap; nlinarith only [hm]⟩

/-- Cutoff graph endpoints are Lebesgue-null in the analytic dictionary. -/
theorem p5U7PrimeCutoff_walls_ae (eta : ℝ) :
    ∀ᵐ p : ℝ × ℝ, p.2 ≠ p.1 ∧ p.2 ≠ (1-p.1)/(2+eta) := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.2 ≠ p.1 ∧ p.2 ≠ (1-p.1)/(2+eta)} :=
    (isClosed_eq continuous_snd continuous_fst).measurableSet.compl.inter
      (isClosed_eq continuous_snd
        ((continuous_const.sub continuous_fst).div_const (2+eta))).measurableSet.compl
  rw [Measure.volume_eq_prod]
  apply (ae_prod_iff_ae_ae hm).mpr
  filter_upwards [] with t
  filter_upwards [volume.ae_ne t,volume.ae_ne ((1-t)/(2+eta))] with u htu hcap
  exact ⟨htu,hcap⟩

theorem measurableSet_p5U7PrimeCutoffTriangle (eta : ℝ) :
    MeasurableSet (p5U7PrimeCutoffTriangle eta) :=
  ((isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_snd).inter
      (isClosed_le continuous_snd
        ((continuous_const.sub continuous_fst).div_const (2+eta))))).measurableSet

/-- The literal prime cutoff has a product-triangle coordinate formula. -/
theorem p5U7PrimeLeadingIntegral_eq_cutoff_triangle (eta : ℝ) (heta : 0 ≤ eta) :
    p5U7PrimeLeadingIntegral eta =
      ∫ p in p5U7PrimeCutoffTriangle eta, p5U7PrimeEtaExtension ![p.1,p.2] := by
  let S := p5U7EtaDomain eta
  let F := S.indicator p5U7PrimeEtaExtension
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hS : MeasurableSet S := measurableSet_p5U7EtaDomain eta
  have hT := measurableSet_p5U7PrimeCutoffTriangle eta
  have hvec (t u : ℝ) : E.symm (t,u) = ![t,u] := by
    ext i
    fin_cases i <;> rfl
  have hae : (fun p : ℝ × ℝ => F (E.symm p)) =ᵐ[volume]
      (p5U7PrimeCutoffTriangle eta).indicator
        (fun p => p5U7PrimeEtaExtension ![p.1,p.2]) := by
    filter_upwards [p5U7PrimeCutoff_walls_ae eta] with p hp
    have hm : E.symm p ∈ S ↔ p ∈ p5U7PrimeCutoffTriangle eta := by
      rw [show p = (p.1,p.2) from rfl,hvec]
      exact p5U7PrimeCutoff_domain_iff heta hp.1 hp.2
    by_cases ht : p ∈ p5U7PrimeCutoffTriangle eta
    · have hs := hm.mpr ht
      change S.indicator p5U7PrimeEtaExtension (E.symm p) = _
      rw [indicator_of_mem hs,indicator_of_mem ht]
      rw [show p = (p.1,p.2) from rfl,hvec]
    · have hs : E.symm p ∉ S := fun hs => ht (hm.mp hs)
      change S.indicator p5U7PrimeEtaExtension (E.symm p) = _
      rw [indicator_of_notMem hs,indicator_of_notMem ht]
  calc
    _ = ∫ x, F x := (integral_p5U7PrimeEtaSample eta heta).symm
    _ = ∫ p : ℝ × ℝ, F (E.symm p) := (hE.symm.integral_comp' F).symm
    _ = ∫ p : ℝ × ℝ, (p5U7PrimeCutoffTriangle eta).indicator
        (fun p => p5U7PrimeEtaExtension ![p.1,p.2]) p := integral_congr_ae hae
    _ = _ := integral_indicator hT

/-- Genuine fixed-cutoff Fubini with the exact clamp for an empty row. -/
theorem p5U7PrimeLeadingIntegral_eq_cutoff_rows (eta : ℝ) (heta : 0 ≤ eta) :
    p5U7PrimeLeadingIntegral eta =
      ∫ t in (59/250 : ℝ)..(1/3 : ℝ), p5U7PrimeCutoffRow eta t := by
  let B : Set (ℝ × ℝ) := Icc (59/250 : ℝ) (1/3) ×ˢ Icc (59/250 : ℝ) 1
  let O : Set (ℝ × ℝ) := {p | p.1 ≤ p.2 ∧ p.2 ≤ (1-p.1)/(2+eta)}
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
      (isClosed_le continuous_snd
        ((continuous_const.sub continuous_fst).div_const (2+eta)))).measurableSet
  have hset : B ∩ O = p5U7PrimeCutoffTriangle eta := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1.1.1,hp.2⟩
    · intro hp
      have hs := p5U7PrimeCutoffTriangle_subset heta hp
      have ht := (p5U7Omega_closed_geometry hs).2.2.2.1
      exact ⟨⟨⟨hp.1,ht⟩,⟨hp.1.trans hp.2.1,by linarith [hp.1,hs.2.2]⟩⟩,hp.2⟩
  have hiB : IntegrableOn g B := hg.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hfubini : (∫ p in p5U7PrimeCutoffTriangle eta, g p) =
      ∫ t in Icc (59/250 : ℝ) (1/3),
        ∫ u in Icc (59/250 : ℝ) 1, O.indicator g (t,u) := by
    calc
      _ = ∫ p in B, O.indicator g p := by rw [setIntegral_indicator hO,hset]
      _ = _ := by
        rw [B,Measure.volume_eq_prod]
        exact setIntegral_prod _ (by
          simpa only [B,Measure.volume_eq_prod] using hiB.indicator hO)
  have hinner : ∀ t ∈ Icc (59/250 : ℝ) (1/3),
      (∫ u in Icc (59/250 : ℝ) 1, O.indicator g (t,u)) = p5U7PrimeCutoffRow eta t := by
    intro t ht
    have heq : (fun u => O.indicator g (t,u)) =
        (Icc t ((1-t)/(2+eta))).indicator (fun u => g (t,u)) := by
      funext u
      by_cases h : t ≤ u ∧ u ≤ (1-t)/(2+eta) <;> simp [O,h]
    rw [heq,setIntegral_indicator measurableSet_Icc]
    have hsub : Icc (59/250 : ℝ) 1 ∩ Icc t ((1-t)/(2+eta)) = Icc t ((1-t)/(2+eta)) := by
      apply inter_eq_right.mpr
      intro u hu
      have hcap := p5U7PrimeCutoff_cap_le heta ht
      exact ⟨ht.1.trans hu.1,by linarith [hu.2,hcap,ht.1]⟩
    rw [hsub]
    by_cases htc : t ≤ (1-t)/(2+eta)
    · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le htc]
      simp only [p5U7PrimeCutoffRow,max_eq_right htc]
      rfl
    · have hct : (1-t)/(2+eta) < t := lt_of_not_ge htc
      rw [Icc_eq_empty hct]
      simp only [integral_empty,p5U7PrimeCutoffRow,max_eq_left hct.le,
        intervalIntegral.integral_same]
  calc
    _ = ∫ p in p5U7PrimeCutoffTriangle eta, g p :=
      p5U7PrimeLeadingIntegral_eq_cutoff_triangle eta heta
    _ = ∫ t in Icc (59/250 : ℝ) (1/3), p5U7PrimeCutoffRow eta t :=
      hfubini.trans (setIntegral_congr_fun measurableSet_Icc hinner)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (59/250 : ℝ) ≤ 1/3)]
end
end ImbalancedChen
