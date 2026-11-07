import ImbalancedChen.P5U7InteriorDoublePrimeTest
import ImbalancedChen.P5U7OriginalOmegaFubini
import Mathlib.MeasureTheory.Measure.Prod

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The zero-margin marked two-prime test integrates over a strict order wall
and a strict square-root wall.  This dictionary pays both walls as genuine
Lebesgue-null graphs, transports Fin 2 coordinates through piFinTwo, and
reuses the proved original compact-triangle Fubini theorem.  No prime mean,
distribution estimate, integral enclosure, or boundary-removal premise is
assumed.
-/

namespace ImbalancedChen

noncomputable section

open Set MeasureTheory
open scoped Topology
open Classical

private theorem p5U7Original_walls_ae :
    ∀ᵐ p : ℝ × ℝ, p.2 ≠ p.1 ∧ p.2 ≠ (1 - p.1) / 2 := by
  have hm : MeasurableSet
      {p : ℝ × ℝ | p.2 ≠ p.1 ∧ p.2 ≠ (1 - p.1) / 2} :=
    (isClosed_eq continuous_snd continuous_fst).measurableSet.compl.inter
      (isClosed_eq continuous_snd
        ((continuous_const.sub continuous_fst).div_const 2)).measurableSet.compl
  rw [Measure.volume_eq_prod]
  apply (ae_prod_iff_ae_ae hm).mpr
  filter_upwards [] with t
  filter_upwards [volume.ae_ne t, volume.ae_ne ((1 - t) / 2)] with u htu hcap
  exact ⟨htu, hcap⟩

private theorem p5U7Original_zero_domain_iff {t u : ℝ}
    (hne : u ≠ t) (hcapne : u ≠ (1 - t) / 2) :
    ![t, u] ∈ logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
        (fun _ => (1 / 2 : ℝ)) ∩ p5U7InteriorRegion 0 ↔
      (t, u) ∈ p5U7OmegaTriangle := by
  constructor
  · rintro ⟨hb, hi⟩
    have ht := (mem_logPrimeBox.mp hb) (0 : Fin 2)
    obtain ⟨horder, hcap⟩ := (p5U7InteriorRegion_iff 0 ![t, u]).mp hi
    change t < u at horder
    change t + (2 + (0 : ℝ)) * u < 1 at hcap
    change p5U7OmegaClosedSupport t u
    exact ⟨ht.1, horder.le, by linarith⟩
  · intro h
    change p5U7OmegaClosedSupport t u at h
    have horder : t < u := lt_of_le_of_ne h.2.1 hne.symm
    have hcap : u < (1 - t) / 2 := lt_of_le_of_ne h.2.2 hcapne
    refine ⟨mem_logPrimeBox.mpr ?_, (p5U7InteriorRegion_iff 0 ![t, u]).mpr ?_⟩
    · intro i
      fin_cases i
      · change 59 / 250 ≤ t ∧ t < (1 / 2 : ℝ)
        exact ⟨h.1, by linarith⟩
      · change 59 / 250 ≤ u ∧ u < (1 / 2 : ℝ)
        exact ⟨h.1.trans h.2.1, by linarith [h.1]⟩
    · change t < u ∧ t + (2 + (0 : ℝ)) * u < 1
      exact ⟨horder, by linarith⟩

/-- The original full Buchstab integral is exactly the zero-margin
double-prime test integral; neither marked order nor a wall is discarded
as an arithmetic identity. -/
theorem p5U7InteriorOmegaIntegral_zero_eq_original :
    p5U7InteriorOmegaIntegral 0 = p5U7OriginalOmegaIntegral 1 := by
  let S := logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
    (fun _ => (1 / 2 : ℝ)) ∩ p5U7InteriorRegion 0
  let G := fun x : Fin 2 → ℝ => p5U7OmegaKernel 1 (x 0) (x 1)
  let F := S.indicator G
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hS : MeasurableSet S :=
    (measurableSet_logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
      (fun _ => (1 / 2 : ℝ))).inter
      (measurableSet_primeAffineGateRegion (p5U7InteriorForms 0) p5U7InteriorBounds)
  have hT : MeasurableSet p5U7OmegaTriangle := by
    exact ((isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_snd).inter
        (isClosed_le continuous_snd
          ((continuous_const.sub continuous_fst).div_const 2)))).measurableSet
  have hvec (t u : ℝ) : E.symm (t, u) = ![t, u] := by
    ext i
    fin_cases i <;> rfl
  have hae : (fun p : ℝ × ℝ => F (E.symm p)) =ᵐ[volume]
      p5U7OmegaTriangle.indicator (fun p => p5U7OmegaKernel 1 p.1 p.2) := by
    filter_upwards [p5U7Original_walls_ae] with p hp
    have hm : E.symm p ∈ S ↔ p ∈ p5U7OmegaTriangle := by
      rw [show p = (p.1, p.2) from rfl, hvec]
      exact p5U7Original_zero_domain_iff hp.1 hp.2
    by_cases ht : p ∈ p5U7OmegaTriangle
    · have hs := hm.mpr ht
      change S.indicator G (E.symm p) = _
      rw [indicator_of_mem hs, indicator_of_mem ht]
      rw [show p = (p.1, p.2) from rfl, hvec]
      rfl
    · have hs : E.symm p ∉ S := fun hs => ht (hm.mp hs)
      change S.indicator G (E.symm p) = _
      rw [indicator_of_notMem hs, indicator_of_notMem ht]
  calc
    p5U7InteriorOmegaIntegral 0 = ∫ x, F x := (integral_indicator hS).symm
    _ = ∫ p : ℝ × ℝ, F (E.symm p) := (hE.symm.integral_comp' F).symm
    _ = ∫ p : ℝ × ℝ, p5U7OmegaTriangle.indicator
        (fun p => p5U7OmegaKernel 1 p.1 p.2) p := integral_congr_ae hae
    _ = ∫ p in p5U7OmegaTriangle, p5U7OmegaKernel 1 p.1 p.2 := integral_indicator hT
    _ = p5U7OriginalOmegaIntegral 1 := p5U7Omega_triangle_integral_eq_nested 1

end

end ImbalancedChen
