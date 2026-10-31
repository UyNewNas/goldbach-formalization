import ImbalancedChen.Certificates.P2AdoptedUnionIntegral
import ImbalancedChen.Certificates.PairedV2FullCertificate
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY; uncompiled. The first import names the intended installation
of the adjacent `P2AdoptedUnionIntegral.lean` candidate.

Actual coordinate equivalences and successive integrations for the adopted
support. No coordinate-Fubini identity or endpoint enclosure is a premise.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedSupportFubini

open MeasureTheory Set
open scoped BigOperators Interval
open P2AdoptedUnion

noncomputable section

abbrev Point3 := Fin 3 → ℝ
abbrev Point2 := Fin 2 → ℝ

def split4 : Point ≃ᵐ ℝ × Point3 :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0

def split3 : Point3 ≃ᵐ ℝ × Point2 :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0

def split2 : Point2 ≃ᵐ ℝ × ℝ :=
  MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)

theorem split4_preserving : MeasurePreserving split4 := by
  exact volume_preserving_piFinSuccAbove _ 0

theorem split3_preserving : MeasurePreserving split3 := by
  exact volume_preserving_piFinSuccAbove _ 0

theorem split2_preserving : MeasurePreserving split2 := by
  exact volume_preserving_piFinTwo _

theorem split4_symm (t : ℝ) (v : Point3) :
    split4.symm (t, v) = Fin.cons t v := by
  ext i
  fin_cases i <;>
    simp [split4, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove]

theorem split3_symm (u : ℝ) (v : Point2) :
    split3.symm (u, v) = Fin.cons u v := by
  ext i
  fin_cases i <;>
    simp [split3, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove]

theorem split2_symm (z w : ℝ) : split2.symm (z, w) = ![z, w] := by
  ext i
  fin_cases i <;> rfl

def tInterval (r : Row) : Set ℝ :=
  Ioo (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ)

def uInterval (r : Row) : Set ℝ :=
  Ioo (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ)

def triangle (r : Row) : Set Point2 :=
  {v | (a : ℝ) < v 1 ∧ v 1 < v 0 ∧ v 0 < (cutoff r : ℝ)}

def tailSupport (r : Row) : Set Point3 := {v |
  (uLower (indices r).2 : ℝ) < v 0 ∧
  v 0 < (uUpper (indices r).2 : ℝ) ∧
  (a : ℝ) < v 2 ∧ v 2 < v 1 ∧ v 1 < (cutoff r : ℝ)}

def triangleKernel (v : Point2) : ℝ := (1 / v 0 ^ 2) * (1 / v 1)

def tailKernel (v : Point3) : ℝ :=
  (1 / v 0) * ((1 / v 1 ^ 2) * (1 / v 2))

def F4 (r : Row) : Point → ℝ := (support r).indicator rawKernel
def F3 (r : Row) : Point3 → ℝ := (tailSupport r).indicator tailKernel
def F2 (r : Row) : Point2 → ℝ := (triangle r).indicator triangleKernel
def tWeight (r : Row) : ℝ → ℝ := (tInterval r).indicator (fun t => 1 / t)
def uWeight (r : Row) : ℝ → ℝ := (uInterval r).indicator (fun u => 1 / u)

theorem first_coordinate_factor (r : Row) (t : ℝ) (v : Point3) :
    F4 r (split4.symm (t, v)) = tWeight r t * F3 r v := by
  rw [split4_symm]
  have htwo : Fin.cons (α := fun _ : Fin 4 => ℝ) t v (2 : Fin 4) = v 1 := by
    exact (Fin.cons_succ (α := fun _ : Fin 4 => ℝ) t v (1 : Fin 3))
  have hthree : Fin.cons (α := fun _ : Fin 4 => ℝ) t v (3 : Fin 4) = v 2 := by
    exact (Fin.cons_succ (α := fun _ : Fin 4 => ℝ) t v (2 : Fin 3))
  have hm : Fin.cons t v ∈ support r ↔ t ∈ tInterval r ∧ v ∈ tailSupport r := by
    simp [support, openFibreSet, openFibreSupport, tInterval, tailSupport, and_assoc, htwo, hthree]
  by_cases ht : t ∈ tInterval r <;> by_cases hv : v ∈ tailSupport r <;>
    simp [F4, F3, tWeight, hm, ht, hv, rawKernel, pairedFibreKernel, tailKernel, htwo, hthree]

theorem second_coordinate_factor (r : Row) (u : ℝ) (v : Point2) :
    F3 r (split3.symm (u, v)) = uWeight r u * F2 r v := by
  rw [split3_symm]
  have htwo : Fin.cons (α := fun _ : Fin 3 => ℝ) u v (2 : Fin 3) = v 1 := by
    exact (Fin.cons_succ (α := fun _ : Fin 3 => ℝ) u v (1 : Fin 2))
  have hm : Fin.cons u v ∈ tailSupport r ↔ u ∈ uInterval r ∧ v ∈ triangle r := by
    simp [tailSupport, uInterval, triangle, and_assoc, htwo]
  by_cases hu : u ∈ uInterval r <;> by_cases hv : v ∈ triangle r <;>
    simp [F3, F2, uWeight, hm, hu, hv, tailKernel, triangleKernel, htwo]

/-- Actual first coordinate Fubini: the t-variable separates from the
remaining adopted three-dimensional supported kernel. -/
theorem first_coordinate_integral (r : Row) :
    (∫ x : Point in support r, rawKernel x) =
      (∫ t in tInterval r, 1 / t) * ∫ v : Point3, F3 r v := by
  calc
    _ = ∫ x : Point, F4 r x := (integral_indicator (support_measurable r)).symm
    _ = ∫ p : ℝ × Point3, F4 r (split4.symm p) :=
      (split4_preserving.symm.integral_comp' (F4 r)).symm
    _ = ∫ p : ℝ × Point3, tWeight r p.1 * F3 r p.2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => first_coordinate_factor r p.1 p.2)
    _ = (∫ t, tWeight r t) * ∫ v : Point3, F3 r v := integral_prod_mul _ _
    _ = _ := by rw [tWeight, tInterval, integral_indicator measurableSet_Ioo]

/-- Actual second coordinate Fubini leaves precisely the triangular z,w
integral; no arbitrary function is substituted for the adopted kernel. -/
theorem second_coordinate_integral (r : Row) :
    (∫ v : Point3, F3 r v) =
      (∫ u in uInterval r, 1 / u) * ∫ v : Point2, F2 r v := by
  calc
    _ = ∫ p : ℝ × Point2, F3 r (split3.symm p) :=
      (split3_preserving.symm.integral_comp' (F3 r)).symm
    _ = ∫ p : ℝ × Point2, uWeight r p.1 * F2 r p.2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => second_coordinate_factor r p.1 p.2)
    _ = (∫ u, uWeight r u) * ∫ v : Point2, F2 r v := integral_prod_mul _ _
    _ = _ := by rw [uWeight, uInterval, integral_indicator measurableSet_Ioo]

theorem first_two_coordinate_integrals (r : Row) :
    (∫ x : Point in support r, rawKernel x) =
      (∫ t in tInterval r, 1 / t) * (∫ u in uInterval r, 1 / u) *
        ∫ v : Point2, F2 r v := by
  rw [first_coordinate_integral, second_coordinate_integral, mul_assoc]

def triangleBox (r : Row) : Set Point2 :=
  Icc (fun _ => (a : ℝ)) (fun _ => (cutoff r : ℝ))

theorem triangle_measurable (r : Row) : MeasurableSet (triangle r) := by
  exact ((isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt (continuous_apply 1) (continuous_apply 0)).inter
      (isOpen_lt (continuous_apply 0) continuous_const))).measurableSet

theorem triangle_subset_box (r : Row) : triangle r ⊆ triangleBox r := by
  intro v hv
  rcases hv with ⟨haw, hwz, hzZ⟩
  change (fun _ => (a : ℝ)) ≤ v ∧ v ≤ (fun _ => (cutoff r : ℝ))
  constructor <;> intro i <;> fin_cases i <;> dsimp <;> linarith

theorem triangleKernel_continuousOn (r : Row) :
    ContinuousOn triangleKernel (triangleBox r) := by
  have hc (i : Fin 2) : ContinuousOn (fun v : Point2 => v i) (triangleBox r) :=
    (continuous_apply i).continuousOn
  have hn (i : Fin 2) (v : Point2) (hv : v ∈ triangleBox r) : v i ≠ 0 :=
    (a_pos.trans_le (hv.1 i)).ne'
  exact (continuousOn_const.div ((hc 0).pow 2)
    (fun v hv => pow_ne_zero 2 (hn 0 v hv))).mul
      (continuousOn_const.div (hc 1) (hn 1))

theorem integrable_F2 (r : Row) : Integrable (F2 r) := by
  have hi : IntegrableOn triangleKernel (triangle r) :=
    ((triangleKernel_continuousOn r).integrableOn_compact isCompact_Icc).mono_set
      (triangle_subset_box r)
  exact hi.integrable_indicator (triangle_measurable r)

theorem triangle_vector_indicator (r : Row) (z w : ℝ) :
    F2 r ![z, w] =
      (Ioo (a : ℝ) (cutoff r : ℝ)).indicator
        (fun z => (1 / z ^ 2) *
          (Ioo (a : ℝ) z).indicator (fun w => 1 / w) w) z := by
  have hm : ![z, w] ∈ triangle r ↔
      z ∈ Ioo (a : ℝ) (cutoff r : ℝ) ∧ w ∈ Ioo (a : ℝ) z := by
    change ((a : ℝ) < w ∧ w < z ∧ z < (cutoff r : ℝ)) ↔
      (((a : ℝ) < z ∧ z < (cutoff r : ℝ)) ∧ (a : ℝ) < w ∧ w < z)
    constructor
    · rintro ⟨haw, hwz, hzZ⟩
      exact ⟨⟨haw.trans hwz, hzZ⟩, haw, hwz⟩
    · rintro ⟨⟨_, hzZ⟩, haw, hwz⟩
      exact ⟨haw, hwz, hzZ⟩
  by_cases hz : z ∈ Ioo (a : ℝ) (cutoff r : ℝ) <;>
    by_cases hw : w ∈ Ioo (a : ℝ) z <;>
      simp [F2, triangleKernel, hm, hz, hw]

/-- The final two coordinates use genuine Fubini, justified by the
proved integrability of the supported triangular reciprocal kernel. -/
theorem triangle_integral_nested (r : Row) :
    (∫ v : Point2, F2 r v) =
      ∫ z in Ioo (a : ℝ) (cutoff r : ℝ),
        (1 / z ^ 2) * ∫ w in Ioo (a : ℝ) z, 1 / w := by
  have hi : Integrable (fun p : ℝ × ℝ => F2 r (split2.symm p)) :=
    split2_preserving.symm.integrable_comp_of_integrable (integrable_F2 r)
  calc
    _ = ∫ p : ℝ × ℝ, F2 r (split2.symm p) :=
      (split2_preserving.symm.integral_comp' (F2 r)).symm
    _ = ∫ z : ℝ, ∫ w : ℝ, F2 r ![z, w] := by
      simpa only [Measure.volume_eq_prod, split2_symm] using integral_prod
        (fun p : ℝ × ℝ => F2 r (split2.symm p)) hi
    _ = ∫ z : ℝ, (Ioo (a : ℝ) (cutoff r : ℝ)).indicator
        (fun z => (1 / z ^ 2) * ∫ w in Ioo (a : ℝ) z, 1 / w) z := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun z => ?_)
      by_cases hz : z ∈ Ioo (a : ℝ) (cutoff r : ℝ)
      · rw [indicator_of_mem hz]
        simp_rw [triangle_vector_indicator, indicator_of_mem hz]
        rw [integral_const_mul, integral_indicator measurableSet_Ioo]
      · rw [indicator_of_notMem hz]
        simp_rw [triangle_vector_indicator, indicator_of_notMem hz]
        exact integral_zero ℝ ℝ
    _ = _ := integral_indicator measurableSet_Ioo

theorem triangle_integral_eq_fibre (r : Row) :
    (∫ v : Point2, F2 r v) = pairedFibreIntegral (a : ℝ) (cutoff r : ℝ) := by
  have haZ : (a : ℝ) ≤ (cutoff r : ℝ) :=
    Rat.cast_le.mpr (row_endpoint_bounds r).1.le
  rw [triangle_integral_nested]
  calc
    _ = ∫ z in (a : ℝ)..(cutoff r : ℝ),
        (1 / z ^ 2) * ∫ w in Ioo (a : ℝ) z, 1 / w := by
      rw [intervalIntegral.integral_of_le haZ, integral_Ioc_eq_integral_Ioo]
    _ = ∫ z in (a : ℝ)..(cutoff r : ℝ),
        (1 / z ^ 2) * ∫ w in (a : ℝ)..z, 1 / w := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [Set.uIcc_of_le haZ] at hz
      change (1 / z ^ 2) * (∫ w in Ioo (a : ℝ) z, 1 / w) =
        (1 / z ^ 2) * (∫ w in (a : ℝ)..z, 1 / w)
      rw [intervalIntegral.integral_of_le hz.1, integral_Ioc_eq_integral_Ioo]
    _ = _ := pairedFibreIntegral_eq_iterated a_pos haZ

theorem setIntegral_Ioo_one_div {l u : ℝ} (hl : 0 < l) (hu : 0 < u)
    (hlu : l ≤ u) : (∫ t in Ioo l u, 1 / t) = Real.log (u / l) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlu]
  exact integral_one_div_of_pos hl hu

/-- Local coordinate Fubini bridge for every actual adopted row. The
coefficient occurs once, and both sides are genuine Lebesgue integrals. -/
theorem support_setIntegral_eq_pairedLocalIntegral (r : Row) :
    ((K : ℝ) / 80) * (∫ x : Point in support r, rawKernel x) =
      pairedLocalIntegral (K : ℝ) a
        (tLower (indices r).1) (tUpper (indices r).1)
        (uLower (indices r).2) (uUpper (indices r).2) (cutoff r) := by
  obtain ⟨haZ, _, huu, _, hht, htu, _, _⟩ := row_endpoint_bounds r
  have haZR : (a : ℝ) ≤ (cutoff r : ℝ) := Rat.cast_le.mpr haZ.le
  have htuR : (tLower (indices r).1 : ℝ) ≤ (tUpper (indices r).1 : ℝ) :=
    Rat.cast_le.mpr htu.le
  have huuR : (uLower (indices r).2 : ℝ) ≤ (uUpper (indices r).2 : ℝ) :=
    Rat.cast_le.mpr huu.le
  have htl : (0 : ℝ) < (tLower (indices r).1 : ℝ) := by
    have hh : (0 : ℝ) < (h : ℝ) := by norm_num [h]
    exact hh.trans (Rat.cast_lt.mpr hht)
  have hul : (0 : ℝ) < (uLower (indices r).2 : ℝ) :=
    a_pos.trans_le (Rat.cast_le.mpr ((row_endpoint_bounds r).1.le.trans
      (row_endpoint_bounds r).2.1))
  rw [first_two_coordinate_integrals, triangle_integral_eq_fibre]
  rw [tInterval, uInterval,
    setIntegral_Ioo_one_div htl (htl.trans_le htuR) htuR,
    setIntegral_Ioo_one_div hul (hul.trans_le huuR) huuR,
    pairedFibreIntegral_eq a_pos haZR,
    pairedLocalIntegral_eq (K : ℝ) a_pos haZR htl (htl.trans_le htuR)
      hul (hul.trans_le huuR)]
  ring

/-- The genuine product-volume integral over all 17572 adopted fibres
is the pre-existing certified sum of actual iterated integrals. -/
theorem unionIntegral_eq_integral : P2AdoptedUnion.unionIntegral =
    ImbalancedChen.Certificates.PairedV2.FullMask.integral := by
  rw [P2AdoptedUnion.unionIntegral_eq_sum]
  unfold ImbalancedChen.Certificates.PairedV2.FullMask.integral
  apply Finset.sum_congr rfl
  intro r _
  exact support_setIntegral_eq_pairedLocalIntegral r

/-- Unconditional numerical enclosure of the genuine union integral. -/
theorem union_actual_enclosure :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤
        P2AdoptedUnion.unionIntegral ∧
      P2AdoptedUnion.unionIntegral ≤
        (55858409959907296 / 100000000000000000000 : ℝ) := by
  rw [unionIntegral_eq_integral]
  exact integral_bounds

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedSupportFubini
