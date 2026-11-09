import ImbalancedChen.P4AOriginalFull87EighthKernelControl
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An original-source quantitative lower comparison for the ACTUAL eighth
residual kernel, not merely positivity at a centre.  The numerator is
the same original finite-cap difference; no witness integral, physical
prime occurrence, asymptotic input or reserve payment is assumed.

This is intentionally downstream of the existing exact original
Source/cap/kernel.  A numerical bound for the right-hand side requires
a new, separately checked lower integral for the ORIGINAL cap gap.
-/

namespace ImbalancedChen.P4AOriginalFull87QuantitativeGapIntegral
noncomputable section

open scoped Classical BigOperators MeasureTheory
open Set Filter MeasureTheory VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87FiniteEighthCap
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87TrimOmission (source_volume_lt_top)

/-- Lower integrand on precisely the same original source.
Unlike the archived rational endpoint, this is an actual real function. -/
def scaledCapGap (c : Cell) (t : Point) : ℝ :=
  (4 / (9 * mu ^ 10)) * (newCap c t - comparison c t)

/-- On the ORIGINAL continuous source, each coordinate is positive and
bounded by the original first-coordinate upper cap mu. -/
private theorem source_coordinate_bounded_by_mu {c : Cell} {t : Point}
    (hs : Source c t) :
    0 < mu ∧ (∀ i : Fin 8, 0 ≤ t i ∧ t i ≤ mu) := by
  have hbasic := source_basic hs
  have hanti : StrictAnti t :=
    Fin.strictAnti_iff_succ_lt.mpr hbasic.2.2.2
  have hmu : 0 < mu :=
    (cutoff_pos.trans (source_coordinate_lower hs 0)).trans hbasic.1
  refine ⟨hmu, ?_⟩
  intro i
  have hi : (0 : Fin 8) ≤ i := by omega
  exact ⟨(cutoff_pos.trans (source_coordinate_lower hs i)).le,
    (hanti.antitone hi).trans hbasic.1.le⟩

/-- The entire ORIGINAL denominator is at most 9 mu^10.
In particular this never replaces the real actualParent by comparison:
the expression is explicitly only the original IDEAL residual. -/
private theorem source_denominator_upper {c : Cell} {t : Point}
    (hs : Source c t) :
    (comparison c t - total t) * (newCap c t - total t) *
        product t ≤ 9 * mu ^ 10 := by
  obtain ⟨hmu, hcoords⟩ := source_coordinate_bounded_by_mu hs
  have hprod : product t ≤ mu ^ 8 := by
    have hp : (∏ i : Fin 8, t i) ≤ (∏ _i : Fin 8, mu) :=
      Finset.prod_le_prod (fun i _ => (hcoords i).1)
        (fun i _ => (hcoords i).2)
    simpa [product] using hp
  have hr := source_residual_range hs
  have hP : 0 < comparison c t - total t :=
    (cutoff_pos.trans hr.1).trans hr.2.1
  have hM : 0 < newCap c t - total t := by
    have hpM : comparison c t < newCap c t := hr.2.2.1
    linarith
  have hMup : newCap c t - total t ≤ 3 * mu := by
    have h7 := (hcoords 7).2
    linarith [hr.2.2.2]
  have hPup : comparison c t - total t ≤ 3 * mu := by
    have hpM := hr.2.2.1
    linarith
  have hpair :
      (comparison c t - total t) * (newCap c t - total t) ≤
        (3 * mu) * (3 * mu) :=
    mul_le_mul hPup hMup (by positivity) hP.le
  calc
    (comparison c t - total t) * (newCap c t - total t) * product t
        ≤ ((3 * mu) * (3 * mu)) * mu ^ 8 :=
          mul_le_mul hpair hprod (pow_nonneg hmu.le 8)
            (mul_pos hP hM).le
    _ = 9 * mu ^ 10 := by ring

/-- A *quantitative* denominator comparison on the actual original
source.  It does not assert that the original cap gap has a certified
positive integral, nor that it is an arithmetic signed saving. -/
theorem scaledCapGap_le_kernel {c : Cell} {t : Point}
    (hs : Source c t) : scaledCapGap c t ≤ kernel c t := by
  have hr := source_residual_range hs
  have hP : 0 < comparison c t - total t :=
    (cutoff_pos.trans hr.1).trans hr.2.1
  have hM : 0 < newCap c t - total t := by
    have hpM := hr.2.2.1
    linarith
  have hJ : 0 < product t := (source_product_lower hs).2
  have hden : 0 <
      (comparison c t - total t) *
        (newCap c t - total t) * product t :=
    mul_pos (mul_pos hP hM) hJ
  have hmu : 0 < mu := (source_coordinate_bounded_by_mu hs).1
  have hupper : 0 < 9 * mu ^ 10 := by positivity
  have hnum : 0 ≤ 4 * (newCap c t - comparison c t) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hr.2.2.1.le)
  have h := (div_le_div_iff₀ hupper hden).mpr
    (mul_le_mul_of_nonneg_left (source_denominator_upper hs) hnum)
  calc
    scaledCapGap c t =
        4 * (newCap c t - comparison c t) / (9 * mu ^ 10) := by
          unfold scaledCapGap
          ring
    _ ≤ 4 * (newCap c t - comparison c t) /
          ((comparison c t - total t) * (newCap c t - total t) *
             product t) := h
    _ = kernel c t := rfl

/-- The ORIGINAL finite cap gap is integrable on its actual Source;
this relies on the proved finite source volume and the original
source terminal ceiling, not a newly added integrability assumption. -/
theorem integrableOn_original_cap_gap (c : Cell) :
    IntegrableOn (fun t : Point => newCap c t - comparison c t)
      (sourceSet c) := by
  have hconst : IntegrableOn (fun _ : Point => 3 * mu) (sourceSet c) :=
    integrableOn_const (source_volume_lt_top c).ne
  apply hconst.mono'
    (((newCap_continuous c).sub (comparison_continuous c)).measurable.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
  have hr := source_residual_range ht
  have hnonneg : 0 ≤ newCap c t - comparison c t :=
    sub_nonneg.mpr hr.2.2.1.le
  have hmu : 0 < mu := (source_coordinate_bounded_by_mu ht).1
  have h7 := ((source_coordinate_bounded_by_mu ht).2 7).2
  have hup : newCap c t - comparison c t ≤ 3 * mu := by
    have hP : 0 < comparison c t - total t :=
      (cutoff_pos.trans hr.1).trans hr.2.1
    linarith [hr.2.2.2]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hup

/-- This is a real, measurable-source INTEGRAL inequality, not an
archive endpoint and not a physical signed-continuation comparison. -/
theorem original_source_integral_scaled_gap_le_kernel (c : Cell) :
    (∫ t in sourceSet c, scaledCapGap c t) ≤
      ∫ t in sourceSet c, kernel c t := by
  have hscaled : IntegrableOn (scaledCapGap c) (sourceSet c) := by
    change IntegrableOn
      (fun t : Point => (4 / (9 * mu ^ 10)) *
        (newCap c t - comparison c t)) (sourceSet c)
    exact (integrableOn_original_cap_gap c).const_mul _
  exact setIntegral_mono_on hscaled (integrableOn_kernel c)
    (sourceSet_measurable c) (fun t ht => scaledCapGap_le_kernel ht)

end
end ImbalancedChen.P4AOriginalFull87QuantitativeGapIntegral
