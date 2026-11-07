import ImbalancedChen.Certificates.PairedV2FullMaskGeometry
import ImbalancedChen.AffinePrimeGates
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FinCases

/-!
SOURCE ONLY; not compiled or installed.

This supplies actual integrability and finite additivity for the genuine
product-volume integral on the adopted 17572-cell union. Integrability is
proved from the literal reciprocal kernel on a compact positive box.
No integral equality, numerical endpoint, or integrability is assumed.

All seven endpoint/ordering walls are also proved null using their actual
nonzero linear forms. The remaining unsupplied bridge is the coordinate
Fubini theorem equating one product-volume support integral with its
`pairedLocalIntegral`. The finite union theorem is unconditional.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2AdoptedUnion

open MeasureTheory Set
open scoped BigOperators

noncomputable section

abbrev Point := Fin 4 → ℝ

/-- Literal reciprocal density with the manuscript's squared z-coordinate. -/
def rawKernel (x : Point) : ℝ := pairedFibreKernel (x 0) (x 1) (x 2) (x 3)

/-- A compact box containing every adopted fibre, bounded away from zero. -/
def box : Set Point := Icc (fun _ => (a : ℝ)) (fun _ => (d : ℝ))

theorem a_pos : (0 : ℝ) < (a : ℝ) := by
  norm_num [a]

theorem support_subset_box (r : Row) : support r ⊆ box := by
  intro x hx
  obtain ⟨haw, hwz, hzu, huh, hht, htd, _⟩ := row_fibre_argument r hx
  have hah : (a : ℝ) < (h : ℝ) := by norm_num [a, h]
  have hhd : (h : ℝ) < (d : ℝ) := by norm_num [h, d]
  change (fun _ => (a : ℝ)) ≤ x ∧ x ≤ (fun _ => (d : ℝ))
  constructor <;> intro i <;> fin_cases i <;> dsimp <;> linarith

theorem region_subset_box : region ⊆ box := by
  intro x hx
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  exact support_subset_box r hr

theorem support_isOpen (r : Row) : IsOpen (support r) := by
  dsimp only [support, openFibreSet, openFibreSupport]
  exact (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt (continuous_apply 1) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_apply 3)).inter
    ((isOpen_lt (continuous_apply 3) (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))))))

theorem support_measurable (r : Row) : MeasurableSet (support r) := by
  exact (support_isOpen r).measurableSet

theorem region_isOpen : IsOpen region := by
  exact isOpen_iUnion support_isOpen

theorem region_measurable : MeasurableSet region := by
  exact region_isOpen.measurableSet

theorem coordinates_pos {x : Point} (hx : x ∈ box) (i : Fin 4) : 0 < x i := by
  exact a_pos.trans_le (hx.1 i)

/-- The reciprocal singularities are absent on the entire compact box. -/
theorem continuousOn_rawKernel : ContinuousOn rawKernel box := by
  have hc (i : Fin 4) : ContinuousOn (fun x : Point => x i) box :=
    (continuous_apply i).continuousOn
  have hn (i : Fin 4) (x : Point) (hx : x ∈ box) : x i ≠ 0 :=
    (coordinates_pos hx i).ne'
  exact (continuousOn_const.div (hc 0) (hn 0)).mul
    ((continuousOn_const.div (hc 1) (hn 1)).mul
      ((continuousOn_const.div ((hc 2).pow 2)
        (fun x hx => pow_ne_zero 2 (hn 2 x hx))).mul
        (continuousOn_const.div (hc 3) (hn 3))))

theorem rawKernel_nonneg {x : Point} (hx : x ∈ box) : 0 ≤ rawKernel x := by
  have h0 := coordinates_pos hx 0
  have h1 := coordinates_pos hx 1
  have h2 := coordinates_pos hx 2
  have h3 := coordinates_pos hx 3
  unfold rawKernel pairedFibreKernel
  positivity

/-- An explicit uniform majorant, independent of the certificate table. -/
theorem rawKernel_le {x : Point} (hx : x ∈ box) :
    rawKernel x ≤ 1 / (a : ℝ) ^ 5 := by
  have h0 := coordinates_pos hx 0
  have h1 := coordinates_pos hx 1
  have h2 := coordinates_pos hx 2
  have h3 := coordinates_pos hx 3
  have h01 : (a : ℝ) * a ≤ x 0 * x 1 :=
    mul_le_mul (hx.1 0) (hx.1 1) a_pos.le h0.le
  have h2sq : (a : ℝ) ^ 2 ≤ x 2 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hx.1 2))
      (add_nonneg h2.le a_pos.le)]
  have h012 : (a : ℝ) * a * a ^ 2 ≤ x 0 * x 1 * x 2 ^ 2 :=
    mul_le_mul h01 h2sq (sq_nonneg (a : ℝ)) (mul_nonneg h0.le h1.le)
  have h0123 : (a : ℝ) * a * a ^ 2 * a ≤ x 0 * x 1 * x 2 ^ 2 * x 3 :=
    mul_le_mul h012 (hx.1 3) a_pos.le
      (mul_nonneg (mul_nonneg h0.le h1.le) (sq_nonneg (x 2)))
  have hden : (a : ℝ) ^ 5 ≤ x 0 * x 1 * x 2 ^ 2 * x 3 := by
    calc
      (a : ℝ) ^ 5 = (a : ℝ) * a * a ^ 2 * a := by ring
      _ ≤ x 0 * x 1 * x 2 ^ 2 * x 3 := h0123
  rw [rawKernel, pairedFibreKernel_eq]
  exact one_div_le_one_div_of_le (pow_pos a_pos 5) hden

theorem rawKernel_norm_le {x : Point} (hx : x ∈ box) :
    ‖rawKernel x‖ ≤ 1 / (a : ℝ) ^ 5 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (rawKernel_nonneg hx)]
  exact rawKernel_le hx

/-- Integrability uses genuine product-volume Lebesgue measure. -/
theorem integrableOn_box : IntegrableOn rawKernel box (volume : Measure Point) := by
  exact continuousOn_rawKernel.integrableOn_compact isCompact_Icc

theorem integrableOn_support (r : Row) :
    IntegrableOn rawKernel (support r) (volume : Measure Point) := by
  exact integrableOn_box.mono_set (support_subset_box r)

theorem integrableOn_region :
    IntegrableOn rawKernel region (volume : Measure Point) := by
  exact integrableOn_box.mono_set region_subset_box

/-- The full genuine union integral is exactly the sum of its disjoint
product-volume support integrals; all hypotheses are proved above. -/
theorem region_setIntegral_eq_sum :
    (∫ x : Point in region, rawKernel x) =
      ∑ r : Row, ∫ x : Point in support r, rawKernel x := by
  exact integral_iUnion_fintype support_measurable
    supports_pairwise_disjoint integrableOn_support

/-- Actual finite-union integration also applies to any selected row set. -/
theorem partial_setIntegral_eq_sum (s : Finset Row) :
    (∫ x : Point in ⋃ r ∈ s, support r, rawKernel x) =
      ∑ r ∈ s, ∫ x : Point in support r, rawKernel x := by
  apply integral_biUnion_finset s (fun r _ => support_measurable r)
  · intro r _ q _ hrq
    exact supports_pairwise_disjoint hrq
  · intro r _
    exact integrableOn_support r

/-- The coefficient is K/80 exactly once, outside the genuine union integral. -/
def unionIntegral : ℝ := ((K : ℝ) / 80) * ∫ x : Point in region, rawKernel x

theorem unionIntegral_eq_sum : unionIntegral =
    ∑ r : Row, ((K : ℝ) / 80) * ∫ x : Point in support r, rawKernel x := by
  rw [unionIntegral, region_setIntegral_eq_sum, Finset.mul_sum]

/-- The corresponding closed cell, including its six endpoint walls and
the triangular ordering wall w=z. -/
def closedSupport (r : Row) : Set Point := {x |
  (tLower (indices r).1 : ℝ) ≤ x 0 ∧
  x 0 ≤ (tUpper (indices r).1 : ℝ) ∧
  (uLower (indices r).2 : ℝ) ≤ x 1 ∧
  x 1 ≤ (uUpper (indices r).2 : ℝ) ∧
  (a : ℝ) ≤ x 3 ∧ x 3 ≤ x 2 ∧ x 2 ≤ (cutoff r : ℝ)}

theorem ae_coordinate_ne (i : Fin 4) (c : ℝ) :
    ∀ᵐ x : Point ∂volume, x i ≠ c := by
  have hproj : (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) ≠ 0 := by
    intro hz
    have hh := congrArg (fun L : Point →L[ℝ] ℝ => L (fun _ => 1)) hz
    norm_num at hh
  rw [ae_iff]
  simpa only [not_not] using
    ImbalancedChen.affinePrimeWall_volume_zero
      (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) hproj c

def orderingWallForm : Point →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 3 - ContinuousLinearMap.proj 2

theorem orderingWallForm_ne_zero : orderingWallForm ≠ 0 := by
  intro hz
  have hh := congrArg (fun L : Point →L[ℝ] ℝ => L ![0, 0, 0, 1]) hz
  norm_num [orderingWallForm, Matrix.cons_val_two] at hh

theorem ae_ordering_ne : ∀ᵐ x : Point ∂volume, x 3 ≠ x 2 := by
  rw [ae_iff]
  simpa only [not_not, orderingWallForm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.proj_apply, sub_eq_zero] using
    ImbalancedChen.affinePrimeWall_volume_zero orderingWallForm
      orderingWallForm_ne_zero 0

/-- Closed and open cells agree almost everywhere for genuine product
volume; none of the seven boundary nullness facts is assumed. -/
theorem closedSupport_ae_eq_support (r : Row) :
    closedSupport r =ᵐ[volume] support r := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [ae_coordinate_ne 0 (tLower (indices r).1),
    ae_coordinate_ne 0 (tUpper (indices r).1),
    ae_coordinate_ne 1 (uLower (indices r).2),
    ae_coordinate_ne 1 (uUpper (indices r).2),
    ae_coordinate_ne 3 a, ae_ordering_ne, ae_coordinate_ne 2 (cutoff r)] with
      x htl htr hul hur haw hwz hZ
  change
    ((tLower (indices r).1 : ℝ) ≤ x 0 ∧
      x 0 ≤ (tUpper (indices r).1 : ℝ) ∧
      (uLower (indices r).2 : ℝ) ≤ x 1 ∧
      x 1 ≤ (uUpper (indices r).2 : ℝ) ∧
      (a : ℝ) ≤ x 3 ∧ x 3 ≤ x 2 ∧ x 2 ≤ (cutoff r : ℝ)) ↔
    ((tLower (indices r).1 : ℝ) < x 0 ∧
      x 0 < (tUpper (indices r).1 : ℝ) ∧
      (uLower (indices r).2 : ℝ) < x 1 ∧
      x 1 < (uUpper (indices r).2 : ℝ) ∧
      (a : ℝ) < x 3 ∧ x 3 < x 2 ∧ x 2 < (cutoff r : ℝ))
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨lt_of_le_of_ne h0 htl.symm, lt_of_le_of_ne h1 htr,
      lt_of_le_of_ne h2 hul.symm, lt_of_le_of_ne h3 hur,
      lt_of_le_of_ne h4 haw.symm, lt_of_le_of_ne h5 hwz,
      lt_of_le_of_ne h6 hZ⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨h0.le, h1.le, h2.le, h3.le, h4.le, h5.le, h6.le⟩

theorem closedSupport_setIntegral (r : Row) :
    (∫ x : Point in closedSupport r, rawKernel x) =
      ∫ x : Point in support r, rawKernel x := by
  exact setIntegral_congr_set (closedSupport_ae_eq_support r)

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2AdoptedUnion
