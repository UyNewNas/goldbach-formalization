import ImbalancedChen.P5U7OriginalRationalCoverCertificate

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual generated outer-minus-inner staircase is paid by two explicit
slanted strips: the original order diagonal and the original square-root
wall. Product-measure integration proves the strip areas; disjoint open
cell ownership gives the corresponding finite rational sum of full cell
areas. No boundary-volume or cardinality supplier is assumed.
-/

namespace ImbalancedChen.P5U7OriginalGridBoundaryArea

noncomputable section

open Set MeasureTheory Filter Topology
open scoped BigOperators
open Classical
open P5U7OriginalStraddlingCells P5U7OriginalStaircaseGeometry
open P5U7OriginalRationalCoverCertificate

def tStep (m : ℕ) : ℚ := (thi - tlo) / m
def uStep (m : ℕ) : ℚ := (uhi - ulo) / m
def diagonalWidth (m : ℕ) : ℚ := tStep m + uStep m
def capWidth (m : ℕ) : ℚ := tStep m + 2 * uStep m
def boundaryIndices (m : ℕ) : Finset (Index m) := outer m \ inner m
def boundary (m : ℕ) : Set (ℝ × ℝ) :=
  ⋃ i ∈ boundaryIndices m, (cell m i).opened
def rationalBoundaryArea (m : ℕ) : ℚ :=
  ∑ i ∈ boundaryIndices m, (cell m i).area
def areaRate (m : ℕ) : ℚ :=
  (thi - tlo) * (3 * tStep m + 4 * uStep m)

theorem step_nonneg (m : ℕ) : 0 ≤ tStep m ∧ 0 ≤ uStep m := by
  constructor
  · exact div_nonneg (by norm_num [thi, tlo]) (Nat.cast_nonneg m)
  · exact div_nonneg (by norm_num [uhi, ulo]) (Nat.cast_nonneg m)

theorem cell_widths (m : ℕ) (i : Index m) :
    (cell m i).b - (cell m i).a = tStep m ∧
      (cell m i).d - (cell m i).c = uStep m := by
  unfold cell mesh tStep uStep
  simp only [Nat.cast_add, Nat.cast_one]
  constructor <;> ring

def strip (center : ℝ → ℝ) (delta : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (tlo : ℝ) thi ∧
    p.2 ∈ Icc (center p.1 - delta) (center p.1 + delta)}

theorem strip_measurable (center : ℝ → ℝ) (hc : Continuous center) (delta : ℝ) :
    MeasurableSet (strip center delta) := by
  exact ((measurableSet_le measurable_const continuous_fst.measurable).inter
    (measurableSet_le continuous_fst.measurable measurable_const)).inter
    ((measurableSet_le ((hc.comp continuous_fst).sub continuous_const).measurable
      continuous_snd.measurable).inter
      (measurableSet_le continuous_snd.measurable
        ((hc.comp continuous_fst).add continuous_const).measurable))

theorem strip_volume (center : ℝ → ℝ) (hc : Continuous center) (delta : ℝ) :
    volume (strip center delta) =
      ENNReal.ofReal (2 * delta) * ENNReal.ofReal ((thi : ℝ) - tlo) := by
  have hfiber (x : ℝ) : volume (Prod.mk x ⁻¹' strip center delta) =
      (Icc (tlo : ℝ) thi).indicator (fun _ => ENNReal.ofReal (2 * delta)) x := by
    by_cases hx : x ∈ Icc (tlo : ℝ) thi
    · have heq : Prod.mk x ⁻¹' strip center delta =
          Icc (center x - delta) (center x + delta) := by
        ext y
        simp only [strip, mem_preimage, mem_setOf_eq, hx, true_and]
      rw [heq, indicator_of_mem hx, Real.volume_Icc]
      congr 1
      ring
    · have heq : Prod.mk x ⁻¹' strip center delta = ∅ := by
        ext y
        simp only [strip, mem_preimage, mem_setOf_eq, hx, false_and, mem_empty_iff_false]
      rw [heq, measure_empty, indicator_of_notMem hx]
  rw [Measure.volume_eq_prod, Measure.prod_apply (strip_measurable center hc delta)]
  simp_rw [hfiber]
  rw [lintegral_indicator measurableSet_Icc, lintegral_const]
  simp only [Measure.restrict_apply measurableSet_univ, univ_inter, Real.volume_Icc]

theorem boundary_subset_strips (m : ℕ) (hm : 0 < m) :
    boundary m ⊆ strip (fun x => x) (diagonalWidth m : ℝ) ∪
      strip (fun x => (1 - x) / 2) ((capWidth m : ℝ) / 2) := by
  intro p hp
  obtain ⟨i, hp⟩ := mem_iUnion.mp hp
  obtain ⟨hi, hpi⟩ := mem_iUnion.mp hp
  obtain ⟨hiO, hiN⟩ := Finset.mem_sdiff.mp hi
  have houter := (Finset.mem_filter.mp hiO).2
  have hnot : ¬ ((cell m i).b ≤ (cell m i).c ∧
      (cell m i).b + 2 * (cell m i).d ≤ 1) := by
    intro hh
    exact hiN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
  have hpC := opened_subset_closed (cell m i) hpi
  have hT := (mesh_bounds tlo thi (by norm_num [tlo, thi]) m hm i.1 i.1.isLt.le).1
  have hT' := (mesh_bounds tlo thi (by norm_num [tlo, thi]) m hm
    (i.1.val + 1) (by omega)).2
  have hbase : p.1 ∈ Icc (tlo : ℝ) thi := by
    have hl : (tlo : ℝ) ≤ (cell m i).a := by exact_mod_cast hT
    have hr : ((cell m i).b : ℝ) ≤ thi := by exact_mod_cast hT'
    exact ⟨hl.trans hpC.1.1, hpC.1.2.trans hr⟩
  have hdt : ((cell m i).b : ℝ) - (cell m i).a = (tStep m : ℝ) := by
    exact_mod_cast (cell_widths m i).1
  have hdu : ((cell m i).d : ℝ) - (cell m i).c = (uStep m : ℝ) := by
    exact_mod_cast (cell_widths m i).2
  rcases not_and_or.mp hnot with hdiag | hcap
  · have hdiagR : ((cell m i).c : ℝ) ≤ (cell m i).b := by
      exact_mod_cast (lt_of_not_ge hdiag).le
    have houterR : ((cell m i).a : ℝ) ≤ (cell m i).d := by exact_mod_cast houter.1
    apply Or.inl
    refine ⟨hbase, ?_⟩
    simp only [diagonalWidth, Rat.cast_add]
    constructor <;> linarith only [hdt, hdu, hdiagR, houterR,
      hpC.1.1, hpC.1.2, hpC.2.1, hpC.2.2]
  · have hcapR : (1 : ℝ) ≤ (cell m i).b + 2 * (cell m i).d := by
      exact_mod_cast (lt_of_not_ge hcap).le
    have houterR : ((cell m i).a : ℝ) + 2 * (cell m i).c ≤ 1 := by
      exact_mod_cast houter.2
    apply Or.inr
    refine ⟨hbase, ?_⟩
    simp only [capWidth, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    constructor <;> linarith only [hdt, hdu, hcapR, houterR,
      hpC.1.1, hpC.1.2, hpC.2.1, hpC.2.2]

/-- Quantitative genuine product-area payment of the complete generated
boundary staircase, with its original order and square-root walls. -/
theorem boundary_volume_real_le (m : ℕ) (hm : 0 < m) :
    (volume (boundary m)).toReal ≤ (areaRate m : ℝ) := by
  have hmeasure := (measure_mono (boundary_subset_strips m hm)).trans
    (measure_union_le
      (strip (fun x => x) (diagonalWidth m : ℝ))
      (strip (fun x => (1 - x) / 2) ((capWidth m : ℝ) / 2)))
  rw [strip_volume _ continuous_id,
    strip_volume _ (by fun_prop : Continuous (fun x : ℝ => (1 - x) / 2))] at hmeasure
  have hfinD : ENNReal.ofReal (2 * (diagonalWidth m : ℝ)) *
      ENNReal.ofReal ((thi : ℝ) - tlo) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hfinC : ENNReal.ofReal (2 * ((capWidth m : ℝ) / 2)) *
      ENNReal.ofReal ((thi : ℝ) - tlo) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hfinite :
      ENNReal.ofReal (2 * (diagonalWidth m : ℝ)) * ENNReal.ofReal ((thi : ℝ) - tlo) +
      ENNReal.ofReal (2 * ((capWidth m : ℝ) / 2)) * ENNReal.ofReal ((thi : ℝ) - tlo) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨hfinD, hfinC⟩
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  have hdt : (0 : ℝ) ≤ (tStep m : ℝ) := by exact_mod_cast (step_nonneg m).1
  have hdu : (0 : ℝ) ≤ (uStep m : ℝ) := by exact_mod_cast (step_nonneg m).2
  have hd : (0 : ℝ) ≤ (diagonalWidth m : ℝ) := by
    simp only [diagonalWidth, Rat.cast_add]
    linarith
  have hc : (0 : ℝ) ≤ (capWidth m : ℝ) := by
    simp only [capWidth, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    linarith
  have hwidth : (0 : ℝ) ≤ (thi : ℝ) - tlo := by norm_num [thi, tlo]
  have hadd := ENNReal.toReal_add hfinD hfinC
  rw [hadd] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
      0 ≤ 2 * (diagonalWidth m : ℝ)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((capWidth m : ℝ) / 2)),
    ENNReal.toReal_ofReal hwidth] at hreal
  unfold areaRate
  push_cast
  simp only [diagonalWidth, capWidth, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] at hreal
  nlinarith only [hreal]

theorem boundary_area_sum_eq_volume (m : ℕ) (hm : 0 < m) :
    (rationalBoundaryArea m : ℝ) = (volume (boundary m)).toReal := by
  have hsum : (∫ p : ℝ × ℝ in boundary m, (1 : ℝ)) =
      ∑ i ∈ boundaryIndices m, ∫ p : ℝ × ℝ in (cell m i).opened, (1 : ℝ) := by
    apply integral_biUnion_finset (boundaryIndices m) (fun i _ => opened_measurable _)
    · intro i _ j _ hij
      exact opened_cells_disjoint m hm hij
    · intro i _
      have hc : IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ)) (cell m i).closed :=
        continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      exact hc.mono_set (opened_subset_closed _)
  have hcell (i : Index m) : (∫ p : ℝ × ℝ in (cell m i).opened, (1 : ℝ)) =
      ((cell m i).area : ℝ) := by
    rw [integral_const]
    simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter,
      smul_eq_mul, opened_volume_real (cell_valid m hm i), mul_one]
  simp_rw [hcell] at hsum
  simp only [integral_const, Measure.real, Measure.restrict_apply measurableSet_univ,
    univ_inter, smul_eq_mul, mul_one] at hsum
  unfold rationalBoundaryArea
  push_cast
  exact hsum.symm

/-- Finite rational total area of every actual boundary cell is O(1/m),
proved through geometric strip payment rather than a supplied cell count. -/
theorem rationalBoundaryArea_le_rate (m : ℕ) (hm : 0 < m) :
    rationalBoundaryArea m ≤ areaRate m := by
  have h := (boundary_area_sum_eq_volume m hm).trans_le (boundary_volume_real_le m hm)
  exact_mod_cast h

theorem areaRate_eq_constant_div (m : ℕ) :
    areaRate m = ((thi - tlo) * (3 * (thi - tlo) + 4 * (uhi - ulo))) / m := by
  unfold areaRate tStep uStep
  ring

end

end ImbalancedChen.P5U7OriginalGridBoundaryArea
