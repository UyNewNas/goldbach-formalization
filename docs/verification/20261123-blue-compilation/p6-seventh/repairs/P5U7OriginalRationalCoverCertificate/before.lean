import ImbalancedChen.P5U7OriginalStaircaseGeometry

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Automatic rational outer/inner staircases enclose the WHOLE genuine
original J7 integral. Outer rectangles pay their complete areas, including
triangle and Buchstab-seam straddles. Inner open rectangles have proved
disjoint ownership and lie in the original triangle. The finite certificate
contains only rational arithmetic and rational Taylor coefficients. Its
truth at the saved original endpoints is not asserted or evaluated.
-/

namespace ImbalancedChen.P5U7OriginalRationalCoverCertificate

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Classical
open P5U7OriginalStraddlingCells P5U7OriginalStaircaseGeometry

def kernel (p : ℝ × ℝ) : ℝ := p5U7OmegaKernel 1 p.1 p.2

theorem triangle_measurable : MeasurableSet p5U7OmegaTriangle := by
  exact ((isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_snd).inter
      (isClosed_le continuous_snd
        ((continuous_const.sub continuous_fst).div_const 2)))).measurableSet

theorem triangle_indicator_integrable : Integrable (p5U7OmegaTriangle.indicator kernel) :=
  (p5U7Omega_triangle_integrable 1).integrable_indicator triangle_measurable

theorem triangle_indicator_nonneg (p : ℝ × ℝ) :
    0 ≤ p5U7OmegaTriangle.indicator kernel p := by
  by_cases hp : p ∈ p5U7OmegaTriangle
  · rw [indicator_of_mem hp]
    exact p5U7Omega_kernel_nonneg (by norm_num) hp
  · simp only [indicator_of_notMem hp, le_refl]

theorem closed_measurable (B : Box) : MeasurableSet B.closed :=
  measurableSet_Icc.prod measurableSet_Icc

theorem opened_measurable (B : Box) : MeasurableSet B.opened :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem closed_volume_real {B : Box} (hB : B.Valid) :
    (volume B.closed).toReal = (B.area : ℝ) := by
  obtain ⟨ha, hab, hb, hc, hcd⟩ := Box.real_guards hB
  rw [Box.closed, Measure.volume_eq_prod, Measure.prod_prod]
  simp only [ENNReal.toReal_mul, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hcd), Box.area,
    Rat.cast_mul, Rat.cast_sub]

theorem opened_volume_real {B : Box} (hB : B.Valid) :
    (volume B.opened).toReal = (B.area : ℝ) := by
  obtain ⟨ha, hab, hb, hc, hcd⟩ := Box.real_guards hB
  rw [Box.opened, Measure.volume_eq_prod, Measure.prod_prod]
  simp only [ENNReal.toReal_mul, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hcd), Box.area,
    Rat.cast_mul, Rat.cast_sub]

def majorant (B : Box) (n : ℕ) : (ℝ × ℝ) → ℝ :=
  B.closed.indicator (fun _ => (B.upper n : ℝ))

def minorant (B : Box) (n : ℕ) : (ℝ × ℝ) → ℝ :=
  B.opened.indicator (fun _ => (B.lower n : ℝ))

theorem majorant_nonneg {B : Box} (hB : B.Valid) (n : ℕ) (p : ℝ × ℝ) :
    0 ≤ majorant B n p := by
  by_cases hp : p ∈ B.closed
  · rw [majorant, indicator_of_mem hp]
    exact_mod_cast Box.upper_nonneg hB n
  · simp only [majorant, indicator_of_notMem hp, le_refl]

theorem majorant_integrable (B : Box) (n : ℕ) : Integrable (majorant B n) := by
  have hc : IntegrableOn (fun _ : ℝ × ℝ => (B.upper n : ℝ)) B.closed :=
    continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact hc.integrable_indicator (closed_measurable B)

theorem minorant_integrable (B : Box) (n : ℕ) : Integrable (minorant B n) := by
  have hc : IntegrableOn (fun _ : ℝ × ℝ => (B.lower n : ℝ)) B.closed :=
    continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact (hc.mono_set (opened_subset_closed B)).integrable_indicator (opened_measurable B)

theorem integral_majorant {B : Box} (hB : B.Valid) (n : ℕ) :
    (∫ p, majorant B n p) = (((B.upper n) * B.area : ℚ) : ℝ) := by
  rw [majorant, integral_indicator (closed_measurable B), integral_const]
  simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter,
    smul_eq_mul, closed_volume_real hB, Rat.cast_mul]
  ring

theorem integral_minorant {B : Box} (hB : B.Valid) (n : ℕ) :
    (∫ p, minorant B n p) = (((B.lower n) * B.area : ℚ) : ℝ) := by
  rw [minorant, integral_indicator (opened_measurable B), integral_const]
  simp only [Measure.real, Measure.restrict_apply measurableSet_univ, univ_inter,
    smul_eq_mul, opened_volume_real hB, Rat.cast_mul]
  ring

def rationalUpper (n m : ℕ) : ℚ :=
  ∑ i ∈ outer m, (cell m i).upper n * (cell m i).area

def rationalLower (n m : ℕ) : ℚ :=
  ∑ i ∈ inner m, (cell m i).lower n * (cell m i).area

/-- Genuine full-cover upper certificate, with automatic geometry and
pointwise Buchstab suppliers. There is no hcover or hIntegral premise. -/
theorem actual_integral_le_rationalUpper (n m : ℕ) (hm : 0 < m) :
    p5U7OriginalOmegaIntegral 1 ≤ (rationalUpper n m : ℝ) := by
  have hg : Integrable (fun p => ∑ i ∈ outer m, majorant (cell m i) n p) :=
    integrable_finsetSum (outer m) (fun i _ => majorant_integrable _ n)
  have hpoint (p : ℝ × ℝ) : p5U7OmegaTriangle.indicator kernel p ≤
      ∑ i ∈ outer m, majorant (cell m i) n p := by
    by_cases hp : p ∈ p5U7OmegaTriangle
    · obtain ⟨i, hi, hpi⟩ := original_triangle_outer_cover m hm hp
      rw [indicator_of_mem hp]
      calc
        kernel p ≤ ((cell m i).upper n : ℝ) :=
          (Box.enclosure (cell_valid m hm i) n hpi hp).2
        _ = majorant (cell m i) n p := (indicator_of_mem hpi _).symm
        _ ≤ _ := Finset.single_le_sum
          (fun j _ => majorant_nonneg (cell_valid m hm j) n p) hi
    · rw [indicator_of_notMem hp]
      exact Finset.sum_nonneg (fun i _ => majorant_nonneg (cell_valid m hm i) n p)
  calc
    p5U7OriginalOmegaIntegral 1 = ∫ p, p5U7OmegaTriangle.indicator kernel p := by
      rw [integral_indicator triangle_measurable]
      exact (p5U7Omega_triangle_integral_eq_nested 1).symm
    _ ≤ ∫ p, ∑ i ∈ outer m, majorant (cell m i) n p :=
      integral_mono triangle_indicator_integrable hg hpoint
    _ = ∑ i ∈ outer m, ∫ p, majorant (cell m i) n p :=
      integral_finsetSum (outer m) (fun i _ => majorant_integrable _ n)
    _ = ∑ i ∈ outer m, (((cell m i).upper n * (cell m i).area : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_majorant (cell_valid m hm i) n
    _ = _ := by
      unfold rationalUpper
      push_cast

/-- Genuine full-source lower certificate. Inner open boxes have proved
disjoint ownership, hence no cell value is counted twice. -/
theorem rationalLower_le_actual_integral (n m : ℕ) (hm : 0 < m) :
    (rationalLower n m : ℝ) ≤ p5U7OriginalOmegaIntegral 1 := by
  have hf : Integrable (fun p => ∑ i ∈ inner m, minorant (cell m i) n p) :=
    integrable_finsetSum (inner m) (fun i _ => minorant_integrable _ n)
  have hpoint (p : ℝ × ℝ) : (∑ i ∈ inner m, minorant (cell m i) n p) ≤
      p5U7OmegaTriangle.indicator kernel p := by
    by_cases hex : ∃ i ∈ inner m, p ∈ (cell m i).opened
    · obtain ⟨i, hi, hpi⟩ := hex
      have hpclosed := opened_subset_closed (cell m i) hpi
      have hpT := inner_cell_subset_triangle m hm hi hpclosed
      have heq : (∑ j ∈ inner m, minorant (cell m j) n p) =
          minorant (cell m i) n p := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          have hnot : p ∉ (cell m j).opened := by
            intro hpj
            exact (Set.disjoint_left.mp (opened_cells_disjoint m hm hji)) hpj hpi
          exact indicator_of_notMem hnot _
        · intro hnot
          exact False.elim (hnot hi)
      rw [heq, minorant, indicator_of_mem hpi, indicator_of_mem hpT]
      exact (Box.enclosure (cell_valid m hm i) n hpclosed hpT).1
    · have hz : (∑ i ∈ inner m, minorant (cell m i) n p) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hnot : p ∉ (cell m i).opened := fun hp => hex ⟨i, hi, hp⟩
        exact indicator_of_notMem hnot _
      rw [hz]
      exact triangle_indicator_nonneg p
  calc
    (rationalLower n m : ℝ) =
        ∑ i ∈ inner m, (((cell m i).lower n * (cell m i).area : ℚ) : ℝ) := by
          unfold rationalLower
          push_cast
    _ = ∑ i ∈ inner m, ∫ p, minorant (cell m i) n p := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_minorant (cell_valid m hm i) n).symm
    _ = ∫ p, ∑ i ∈ inner m, minorant (cell m i) n p :=
      (integral_finsetSum (inner m) (fun i _ => minorant_integrable _ n)).symm
    _ ≤ ∫ p, p5U7OmegaTriangle.indicator kernel p :=
      integral_mono hf triangle_indicator_integrable hpoint
    _ = p5U7OriginalOmegaIntegral 1 := by
      rw [integral_indicator triangle_measurable]
      exact p5U7Omega_triangle_integral_eq_nested 1

/-- A finite rational statement only; neither an integral nor a count
occurs in this check. Lower/upper meshes and precisions are independent. -/
def directedCheck (nL mL nU mU : ℕ) (l u : ℚ) : Bool := decide
  (l ≤ rationalLower nL mL ∧ rationalUpper nU mU ≤ u)

theorem directedCheck_sound (nL mL nU mU : ℕ) (l u : ℚ)
    (hmL : 0 < mL) (hmU : 0 < mU)
    (hcheck : directedCheck nL mL nU mU l u = true) :
    (l : ℝ) ≤ p5U7OriginalOmegaIntegral 1 ∧
      p5U7OriginalOmegaIntegral 1 ≤ (u : ℝ) := by
  have hc : l ≤ rationalLower nL mL ∧ rationalUpper nU mU ≤ u :=
    of_decide_eq_true hcheck
  have hL : (l : ℝ) ≤ (rationalLower nL mL : ℝ) := by exact_mod_cast hc.1
  have hU : (rationalUpper nU mU : ℝ) ≤ (u : ℝ) := by exact_mod_cast hc.2
  exact ⟨hL.trans (rationalLower_le_actual_integral nL mL hmL),
    (actual_integral_le_rationalUpper nU mU hmU).trans hU⟩

def originalLower : ℚ :=
  (7183180737282426411788973366247539 / 5192296858534827628530496329220096) /
    (67619 / 10000)
def originalUpper : ℚ :=
  (1672464594622060236183097 / 1208925819614629174706176) / (67619 / 10000)

def independentOriginalCheck (nL mL nU mU : ℕ) : Bool :=
  directedCheck nL mL nU mU originalLower originalUpper

/-- Soundness at the literal two independent original U7 endpoints.
This theorem makes NO assertion that any finite instance passes. -/
theorem independentOriginalCheck_sound (nL mL nU mU : ℕ)
    (hmL : 0 < mL) (hmU : 0 < mU)
    (hcheck : independentOriginalCheck nL mL nU mU = true) :
    (originalLower : ℝ) ≤ p5U7OriginalOmegaIntegral 1 ∧
      p5U7OriginalOmegaIntegral 1 ≤ (originalUpper : ℝ) :=
  directedCheck_sound nL mL nU mU originalLower originalUpper hmL hmU hcheck

end

end ImbalancedChen.P5U7OriginalRationalCoverCertificate
