import ImbalancedChen.Part3PositiveCompactTensorLpApproximation
import ImbalancedChen.Part3CuspVerticalHeightCommutator
import ImbalancedChen.Part3ProductConvolutionSecondDerivatives
import ImbalancedChen.Part3CompactRectanglePhysicalRellich

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A NEW quantitative cutoff with one fixed horizontal profile, one fixed
bottom transition, and the EXISTING fixed chi(y/Y). Its actual Euclidean
first partials have a genuine constant chosen BEFORE Y, for all Y>=1.
The old qualitative686/8f6c cutoffs remain unchanged: arbitrary chosen
ContDiffBumpBase families have no asserted uniform radius-ratio bound.
Here every undilated profile is fixed, and chi'/Y is paid explicitly.
No polynomial D(Y), uniform derivative supplier or spectral input is used. -/

namespace ImbalancedChen.Part3.QuantitativeChartCutoffFirstDerivatives20261026b
noncomputable section
open Set Filter
open scoped Topology
open PositiveRectangleSmoothTensorDensity20261025a
open CuspVerticalHeightCommutator20261026b ActualCuspStripCutoff20261025a
open ProductConvolutionSecondDerivatives20261026a CompactRectanglePhysicalRellich20261026a

def quantitativeHorizontal : ℝ → ℝ := horizontalBump (1/2) (by norm_num)
def quantitativeBottom : ℝ → ℝ := lowerHeightTransition (1/2)

theorem quantitativeHorizontal_smooth : ContDiff ℝ ∞ quantitativeHorizontal :=
  (horizontalBump (1/2) (by norm_num)).contDiff

theorem quantitativeBottom_smooth : ContDiff ℝ ∞ quantitativeBottom := lowerHeightTransition_smooth (1/2)

private theorem exists_horizontal_derivative_bound :
    ∃ B : ℝ,0 ≤ B ∧ ∀ x,|deriv quantitativeHorizontal x| ≤ B := by
  have hc := quantitativeHorizontal_smooth.continuous_deriv (by simp)
  have hk : IsCompact (tsupport (deriv quantitativeHorizontal)) :=
    (horizontalBump (1/2) (by norm_num)).hasCompactSupport.deriv
  obtain ⟨b,hb⟩ := hk.bddAbove_image hc.norm.continuousOn
  refine ⟨max b 0,le_max_right _ _,?_⟩
  intro x
  by_cases hx : x ∈ tsupport (deriv quantitativeHorizontal)
  · exact (by simpa only [Real.norm_eq_abs] using hb ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,abs_zero]
    exact le_max_right _ _

private theorem bottom_deriv_zero_below {y : ℝ} (hy : y < 1/4) : deriv quantitativeBottom y=0 := by
  have he : quantitativeBottom =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
    filter_upwards [lt_mem_nhds hy] with t ht
    exact lowerHeightTransition_zero (by norm_num : (0 : ℝ)<1/2) (by linarith)
  simpa only [deriv_const] using he.deriv_eq

private theorem bottom_deriv_zero_above {y : ℝ} (hy : 1/2 < y) : deriv quantitativeBottom y=0 := by
  have he : quantitativeBottom =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
    filter_upwards [gt_mem_nhds hy] with t ht
    exact lowerHeightTransition_one (by norm_num : (0 : ℝ)<1/2) ht.le
  simpa only [deriv_const] using he.deriv_eq

private theorem exists_bottom_derivative_bound :
    ∃ B : ℝ,0 ≤ B ∧ ∀ y,|deriv quantitativeBottom y| ≤ B := by
  have hc := quantitativeBottom_smooth.continuous_deriv (by simp)
  obtain ⟨b,hb⟩ := (isCompact_Icc : IsCompact (Icc (1/4 : ℝ) (1/2))).bddAbove_image hc.norm.continuousOn
  refine ⟨max b 0,le_max_right _ _,?_⟩
  intro y
  by_cases hy : y ∈ Icc (1/4 : ℝ) (1/2)
  · exact (by simpa only [Real.norm_eq_abs] using hb ⟨y,hy,rfl⟩).trans (le_max_left _ _)
  · have hzero : deriv quantitativeBottom y=0 := by
      rcases lt_or_ge y (1/4 : ℝ) with h | h
      · exact bottom_deriv_zero_below h
      · exact bottom_deriv_zero_above (lt_of_not_ge (fun h' => hy ⟨h,h'⟩))
    rw [hzero,abs_zero]
    exact le_max_right _ _

def horizontalFirstDerivativeBound : ℝ := Classical.choose exists_horizontal_derivative_bound
def bottomFirstDerivativeBound : ℝ := Classical.choose exists_bottom_derivative_bound
def quantitativeFirstDerivativeBound : ℝ :=
  horizontalFirstDerivativeBound+bottomFirstDerivativeBound+derivativeBound

theorem horizontalFirstDerivativeBound_nonneg : 0 ≤ horizontalFirstDerivativeBound :=
  (Classical.choose_spec exists_horizontal_derivative_bound).1
theorem bottomFirstDerivativeBound_nonneg : 0 ≤ bottomFirstDerivativeBound :=
  (Classical.choose_spec exists_bottom_derivative_bound).1
theorem quantitativeFirstDerivativeBound_nonneg : 0 ≤ quantitativeFirstDerivativeBound := by
  exact add_nonneg (add_nonneg horizontalFirstDerivativeBound_nonneg bottomFirstDerivativeBound_nonneg)
    derivativeBound_nonneg

theorem quantitativeHorizontal_deriv_bound (x : ℝ) :
    |deriv quantitativeHorizontal x| ≤ horizontalFirstDerivativeBound :=
  (Classical.choose_spec exists_horizontal_derivative_bound).2 x

theorem quantitativeBottom_deriv_bound (y : ℝ) :
    |deriv quantitativeBottom y| ≤ bottomFirstDerivativeBound :=
  (Classical.choose_spec exists_bottom_derivative_bound).2 y

theorem quantitativeVertical_deriv_bound {Y : ℝ} (hY : 1 ≤ Y) (y : ℝ) :
    |deriv (verticalHeightCutoff (1/2) Y) y| ≤ bottomFirstDerivativeBound+derivativeBound := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hlow : |quantitativeBottom y| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hhigh : |heightCutoff Y y| ≤ 1 := by
    rw [abs_of_nonneg (chi_nonneg _)]
    exact chi_le_one _
  have hhighD : |deriv (heightCutoff Y) y| ≤ derivativeBound := by
    rw [deriv_heightCutoff,abs_div,abs_of_pos hYp]
    exact (div_le_div_of_nonneg_right (deriv_chi_bound _) hYp.le).trans
      ((div_le_self derivativeBound_nonneg hY))
  have hd := (((quantitativeBottom_smooth.differentiable (by simp) y).hasDerivAt).mul
    (((heightCutoff_cinfty Y).differentiable (by simp) y).hasDerivAt)).deriv
  change |deriv (fun t => quantitativeBottom t*heightCutoff Y t) y| ≤ _
  rw [hd]
  calc
    _ ≤ |deriv quantitativeBottom y*heightCutoff Y y|+|quantitativeBottom y*deriv (heightCutoff Y) y| := abs_add_le _ _
    _ = |deriv quantitativeBottom y|*|heightCutoff Y y|+|quantitativeBottom y|*|deriv (heightCutoff Y) y| := by rw [abs_mul,abs_mul]
    _ ≤ bottomFirstDerivativeBound*1+1*derivativeBound :=
      add_le_add (mul_le_mul (quantitativeBottom_deriv_bound y) hhigh (abs_nonneg _) bottomFirstDerivativeBound_nonneg)
        (mul_le_mul hlow hhighD (abs_nonneg _) zero_le_one)
    _ = _ := by ring

def quantitativePlanarCutoff (Y : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((quantitativeHorizontal p.1*verticalHeightCutoff (1/2) Y p.2 : ℝ) : ℂ)

def quantitativeUpperCutoff (Y : ℝ) (z : UpperHalfPlane) : ℂ :=
  quantitativePlanarCutoff Y (z.re,z.im)

theorem quantitativePlanarCutoff_smooth (Y : ℝ) : ContDiff ℝ ∞ (quantitativePlanarCutoff Y) :=
  Complex.ofRealCLM.contDiff.comp ((quantitativeHorizontal_smooth.comp contDiff_fst).mul
    ((verticalHeightCutoff_smooth (1/2) Y).comp contDiff_snd))

theorem quantitativePlanarCutoff_norm_le_one (Y : ℝ) (p : ℝ × ℝ) :
    ‖quantitativePlanarCutoff Y p‖ ≤ 1 := by
  have hh0 := (horizontalBump (1/2) (by norm_num)).nonneg (x := p.1)
  have hh1 := (horizontalBump (1/2) (by norm_num)).le_one (x := p.1)
  have hv := verticalHeightCutoff_range (1/2) Y p.2
  rw [quantitativePlanarCutoff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hh0 hv.1)]
  exact (mul_le_mul hh1 hv.2 hv.1 zero_le_one).trans_eq (one_mul _)

theorem quantitativePlanarCutoff_partial_x (Y : ℝ) (p : ℝ × ℝ) :
    partial (quantitativePlanarCutoff Y) 0 p =
      ((deriv quantitativeHorizontal p.1*verticalHeightCutoff (1/2) Y p.2 : ℝ) : ℂ) := by
  have hd := ((quantitativeHorizontal_smooth.differentiable (by simp) p.1).hasDerivAt.mul_const
    (verticalHeightCutoff (1/2) Y p.2)).ofReal_comp
  calc
    _ = directional xDirection (quantitativePlanarCutoff Y) p := rfl
    _ = deriv (fun t => quantitativePlanarCutoff Y (t,p.2)) p.1 := directional_x_eq_slice (quantitativePlanarCutoff_smooth Y) p
    _ = _ := hd.deriv

theorem quantitativePlanarCutoff_partial_y (Y : ℝ) (p : ℝ × ℝ) :
    partial (quantitativePlanarCutoff Y) 1 p =
      ((quantitativeHorizontal p.1*deriv (verticalHeightCutoff (1/2) Y) p.2 : ℝ) : ℂ) := by
  have hd := (((verticalHeightCutoff_smooth (1/2) Y).differentiable (by simp) p.2).hasDerivAt.const_mul
    (quantitativeHorizontal p.1)).ofReal_comp
  calc
    _ = directional yDirection (quantitativePlanarCutoff Y) p := by simp [partial,direction,directional,yDirection]
    _ = deriv (fun t => quantitativePlanarCutoff Y (p.1,t)) p.2 := directional_y_eq_slice (quantitativePlanarCutoff_smooth Y) p
    _ = _ := hd.deriv

/-- A genuine UNIFORM-IN-Y Euclidean partial bound chosen before every
height, mode cutoff and input vector. -/
theorem quantitativePlanarCutoff_partial_bound {Y : ℝ} (hY : 1 ≤ Y)
    (j : Fin 2) (p : ℝ × ℝ) : ‖partial (quantitativePlanarCutoff Y) j p‖ ≤ quantitativeFirstDerivativeBound := by
  fin_cases j
  · rw [quantitativePlanarCutoff_partial_x,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    have hv := verticalHeightCutoff_range (1/2) Y p.2
    have hb : |verticalHeightCutoff (1/2) Y p.2| ≤ 1 := by
      rw [abs_of_nonneg hv.1]
      exact hv.2
    have h := mul_le_mul (quantitativeHorizontal_deriv_bound p.1) hb (abs_nonneg _) horizontalFirstDerivativeBound_nonneg
    have hle : horizontalFirstDerivativeBound ≤ quantitativeFirstDerivativeBound := by
      dsimp [quantitativeFirstDerivativeBound]
      linarith [bottomFirstDerivativeBound_nonneg,derivativeBound_nonneg]
    exact (by simpa only [mul_one] using h).trans hle
  · rw [quantitativePlanarCutoff_partial_y,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    have hh : |quantitativeHorizontal p.1| ≤ 1 := by
      rw [abs_of_nonneg ((horizontalBump (1/2) (by norm_num)).nonneg)]
      exact (horizontalBump (1/2) (by norm_num)).le_one
    have h := mul_le_mul hh (quantitativeVertical_deriv_bound hY p.2) (abs_nonneg _) zero_le_one
    have hle : bottomFirstDerivativeBound+derivativeBound ≤ quantitativeFirstDerivativeBound := by
      dsimp [quantitativeFirstDerivativeBound]
      linarith [horizontalFirstDerivativeBound_nonneg]
    exact (by simpa only [one_mul] using h).trans hle

end
end ImbalancedChen.Part3.QuantitativeChartCutoffFirstDerivatives20261026b
