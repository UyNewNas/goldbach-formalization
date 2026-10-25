import ImbalancedChen.Part3CompletedEisensteinReflection
import ImbalancedChen.Part3ContinuedFourierSpatialContDiffTwo
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

The central completed constant term is computed from the actual dslope
definition: at s=1/2 it is the analytic derivative value, not a totalized
division. Its correction is exactly sqrt(y)*log(y). Explicit spatial
derivatives prove the central Euler/Maass relation and genuine real-pair C2.
No continuity-of-spatial-derivatives-in-s premise is used.
-/

namespace ImbalancedChen.Part3.CompletedEisensteinCentralHeight

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.ContinuedFourierNonconstantMaass
open ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo

def centralScalar : ℂ := completedRiemannZeta₀ 1 + completedRiemannZeta₀ 0 - 2

def centralHeight (y : ℝ) : ℂ := centralScalar * root0 y + root0 y * (Real.log y : ℂ)
def centralFirst (y : ℝ) : ℂ :=
  centralScalar * root1 y + root1 y * (Real.log y : ℂ) + root0 y * (y : ℂ)⁻¹
def centralSecond (y : ℝ) : ℂ :=
  centralScalar * root2 y + root2 y * (Real.log y : ℂ) +
    2 * root1 y * (y : ℂ)⁻¹ - root0 y * ((y : ℂ) ^ 2)⁻¹

theorem complex_half_power_eq_root0 (y : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (1 / 2 : ℂ) = root0 y := by
  simpa only [root0, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    (Complex.ofReal_cpow hy.le (1 / 2 : ℝ)).symm

/-- The actual central analytic-limit correction, computed by dslope_same. -/
theorem reflectionHeightQuotient_half (y : ℝ) (hy : 0 < y) :
    reflectionHeightQuotient y (1 / 2 : ℂ) = root0 y * (Real.log y : ℂ) := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have ha := (hasDerivAt_id (1 / 2 : ℂ)).const_cpow (c := (y : ℂ)) (Or.inl hyC)
  have hb := ((hasDerivAt_id (1 / 2 : ℂ)).const_sub 1).const_cpow
    (c := (y : ℂ)) (Or.inl hyC)
  have hd : deriv (heightDifference y) (1 / 2 : ℂ) =
      2 * root0 y * (Real.log y : ℂ) := by
    convert (ha.sub hb).deriv using 1 <;>
      simp [heightDifference, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num,
        complex_half_power_eq_root0 y hy, ← Complex.ofReal_log hy.le] <;> ring
  rw [reflectionHeightQuotient, dslope_same, hd]
  ring

/-- The removable central value includes the logarithmic height term. -/
theorem completedConstant_half (y : ℝ) (hy : 0 < y) :
    completedConstant y (1 / 2 : ℂ) = centralHeight y := by
  unfold completedConstant
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, reflectionHeightQuotient_half y hy]
  simp only [complex_half_power_eq_root0 y hy]
  norm_num
  unfold centralHeight centralScalar
  ring

private theorem log_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) (y : ℂ)⁻¹ y := by
  simpa only [Complex.ofReal_inv] using (Real.hasDerivAt_log hy.ne').ofReal_comp

private theorem inv_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => (t : ℂ)⁻¹) (-((y : ℂ) ^ 2)⁻¹) y := by
  simpa [pow_two, div_eq_mul_inv] using ((hasDerivAt_id y).inv hy.ne').ofReal_comp

theorem centralHeight_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt centralHeight (centralFirst y) y := by
  have h := ((root0_hasDerivAt hy).const_mul centralScalar).add
    ((root0_hasDerivAt hy).mul (log_hasDerivAt hy))
  convert h using 1 <;> simp [centralHeight, centralFirst] <;> ring

theorem centralFirst_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt centralFirst (centralSecond y) y := by
  have h := (((root1_hasDerivAt hy).const_mul centralScalar).add
    ((root1_hasDerivAt hy).mul (log_hasDerivAt hy))).add
      ((root0_hasDerivAt hy).mul (inv_hasDerivAt hy))
  convert h using 1 <;> simp [centralFirst, centralSecond] <;> ring

theorem completedConstant_half_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => completedConstant t (1 / 2 : ℂ)) (centralFirst y) y := by
  apply (centralHeight_hasDerivAt hy).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact completedConstant_half t ht

/-- The logarithmic central correction has the repeated-root eigenvalue 1/4. -/
theorem centralHeight_euler {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * centralSecond y = (1 / 4 : ℂ) * centralHeight y := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  calc
    _ = -(centralScalar + (Real.log y : ℂ)) * ((y : ℂ) ^ 2 * root2 y) -
        2 * ((y : ℂ) * root1 y) + root0 y := by
      unfold centralSecond
      field_simp [hyC] <;> ring
    _ = _ := by
      rw [root2_relation hy, root1_relation hy]
      unfold centralHeight
      ring

theorem centralHeight_contDiffOn_two :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => centralHeight p.2) upperChart := by
  have hsqrt : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sqrt p.2) upperChart :=
    contDiffOn_snd.sqrt (fun p hp => ne_of_gt hp)
  have hroot : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (Real.sqrt p.2 : ℂ)) upperChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hsqrt
  have hlogR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.log p.2) upperChart :=
    contDiffOn_snd.log (fun p hp => ne_of_gt hp)
  have hlog : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (Real.log p.2 : ℂ)) upperChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hlogR
  simpa only [centralHeight, root0_eq_sqrt] using
    (hroot.const_mul centralScalar).add (hroot.mul hlog)

end

end ImbalancedChen.Part3.CompletedEisensteinCentralHeight
