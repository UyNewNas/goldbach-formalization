import ImbalancedChen.Part3MaassFiniteCoreL2LinearOperator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Actual compact-tensor lift for the inverse hyperbolic-to-planar L² map.
Multiplication of the vertical factor by height preserves the real C²
compact positive-height core. Division by height cancels it everywhere,
including at zero because positive-height support forces the value there to vanish.
-/

namespace ImbalancedChen.Part3.MaassTensorHeightLift20261025a

noncomputable section

open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreResolventCoercivity20261025a

def heightMultiplyTensor (T : CompactTensor) : CompactTensor where
  horizontal := T.horizontal
  vertical := fun y => (y : ℂ) * T.vertical y
  horizontal_smooth := T.horizontal_smooth
  vertical_smooth := Complex.ofRealCLM.contDiff.mul T.vertical_smooth
  horizontal_compact := T.horizontal_compact
  vertical_compact := T.vertical_compact.mul_left
  vertical_positive := tsupport_mul_subset_right.trans T.vertical_positive

theorem heightMultiplyTensor_function (T : CompactTensor) (z : UpperHalfPlane) :
    tensorFunctionH (heightMultiplyTensor T).horizontal
      (heightMultiplyTensor T).vertical z =
      (z.im : ℂ) * tensorFunctionH T.horizontal T.vertical z := by
  simp only [tensorFunctionH_eq, heightMultiplyTensor]
  ring

theorem divideHeight_heightMultiplyTensor_vertical (T : CompactTensor) :
    divideHeight (heightMultiplyTensor T).vertical = T.vertical := by
  funext y
  by_cases hy : y = 0
  · subst y
    have hz : T.vertical 0 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact (lt_irrefl (0 : ℝ)) (T.vertical_positive h)
    simp [divideHeight, heightMultiplyTensor, hz]
  · have hc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    simp only [divideHeight, heightMultiplyTensor, Complex.ofReal_inv]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem unweight_heightMultiplyTensor (T : CompactTensor) {p : ℝ × ℝ}
    (hp : p ∈ upperChart) :
    ((p.2⁻¹ : ℝ) : ℂ) *
      tensorFunction (heightMultiplyTensor T).horizontal
        (heightMultiplyTensor T).vertical p =
      tensorFunction T.horizontal T.vertical p := by
  have hv := congrFun (divideHeight_heightMultiplyTensor_vertical T) p.2
  change ((p.2⁻¹ : ℝ) : ℂ) *
      (T.horizontal p.1 * (heightMultiplyTensor T).vertical p.2) =
      T.horizontal p.1 * T.vertical p.2
  change ((p.2⁻¹ : ℝ) : ℂ) * (heightMultiplyTensor T).vertical p.2 =
      T.vertical p.2 at hv
  calc
    _ = T.horizontal p.1 *
        (((p.2⁻¹ : ℝ) : ℂ) * (heightMultiplyTensor T).vertical p.2) := by ring
    _ = _ := by rw [hv]

end

end ImbalancedChen.Part3.MaassTensorHeightLift20261025a
