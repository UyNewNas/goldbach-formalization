import ImbalancedChen.Part3PrimeStandardCosetRepresentatives
import ImbalancedChen.Part3ActualPrimeHeckeRealBranch
import ImbalancedChen.Part3Gamma0PairedEdgeGreenCancellation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Literal normalized real-matrix identity
  W_p * B_r = realSL(S*T^r),
where the already constructed B_r acts by (z+r)/p. Both sqrt(p) factors
are retained in the proof. Consequently every finite original coset
top-edge branch is the actual Fricke chart at height T/p. Its derivative
before the Fricke action is exactly 1/p, not a normalized probability
weight or a replacement of T/p by T. The local complex map identity is
also retained for honest differentiation of arbitrary outer fields.
-/

noncomputable section
open Complex Matrix Matrix.SpecialLinearGroup Filter Topology
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.PrimeStandardCosets20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeBranchSeparation20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeRealBranch20261026b
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.Gamma0PairedEdgeGreen20261026b
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.PrimeTopFrickeMatrix20261026b

/-- Exact determinant-one matrix equality of the actual two charts. -/
theorem fricke_mul_finite_branch (p : ℕ) (hp : p.Prime) (r : ZMod p) :
    frickeSL p hp.pos * branchSL p hp.pos (some r) =
      realSL (standardRepresentative p (some r)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpR).ne'
  have hsq := Real.sq_sqrt hpR.le
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeSL, frickeMatrix, branchSL, branchRealMatrix, branchMatrix, realSL,
      standardRepresentative, Matrix.SpecialLinearGroup.map_apply_coe,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two,
      ModularGroup.coe_S, ModularGroup.coe_T_zpow, smul_eq_mul] <;>
    field_simp [hs] <;> nlinarith [hsq]

/-- The actual original S*T^r action is W_p((z+r)/p), with no cusp or
coordinate identification assumption. The exact affine action of B_r is
the existing branchSL_some_coe theorem. -/
theorem standardRepresentative_some_action (p : ℕ) (hp : p.Prime) (r : ZMod p)
    (z : UpperHalfPlane) :
    standardRepresentative p (some r) • z =
      frickeSL p hp.pos • (branchSL p hp.pos (some r) • z) := by
  rw [← realSL_action_int (standardRepresentative p (some r)),
    ← fricke_mul_finite_branch p hp r, mul_smul]

/-- The true intermediate height is divided by p. -/
theorem finite_branch_height (p : ℕ) (hp : p.Prime) (r : ZMod p) (z : UpperHalfPlane) :
    (branchSL p hp.pos (some r) • z).im = z.im / (p : ℝ) := by
  simpa only [← Complex.ofReal_natCast, Complex.div_ofReal_im, Complex.add_im,
    Complex.ofReal_im, add_zero] using congrArg Complex.im (branchSL_some_coe p hp.pos r z)

/-- Exact local identity before differentiating outer functions. -/
theorem standardMap_eq_fricke_branch_eventually (p : ℕ) (hp : p.Prime) (r : ZMod p)
    (z : UpperHalfPlane) :
    slMap (realSL (standardRepresentative p (some r))) =ᶠ[𝓝 (z : ℂ)]
      (fun w => slMap (frickeSL p hp.pos) (slMap (branchSL p hp.pos (some r)) w)) := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  let W : UpperHalfPlane := ⟨w, hw⟩
  have hB : slMap (branchSL p hp.pos (some r)) w =
      ((branchSL p hp.pos (some r) • W : UpperHalfPlane) : ℂ) := by
    change slMap _ (W : ℂ) = _
    rw [slMap_eq_action]
  change slMap (realSL (standardRepresentative p (some r))) (W : ℂ) = _
  rw [slMap_eq_action, realSL_action_int, hB, slMap_eq_action,
    standardRepresentative_some_action p hp r]

/-- The actual affine branch tangent multiplier. This 1/p factor is
exactly the one required by the p horizontal subinterval partition. -/
theorem slFactor_finite_branch (p : ℕ) (hp : p.Prime) (r : ZMod p) (w : ℂ) :
    slFactor (branchSL p hp.pos (some r)) w = 1 / (p : ℂ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpR).ne'
  have hsq : (Real.sqrt (p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hpR.le
  have hden : UpperHalfPlane.denom (realGL (branchSL p hp.pos (some r))) w =
      (Real.sqrt (p : ℝ) : ℂ) := by
    simp [realGL, UpperHalfPlane.denom, branchSL, branchRealMatrix, branchMatrix,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.coeFn_eq_coe,
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, smul_eq_mul] <;>
      rw [← hsq] <;> field_simp [hs] <;> ring
  rw [slFactor, hden, hsq]

end ImbalancedChen.Part3.PrimeTopFrickeMatrix20261026b
