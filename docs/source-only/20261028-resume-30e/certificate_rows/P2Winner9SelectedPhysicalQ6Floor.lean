import ImbalancedChen.P2Winner9SelectedPhysicalMeans
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original Q6 row-floor fields are bound to the same row data and measured
physical correction. The remaining T10 Jensen-gap expectation bound is
explicitly NOT replaced by a target-shaped analytic enclosure hypothesis.
All closed finite floor proof bodies below remain unevaluated.
-/

namespace ImbalancedChen.P2Winner9SelectedPhysicalQ6Floor

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedAllMixedMoments
open ImbalancedChen.P2Winner9SelectedPhysicalMeans
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

def totalFloor (r : Fin 2) : Nat :=
  if r = 0 then 18932817790080969734485 else 18300039665022900361522

def rawFloor (r : Fin 2) : Nat :=
  if r = 0 then 33553775924834770601 else 6463231997558714529

/-- Exact original mixed Q6 directed floor obligations, checked against
the independently reconstructed typed coefficients, not summary gains.
NOT EXECUTED; the compiler owner may need resource-safe coefficient code. -/
theorem actual_Q6_rounding : ∀ r : Fin 2,
    curvatureFloorQ80 (P2Winner9MixedDegreeSixExactAssembly.total (data r)).num
      (P2Winner9MixedDegreeSixExactAssembly.total (data r)).den (totalFloor r) ∧
      jensenProductFloorQ96 (data r).jensenNum (data r).jensenDen
        (totalFloor r) (rawFloor r) := by
  decide +kernel

def physicalQ6 (r : Fin 2) : ℝ :=
  ∑ j : Fin 10, ∑ k : Fin 7,
    (((9 + k.val).choose k.val : ℝ) *
      ((∫ z in sourceSupport (vertices r),
        physicalMixedK (fun i => (means r i : ℝ)) (upper r : ℝ) j k.val z) /
          gapMass r)) /
      (2 * (((data r).maxima j : ℝ) / (data r).L)^2 *
        (((data r).U : ℝ) / (data r).L)^10)

theorem physicalQ6_eq_source (r : Fin 2) :
    physicalQ6 r = (value (q6 (data r)) : ℝ) :=
  (physical_Q6_identity r).symm

/-- Nonnegativity comes from the actual physical integrands, including
Y>=0 on the full source support, rather than a positivity assumption on
the signed intermediate convolution coefficients. -/
theorem physicalQ6_nonneg (r : Fin 2) : 0 ≤ physicalQ6 r := by
  unfold physicalQ6
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  have hI : 0 ≤ ∫ z in sourceSupport (vertices r),
      physicalMixedK (fun i => (means r i : ℝ)) (upper r : ℝ) j k.val z := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem
      (sourceSupport_measurable (vertices r) (row_det_ne_zero r))] with z hz
    unfold physicalMixedK
    exact mul_nonneg
      (mul_nonneg (actual_support_caps r hz).1
        (pow_nonneg (actual_uniform_Y r hz).1 _)) (sq_nonneg _)
  have hL : (0 : ℝ) < (data r).L := by exact_mod_cast (data r).LPos
  have hU : (0 : ℝ) < (data r).U := by exact_mod_cast (data r).UPos
  have hV : (0 : ℝ) < (data r).maxima j := by exact_mod_cast (data r).maximaPos j
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hI (gapMass_pos r).le)) (by positivity)

theorem actual_source_Q6_nonneg (r : Fin 2) : 0 ≤ (value (q6 (data r)) : ℝ) := by
  rw [← physicalQ6_eq_source]
  exact physicalQ6_nonneg r

/-- The directed original floor is below the exact source T10 plus the
true measured physical Q6 correction. The next remaining step is to bound
the full reciprocal-product integral by this same expression. -/
theorem original_floor_measured_expression (r : Fin 2) :
    (rawFloor r : ℝ) / (q96 : ℝ) ≤
      ((data r).jensenNum : ℝ) / (data r).jensenDen *
        (1 + (value (t10 (data r)) : ℝ) + physicalQ6 r) := by
  have h := mixed_directed_floor_semantics (data r) (totalFloor r) (rawFloor r)
    (actual_Q6_rounding r).1 (actual_Q6_rounding r).2
  rw [P2Winner9MixedDegreeSixExactAssembly.total, add_value] at h
  rw [physicalQ6_eq_source]
  have hr := (show ((rawFloor r : ℚ) / q96 : ℝ) ≤
      (((((data r).jensenNum : ℚ) / (data r).jensenDen) *
        (1 + (value (t10 (data r)) + value (q6 (data r))))) : ℝ) from
      by exact_mod_cast h)
  push_cast at hr
  convert hr using 1 <;> ring

end

end ImbalancedChen.P2Winner9SelectedPhysicalQ6Floor
