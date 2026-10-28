import ImbalancedChen.P5OldFifthActualChildJensenIntegral
import ImbalancedChen.P5NamedFifthPayloadSemantics

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Two concrete original grid1600 all-zero child instances. The arithmetic
payload proof supplies fixed parent picks and actual child d; no gap
integral, ratio check, or Jensen conclusion is taken as a new premise.
These are whole-child unbuffered positive frozen-parent integrals.
-/

namespace ImbalancedChen.P5NamedFifthChildJensenInstances
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateBarycentric
open P5OldFifthChildQJensen
open P5OldFifthPointwiseQ
open P5NamedFifthPayloadSemantics
open P5OldFifthActualChildJensenIntegral

private theorem parent0_last_child_endpoint :
    childRight selectedParent0 zeroChild 4 = (101 : ℝ) / 1600 := by
  norm_num [childRight, childRightNumer, childLeftNumer, selectedParent0, zeroChild, width]

private theorem parent1_last_child_endpoint :
    childRight selectedParent1 zeroChild 4 = (101 : ℝ) / 1600 := by
  norm_num [childRight, childRightNumer, childLeftNumer, selectedParent1, zeroChild, width]

/-- Parent picks and all 32 actual grid1600 vertices give d=29824;
this is not the parent grid400 field 5984. -/
theorem parent0_zero_child_Q_average :
    Q 4 (233 / 808 : ℝ) ≤
      ⨍ t in childBox selectedParent0 zeroChild,
        Q 4 (childX (sourcePicks selectedParent0) selectedParent0 zeroChild t) := by
  have h := actual_child_Q_average_lower (sourcePicks selectedParent0) selectedParent0
    zeroChild (parent0_childLeft_pos zeroChild)
    (b := savedRatio selectedParent0)
    (by rw [parent0_ratio]; norm_num) (by rw [parent0_ratio]; norm_num)
    (fun t ht => parent0_child_new_ratio zeroChild t ht)
    29824 (by norm_num) parent0_actual_zero_child_hd
  rw [parent0_ratio, parent0_last_child_endpoint] at h
  norm_num at h
  exact h

/-- The second actual parent uses its distinct source ratio 399/100
and d=25152, instead of the parent grid400 field 5232. -/
theorem parent1_zero_child_Q_average :
    Q (399 / 100 : ℝ) (393 / 1616 : ℝ) ≤
      ⨍ t in childBox selectedParent1 zeroChild,
        Q (399 / 100 : ℝ)
          (childX (sourcePicks selectedParent1) selectedParent1 zeroChild t) := by
  have h := actual_child_Q_average_lower (sourcePicks selectedParent1) selectedParent1
    zeroChild (parent1_childLeft_pos zeroChild)
    (b := savedRatio selectedParent1)
    (by rw [parent1_ratio]; norm_num) (by rw [parent1_ratio]; norm_num)
    (fun t ht => parent1_child_new_ratio zeroChild t ht)
    25152 (by norm_num) parent1_actual_zero_child_hd
  rw [parent1_ratio, parent1_last_child_endpoint] at h
  norm_num at h
  exact h

/-- An actual whole-child positive-kernel lower bound with every local
geometry and vertex premise discharged by the literal parent0 payload. -/
theorem parent0_zero_child_positive_kernel_integral :
    childVolume selectedParent0 zeroChild * childPrefactor selectedParent0 zeroChild *
        Q 4 (233 / 808 : ℝ) ≤
      ∫ t in childBox selectedParent0 zeroChild,
        frozenUpperPositiveKernel (sourcePicks selectedParent0) selectedParent0 t := by
  have h := integral_frozenUpperPositiveKernel_ge_child_Jensen
    (sourcePicks selectedParent0) selectedParent0 zeroChild
    (parent0_childLeft_pos zeroChild) (b := savedRatio selectedParent0)
    (by rw [parent0_ratio]; norm_num) (by rw [parent0_ratio]; norm_num)
    (fun t ht => parent0_child_new_ratio zeroChild t ht)
    29824 (by norm_num) parent0_actual_zero_child_hd
  rw [parent0_ratio, parent0_last_child_endpoint] at h
  norm_num at h
  exact h

/-- The companion actual child; its independent raw row and source picks
are retained throughout the same genuine moving strict-gate profile. -/
theorem parent1_zero_child_positive_kernel_integral :
    childVolume selectedParent1 zeroChild * childPrefactor selectedParent1 zeroChild *
        Q (399 / 100 : ℝ) (393 / 1616 : ℝ) ≤
      ∫ t in childBox selectedParent1 zeroChild,
        frozenUpperPositiveKernel (sourcePicks selectedParent1) selectedParent1 t := by
  have h := integral_frozenUpperPositiveKernel_ge_child_Jensen
    (sourcePicks selectedParent1) selectedParent1 zeroChild
    (parent1_childLeft_pos zeroChild) (b := savedRatio selectedParent1)
    (by rw [parent1_ratio]; norm_num) (by rw [parent1_ratio]; norm_num)
    (fun t ht => parent1_child_new_ratio zeroChild t ht)
    25152 (by norm_num) parent1_actual_zero_child_hd
  rw [parent1_ratio, parent1_last_child_endpoint] at h
  norm_num at h
  exact h

end
end ImbalancedChen.P5NamedFifthChildJensenInstances
