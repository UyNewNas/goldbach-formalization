import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
Expression-only probe of the two existing P2.7 source fixes.
The actual certified bounds and the already proved null-wall theorem are
explicit parameters. No project source, object, registry or acceptance
receipt is read or written, and no project theorem is accepted here.
-/

namespace P27ExpressionProbe

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

set_option Elab.async false

abbrev Point := Fin 4 → ℝ

-- The exact type of hb after the existing lower_sum/upper_sum rewrites.
example (integral : ℝ)
    (hb : (((55858378943374979 / 100000000000000000000 : ℚ) : ℝ) ≤ integral ∧
      integral ≤ ((55858409959907296 / 100000000000000000000 : ℚ) : ℝ))) :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤ integral ∧
      integral ≤ (55858409959907296 / 100000000000000000000 : ℝ) := by
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hb ⊢
  exact hb

-- The exact supplier signature, supplied locally instead of recompiling
-- the already accepted ImbalancedChen.AffinePrimeGates module.
example
    (affinePrimeWall_volume_zero :
      ∀ (L : Point →L[ℝ] ℝ), L ≠ 0 → ∀ (c : ℝ), volume {x | L x = c} = 0)
    (i : Fin 4) (c : ℝ) :
    ∀ᵐ x : Point ∂volume, x i ≠ c := by
  have hproj : (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) ≠ 0 := by
    intro hz
    have hh := congrArg (fun L : Point →L[ℝ] ℝ => L (fun _ => 1)) hz
    norm_num at hh
  rw [ae_iff]
  simpa only [not_not, ContinuousLinearMap.proj_apply] using
    affinePrimeWall_volume_zero
      (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) hproj c

def orderingWallForm : Point →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (3 : Fin 4) : Point →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj (2 : Fin 4) : Point →L[ℝ] ℝ)

theorem orderingWallForm_ne_zero : orderingWallForm ≠ 0 := by
  intro hz
  have hh := congrArg (fun L : Point →L[ℝ] ℝ => L ![0, 0, 0, 1]) hz
  norm_num [orderingWallForm, Matrix.cons_val_two] at hh
  change (1 : ℝ) = 0 at hh
  norm_num at hh

example
    (affinePrimeWall_volume_zero :
      ∀ (L : Point →L[ℝ] ℝ), L ≠ 0 → ∀ (c : ℝ), volume {x | L x = c} = 0) :
    ∀ᵐ x : Point ∂volume, x 3 ≠ x 2 := by
  rw [ae_iff]
  simpa only [not_not, orderingWallForm, sub_apply,
    ContinuousLinearMap.proj_apply, sub_eq_zero] using
    affinePrimeWall_volume_zero orderingWallForm
      orderingWallForm_ne_zero 0

end

end P27ExpressionProbe
