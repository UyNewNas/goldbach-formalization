import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An explicit smooth compact horizontal unit partition for integer
translations. The telescoping difference of the genuine smooth transition
has support in [-1,1]. Its integer translates sum exactly to one; its
first and second derivative translates sum to zero. Endpoint derivative
vanishing is proved by actual one-sided derivative uniqueness, rather
than inferred from a single zero value.
-/
namespace ImbalancedChen.Part3.SmoothIntegerUnitPartition20261026b

noncomputable section
open Set Filter

/-- A finite two-term telescope, valid even when x is an integer. -/
theorem integer_tsum_step_difference (f : ℝ → ℝ) (a b : ℝ)
    (hleft : ∀ x ≤ 0, f x = a) (hright : ∀ x, 1 ≤ x → f x = b) (x : ℝ) :
    (∑' k : ℤ, (f (x + (k : ℝ) + 1) - f (x + (k : ℝ)))) = b - a := by
  classical
  let n : ℤ := Int.floor x
  have hxlo : (n : ℝ) ≤ x := Int.floor_le x
  have hxhi : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
  have hfinite : ∀ k ∉ ({-n, -n - 1} : Finset ℤ),
      f (x + (k : ℝ) + 1) - f (x + (k : ℝ)) = 0 := by
    intro k hk
    have hk0 : k ≠ -n := by intro heq; apply hk; simp [heq]
    have hk1 : k ≠ -n - 1 := by intro heq; apply hk; simp [heq]
    have hcases : k ≤ -n - 2 ∨ 1 - n ≤ k := by omega
    rcases hcases with h | h
    · have hc : (k : ℝ) ≤ -(n : ℝ) - 2 := by exact_mod_cast h
      rw [hleft _ (by linarith), hleft _ (by linarith), sub_self]
    · have hc : 1 - (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      rw [hright _ (by linarith), hright _ (by linarith), sub_self]
  rw [tsum_eq_sum hfinite]
  have hne : -n ≠ -n - 1 := by omega
  rw [Finset.sum_pair hne]
  have hone : 1 ≤ x + ((-n : ℤ) : ℝ) + 1 := by push_cast; linarith
  have hzero : x + ((-n - 1 : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
  have heq : x + ((-n - 1 : ℤ) : ℝ) + 1 = x + ((-n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hright _ hone, hleft _ hzero, heq]
  ring

private theorem deriv_zero_of_const_on_Iic (f : ℝ → ℝ) (c x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hc : ∀ y ≤ x, f y = c) : deriv f x = 0 := by
  have hd : HasDerivWithinAt f 0 (Iic x) x :=
    (hasDerivAt_const x c).hasDerivWithinAt.congr
      (fun y hy => hc y hy) (hc x le_rfl)
  exact (hf.derivWithin (uniqueDiffWithinAt_Iic x)).symm.trans
    (hd.derivWithin (uniqueDiffWithinAt_Iic x))

private theorem deriv_zero_of_const_on_Ici (f : ℝ → ℝ) (c x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hc : ∀ y, x ≤ y → f y = c) : deriv f x = 0 := by
  have hd : HasDerivWithinAt f 0 (Ici x) x :=
    (hasDerivAt_const x c).hasDerivWithinAt.congr
      (fun y hy => hc y hy) (hc x le_rfl)
  exact (hf.derivWithin (uniqueDiffWithinAt_Ici x)).symm.trans
    (hd.derivWithin (uniqueDiffWithinAt_Ici x))

theorem transition_deriv_nonpos (x : ℝ) (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 :=
  deriv_zero_of_const_on_Iic Real.smoothTransition 0 x
    ((Real.smoothTransition.contDiff (n := ∞)).differentiable (by simp) x)
    (fun y hy => Real.smoothTransition.zero_of_nonpos (hy.trans hx))

theorem transition_deriv_one_le (x : ℝ) (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 :=
  deriv_zero_of_const_on_Ici Real.smoothTransition 1 x
    ((Real.smoothTransition.contDiff (n := ∞)).differentiable (by simp) x)
    (fun y hy => Real.smoothTransition.one_of_one_le (hx.trans hy))

theorem transition_deriv_cinfty : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2

theorem transition_second_nonpos (x : ℝ) (hx : x ≤ 0) :
    deriv (deriv Real.smoothTransition) x = 0 :=
  deriv_zero_of_const_on_Iic (deriv Real.smoothTransition) 0 x
    (transition_deriv_cinfty.differentiable (by simp) x)
    (fun y hy => transition_deriv_nonpos y (hy.trans hx))

theorem transition_second_one_le (x : ℝ) (hx : 1 ≤ x) :
    deriv (deriv Real.smoothTransition) x = 0 :=
  deriv_zero_of_const_on_Ici (deriv Real.smoothTransition) 0 x
    (transition_deriv_cinfty.differentiable (by simp) x)
    (fun y hy => transition_deriv_one_le y (hx.trans hy))

private theorem deriv_shift_difference (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv (fun t => f (t + 1) - f t) x = deriv f (x + 1) - deriv f x := by
  have hd : HasDerivAt (fun t => f (t + 1)) (deriv f (x + 1)) x := by
    simpa only [mul_one] using
      ((hf (x + 1)).hasDerivAt.comp x ((hasDerivAt_id x).add_const 1))
  exact (hd.sub (hf x).hasDerivAt).deriv

def horizontalUnitPartition (x : ℝ) : ℝ := Real.smoothTransition (x + 1) - Real.smoothTransition x

theorem horizontalUnitPartition_cinfty : ContDiff ℝ ∞ horizontalUnitPartition :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem horizontalUnitPartition_zero_left (x : ℝ) (hx : x ≤ -1) :
    horizontalUnitPartition x = 0 := by
  rw [horizontalUnitPartition, Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem horizontalUnitPartition_zero_right (x : ℝ) (hx : 1 ≤ x) :
    horizontalUnitPartition x = 0 := by
  rw [horizontalUnitPartition, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le hx, sub_self]

theorem horizontalUnitPartition_tsupport : tsupport horizontalUnitPartition ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (horizontalUnitPartition_zero_left x (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hx (horizontalUnitPartition_zero_right x (le_of_lt (lt_of_not_ge h)))

theorem horizontalUnitPartition_compact : HasCompactSupport horizontalUnitPartition :=
  isCompact_Icc.of_isClosed_subset isClosed_closure horizontalUnitPartition_tsupport

theorem horizontalUnitPartition_deriv (x : ℝ) :
    deriv horizontalUnitPartition x =
      deriv Real.smoothTransition (x + 1) - deriv Real.smoothTransition x :=
  deriv_shift_difference Real.smoothTransition
    ((Real.smoothTransition.contDiff (n := ∞)).differentiable (by simp)) x

theorem horizontalUnitPartition_second (x : ℝ) :
    deriv (deriv horizontalUnitPartition) x =
      deriv (deriv Real.smoothTransition) (x + 1) - deriv (deriv Real.smoothTransition) x := by
  rw [show deriv horizontalUnitPartition =
      (fun t => deriv Real.smoothTransition (t + 1) - deriv Real.smoothTransition t) from
    funext horizontalUnitPartition_deriv]
  exact deriv_shift_difference (deriv Real.smoothTransition)
    (transition_deriv_cinfty.differentiable (by simp)) x

theorem horizontalUnitPartition_integer_sum (x : ℝ) :
    (∑' k : ℤ, horizontalUnitPartition (x + (k : ℝ))) = 1 := by
  simpa only [horizontalUnitPartition, sub_zero] using integer_tsum_step_difference
    Real.smoothTransition 0 1 (fun _ => Real.smoothTransition.zero_of_nonpos)
    (fun _ => Real.smoothTransition.one_of_one_le) x

theorem horizontalUnitPartition_deriv_integer_sum (x : ℝ) :
    (∑' k : ℤ, deriv horizontalUnitPartition (x + (k : ℝ))) = 0 := by
  simp_rw [horizontalUnitPartition_deriv]
  simpa only [sub_self] using integer_tsum_step_difference (deriv Real.smoothTransition) 0 0
    transition_deriv_nonpos transition_deriv_one_le x

theorem horizontalUnitPartition_second_integer_sum (x : ℝ) :
    (∑' k : ℤ, deriv (deriv horizontalUnitPartition) (x + (k : ℝ))) = 0 := by
  simp_rw [horizontalUnitPartition_second]
  simpa only [sub_self] using integer_tsum_step_difference (deriv (deriv Real.smoothTransition)) 0 0
    transition_second_nonpos transition_second_one_le x

end
end ImbalancedChen.Part3.SmoothIntegerUnitPartition20261026b
