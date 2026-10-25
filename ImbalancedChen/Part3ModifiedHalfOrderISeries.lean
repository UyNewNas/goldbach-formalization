import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# An actual modified I-series at real order one half

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The normalized half-order solution is defined by the convergent series
  sqrt(2/pi) * q^(-1/2) * sum_n q^(2n+1)/(2n+1)!.
On q>0 this is the standard half-order closed form
  sqrt(2/pi) * q^(-1/2) * sinh q.
Its first and second actual q-derivatives are calculated, and the
modified Bessel equation with nu^2=1/4 is derived algebraically.

This is a real nonnegative-order atom. It does not construct I_(2it),
identify a generic Gamma-normalized I implementation (none exists in the
pinned special-function library), or assert a Wronskian relation with
the project's actual K integral.
-/

namespace ImbalancedChen.Part3.ModifiedHalfOrderISourceOnly

noncomputable section

open Filter Set
open scoped Topology

def halfINormalization : ℝ := Real.sqrt (2 / Real.pi)

/-- The actual odd-factorial series term, with its fixed half-order normalization. -/
def modifiedHalfITerm (q : ℝ) (n : ℕ) : ℝ :=
  halfINormalization * q ^ (-1 / 2 : ℝ) *
    (q ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))

/-- Defined by the infinite series, not by an assumed differential equation. -/
def modifiedHalfI (q : ℝ) : ℝ := ∑' n : ℕ, modifiedHalfITerm q n

theorem modifiedHalfITerm_hasSum (q : ℝ) :
    HasSum (modifiedHalfITerm q)
      (halfINormalization * q ^ (-1 / 2 : ℝ) * Real.sinh q) := by
  exact (Real.hasSum_sinh q).mul_left (halfINormalization * q ^ (-1 / 2 : ℝ))

/-- Actual convergence, for every real q under the totalized real-power convention. -/
theorem modifiedHalfITerm_summable (q : ℝ) : Summable (modifiedHalfITerm q) :=
  (modifiedHalfITerm_hasSum q).summable

theorem modifiedHalfI_eq_closedForm (q : ℝ) :
    modifiedHalfI q = halfINormalization * q ^ (-1 / 2 : ℝ) * Real.sinh q :=
  (modifiedHalfITerm_hasSum q).tsum_eq

/-- Explicit first derivative jet, with every q-dependent factor displayed. -/
def modifiedHalfIFirst (q : ℝ) : ℝ :=
  halfINormalization *
    ((-1 / 2 : ℝ) * q ^ (-3 / 2 : ℝ) * Real.sinh q +
      q ^ (-1 / 2 : ℝ) * Real.cosh q)

/-- Explicit second derivative jet. -/
def modifiedHalfISecond (q : ℝ) : ℝ :=
  halfINormalization *
    ((3 / 4 : ℝ) * q ^ (-5 / 2 : ℝ) * Real.sinh q -
      q ^ (-3 / 2 : ℝ) * Real.cosh q + q ^ (-1 / 2 : ℝ) * Real.sinh q)

theorem hasDerivAt_rpow_minus_half {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => x ^ (-1 / 2 : ℝ))
      ((-1 / 2 : ℝ) * q ^ (-3 / 2 : ℝ)) q := by
  convert Real.hasDerivAt_rpow_const (x := q) (p := (-1 / 2 : ℝ)) (Or.inl hq.ne')
    using 1 <;> norm_num

theorem hasDerivAt_rpow_minus_three_halves {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => x ^ (-3 / 2 : ℝ))
      ((-3 / 2 : ℝ) * q ^ (-5 / 2 : ℝ)) q := by
  convert Real.hasDerivAt_rpow_const (x := q) (p := (-3 / 2 : ℝ)) (Or.inl hq.ne')
    using 1 <;> norm_num

/-- The derivative of the series-defined function, obtained through its
proved convergent closed form rather than postulating termwise calculus. -/
theorem modifiedHalfI_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt modifiedHalfI (modifiedHalfIFirst q) q := by
  have heq : modifiedHalfI = fun x =>
      halfINormalization * x ^ (-1 / 2 : ℝ) * Real.sinh x := by
    funext x
    exact modifiedHalfI_eq_closedForm x
  rw [heq]
  have h := ((hasDerivAt_rpow_minus_half hq).const_mul halfINormalization).mul
    (Real.hasDerivAt_sinh q)
  convert h using 1 <;> dsimp [modifiedHalfIFirst] <;> ring

/-- The explicitly computed first jet has the explicitly computed second jet. -/
theorem modifiedHalfIFirst_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt modifiedHalfIFirst (modifiedHalfISecond q) q := by
  have hleft := ((hasDerivAt_rpow_minus_three_halves hq).const_mul (-1 / 2 : ℝ)).mul
    (Real.hasDerivAt_sinh q)
  have hright := (hasDerivAt_rpow_minus_half hq).mul (Real.hasDerivAt_cosh q)
  have h := (hleft.add hright).const_mul halfINormalization
  convert h using 1 <;> dsimp [modifiedHalfIFirst, modifiedHalfISecond] <;> ring

/-- This is the actual second derivative of the series function on q>0. -/
theorem deriv_modifiedHalfI_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt (deriv modifiedHalfI) (modifiedHalfISecond q) q := by
  apply (modifiedHalfIFirst_hasDerivAt hq).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  exact (modifiedHalfI_hasDerivAt hx).deriv

theorem rpow_minus_three_halves_eq {q : ℝ} (hq : 0 < q) :
    q ^ (-3 / 2 : ℝ) = q ^ (-1 / 2 : ℝ) / q := by
  convert Real.rpow_sub_one hq.ne' (-1 / 2 : ℝ) using 1 <;> norm_num

theorem rpow_minus_five_halves_eq {q : ℝ} (hq : 0 < q) :
    q ^ (-5 / 2 : ℝ) = q ^ (-1 / 2 : ℝ) / q ^ 2 := by
  convert Real.rpow_sub_natCast hq.ne' (-1 / 2 : ℝ) 2 using 1 <;> norm_num

/-- The exact modified Bessel equation for the computed jets. -/
theorem modifiedHalfI_jet_equation {q : ℝ} (hq : 0 < q) :
    q ^ 2 * modifiedHalfISecond q + q * modifiedHalfIFirst q -
      (q ^ 2 + (1 / 4 : ℝ)) * modifiedHalfI q = 0 := by
  rw [modifiedHalfI_eq_closedForm]
  dsimp only [modifiedHalfIFirst, modifiedHalfISecond]
  rw [rpow_minus_three_halves_eq hq, rpow_minus_five_halves_eq hq]
  field_simp [hq.ne']
  <;> ring

/-- The actual series-defined half-order I solves the modified Bessel ODE;
neither a target ODE nor a supplier encoding the ODE is a premise. -/
theorem modifiedHalfI_modifiedBessel_equation {q : ℝ} (hq : 0 < q) :
    q ^ 2 * deriv (deriv modifiedHalfI) q + q * deriv modifiedHalfI q -
      (q ^ 2 + (1 / 4 : ℝ)) * modifiedHalfI q = 0 := by
  rw [(deriv_modifiedHalfI_hasDerivAt hq).deriv, (modifiedHalfI_hasDerivAt hq).deriv]
  exact modifiedHalfI_jet_equation hq

end

end ImbalancedChen.Part3.ModifiedHalfOrderISourceOnly
