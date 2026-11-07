import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
Exact polynomial jets for u-derivatives of exp(-q cosh u), for every real q.
This is the algebraic/differential precursor to a separate Schwartz proof;
no decay estimate or Schwartz membership is asserted here.
-/

namespace ImbalancedChen.Part3.KProfileDerivativePolynomialsSourceOnly
noncomputable section
open Polynomial

def profile (q u : ℝ) : ℝ := Real.exp (-q * Real.cosh u)

def nextA (q : ℝ) (A B : ℝ[X]) : ℝ[X] :=
  X * B + (X ^ 2 - 1) * (B.derivative - C q * B)

def nextB (q : ℝ) (A B : ℝ[X]) : ℝ[X] :=
  A.derivative - C q * A

/-- Both polynomial sequences are generated simultaneously from (1,0). -/
def jet (q : ℝ) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 0)
  | n + 1 =>
      (nextA q (jet q n).1 (jet q n).2,
       nextB q (jet q n).1 (jet q n).2)

def A (q : ℝ) (n : ℕ) : ℝ[X] := (jet q n).1
def B (q : ℝ) (n : ℕ) : ℝ[X] := (jet q n).2

theorem A_zero (q : ℝ) : A q 0 = 1 := rfl
theorem B_zero (q : ℝ) : B q 0 = 0 := rfl

theorem A_succ (q : ℝ) (n : ℕ) :
    A q (n + 1) = X * B q n +
      (X ^ 2 - 1) * ((B q n).derivative - C q * B q n) := rfl

theorem B_succ (q : ℝ) (n : ℕ) :
    B q (n + 1) = (A q n).derivative - C q * A q n := rfl

def jetValue (q : ℝ) (A B : ℝ[X]) (u : ℝ) : ℝ :=
  (A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)) * profile q u

/-- One exact u-derivative closes under the stated polynomial recursion. -/
theorem hasDerivAt_jetValue (q : ℝ) (A B : ℝ[X]) (u : ℝ) :
    HasDerivAt (jetValue q A B)
      (jetValue q (nextA q A B) (nextB q A B) u) u := by
  have hcosh := Real.hasDerivAt_cosh u
  have hsinh := Real.hasDerivAt_sinh u
  have hA : HasDerivAt (fun v : ℝ => A.eval (Real.cosh v))
      (A.derivative.eval (Real.cosh u) * Real.sinh u) u :=
    (A.hasDerivAt (Real.cosh u)).comp u hcosh
  have hB : HasDerivAt (fun v : ℝ => B.eval (Real.cosh v))
      (B.derivative.eval (Real.cosh u) * Real.sinh u) u :=
    (B.hasDerivAt (Real.cosh u)).comp u hcosh
  have hinner : HasDerivAt (fun v : ℝ => -q * Real.cosh v)
      (-q * Real.sinh u) u := hcosh.const_mul (-q)
  have hprofile : HasDerivAt (profile q)
      (profile q u * (-q * Real.sinh u)) u := by
    simpa only [profile] using (Real.hasDerivAt_exp _).comp u hinner
  have hfirst : HasDerivAt
      (fun v : ℝ => A.eval (Real.cosh v) +
        Real.sinh v * B.eval (Real.cosh v))
      (A.derivative.eval (Real.cosh u) * Real.sinh u +
        (Real.cosh u * B.eval (Real.cosh u) +
          Real.sinh u *
            (B.derivative.eval (Real.cosh u) * Real.sinh u))) u := by
    exact hA.add (hsinh.mul hB)
  have hs2 : Real.sinh u ^ 2 = Real.cosh u ^ 2 - 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq u]
  convert hfirst.mul hprofile using 1
  · funext v
    rfl
  · simp only [jetValue, nextA, nextB, eval_add, eval_mul,
      eval_sub, eval_X, eval_pow, eval_one, eval_C]
    rw [← hs2]
    ring

/-- All ordinary iterated derivatives have a literal polynomial jet. -/
theorem iteratedDeriv_profile_eq (q : ℝ) (n : ℕ) (u : ℝ) :
    iteratedDeriv n (profile q) u =
      jetValue q (A q n) (B q n) u := by
  induction n generalizing u with
  | zero =>
      simp [iteratedDeriv_zero, A_zero, B_zero, jetValue]
  | succ n ih =>
      have hfun : iteratedDeriv n (profile q) =
          jetValue q (A q n) (B q n) := by
        funext v
        exact ih v
      rw [iteratedDeriv_succ, hfun]
      simpa only [A_succ, B_succ, nextA, nextB] using
        (hasDerivAt_jetValue q (A q n) (B q n) u).deriv

/-- Smoothness follows directly from the real exponential and hyperbolic cosine. -/
theorem profile_contDiff (q : ℝ) : ContDiff ℝ ⊤ (profile q) := by
  unfold profile
  fun_prop

end
end ImbalancedChen.Part3.KProfileDerivativePolynomialsSourceOnly
