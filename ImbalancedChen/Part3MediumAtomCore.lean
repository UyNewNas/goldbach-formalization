import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! The medium atom and its finite dyadic factor support. -/

namespace ImbalancedChen.Part3

noncomputable section

/-- One local convolution, with one interval and fixed coefficients shared
by every term of the modulus sum.  The residue may move with the atom. -/
structure MediumAtom where
  U : ℝ
  V : ℝ
  Q1 : ℝ
  Q2 : ℝ
  Q3 : ℝ
  residue : ℤ
  intervalLo : ℝ
  intervalHi : ℝ
  alpha : ℕ → ℂ
  beta : ℕ → ℂ
  gamma1 : ℕ → ℂ
  gamma2 : ℕ → ℂ
  gamma3 : ℕ → ℂ

/-- Concrete dyadic support `Q ≤ q ≤ 2Q`, including the trivial factor
`q=1` at `Q=1`. The manuscript writes `q ≍ Q`; the compiler must assign
overlapping endpoints without multiplicity loss when it chooses its atoms. -/
def factorCarrier (Q : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.ceil Q) (Nat.floor (2 * Q))

end

end ImbalancedChen.Part3
