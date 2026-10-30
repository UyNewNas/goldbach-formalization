import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Finset.Nat

/-! Finite MediumAtom and admissibility data, extracted verbatim with original names. -/
namespace ImbalancedChen.Part3
noncomputable section
open scoped BigOperators
open Classical

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

def MediumAtom.scale (d : MediumAtom) : ℝ := d.U * d.V

def MediumAtom.alphaCarrier (d : MediumAtom) : Finset ℕ :=
  (Finset.Icc (Nat.ceil d.U) (Nat.floor (2 * d.U))).filter
    (fun n => d.intervalLo < (n : ℝ) ∧ (n : ℝ) ≤ d.intervalHi)

def MediumAtom.betaCarrier (d : MediumAtom) : Finset ℕ :=
  Finset.Icc (Nat.ceil d.V) (Nat.floor (2 * d.V))

/-- Concrete dyadic support `Q ≤ q ≤ 2Q`, including the trivial factor
`q=1` at `Q=1`. The manuscript writes `q ≍ Q`; the compiler must assign
overlapping endpoints without multiplicity loss when it chooses its atoms. -/
def factorCarrier (Q : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.ceil Q) (Nat.floor (2 * Q))

/-- Precisely the geometric and coefficient gates of the frozen restricted
medium proposition.  `scale` is the complete convolution product. -/
def MediumAdmissible (B : ℕ) (σ κ c0 : ℝ) (d : MediumAtom) : Prop :=
  1 ≤ d.U ∧ 1 ≤ d.V ∧ 1 ≤ d.Q1 ∧ 1 ≤ d.Q2 ∧ 1 ≤ d.Q3 ∧
  Real.exp (Real.exp 1) < d.scale ∧
  c0 * d.scale ≤ (d.residue.natAbs : ℝ) ∧
  (d.residue.natAbs : ℝ) ≤ d.scale ^ (1 + κ) ∧
  d.Q1 < d.U * d.scale ^ (-σ) ∧
  d.U ^ 2 * d.Q2 * d.Q3 ^ 2 < d.scale ^ (1 - 8 * σ) ∧
  (d.residue.natAbs : ℝ) ^ (7 / 32 : ℝ) * d.U * d.Q1 * d.Q2 ^ 5 * d.Q3 ^ 2 <
    d.scale ^ (2 - 15 * σ) ∧
  d.U ^ (1 + 2 * (7 / 32 : ℝ)) * d.Q1 *
      d.Q2 ^ (5 - 2 * (7 / 32 : ℝ)) * d.Q3 ^ (2 + 2 * (7 / 32 : ℝ)) <
    d.scale ^ (2 - 15 * σ) ∧
  (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) ∧
  (∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
    Nat.Prime p → p ∣ n →
      d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3) < (p : ℝ)) ∧
  (∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ (m.divisors.card : ℝ) ^ B) ∧
  (∀ q ∈ factorCarrier d.Q1, ‖d.gamma1 q‖ ≤ 1 ∧
    (d.gamma1 q ≠ 0 → Nat.Coprime q d.residue.natAbs)) ∧
  (∀ q ∈ factorCarrier d.Q2, ‖d.gamma2 q‖ ≤ 1 ∧
    (d.gamma2 q ≠ 0 → Nat.Coprime q d.residue.natAbs)) ∧
  (∀ q ∈ factorCarrier d.Q3, ‖d.gamma3 q‖ ≤ 1 ∧
    (d.gamma3 q ≠ 0 → Nat.Coprime q d.residue.natAbs))

end
end ImbalancedChen.Part3
