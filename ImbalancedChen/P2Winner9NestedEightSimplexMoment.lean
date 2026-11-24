import ImbalancedChen.P2AffineSimplexMomentLaw
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The earlier source-only P2AffineSimplexMomentLaw proves the one-dimensional
beta monomial integral from Mathlib's FTC primitives. This new source
iterates that calculus identity through EIGHT simplex coordinates, with
an arbitrary residual barycentric exponent m0 and arbitrary coordinate
exponents. It obtains the exact factorial formula for the nested integral,
and in particular for total exponent degree at most four.

This is not yet the actual Lebesgue integral over Δ8. The remaining
primitive is the Fubini slicing equality from the measurable closed set
`standardSimplex s` to `nestedMoment`; it must be proved rather than
supplied as an hMoment or an assumed final mixed identity. The beta source
itself is not an accepted installed module. No Lean, producer, checker or
numerical replay ran.
-/

namespace ImbalancedChen.P2Winner9NestedEightSimplexMoment

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Certificates.P2AffineSimplexMomentLaw

def totalDegree (m0 : Nat) (ms : List Nat) : Nat :=
  m0 + ms.sum + ms.length

def factorialProduct (ms : List Nat) : Nat :=
  (ms.map Nat.factorial).prod

def coefficient (m0 : Nat) (ms : List Nat) : ℝ :=
  ((m0.factorial * factorialProduct ms : Nat) : ℝ) /
    ((totalDegree m0 ms).factorial : ℝ)

/-- Integrate successive nonnegative simplex coordinates; the remaining
coordinate is the residual `s - sum(x)`, raised to exponent m0. -/
def nestedMoment (m0 : Nat) : List Nat → ℝ → ℝ
  | [], s => s^m0
  | a :: ms, s =>
      ∫ x in (0 : ℝ)..s, x^a * nestedMoment m0 ms (s - x)

private theorem coefficient_cons (m0 a : Nat) (ms : List Nat) :
    coefficient m0 ms *
        ((a.factorial : ℝ) * ((totalDegree m0 ms).factorial : ℝ) /
          ((a + totalDegree m0 ms + 1).factorial : ℝ)) =
      coefficient m0 (a :: ms) := by
  have hi : totalDegree m0 (a :: ms) = a + totalDegree m0 ms + 1 := by
    simp [totalDegree]
    omega
  have hOld : ((totalDegree m0 ms).factorial : ℝ) ≠ 0 := by positivity
  have hNew : ((a + totalDegree m0 ms + 1).factorial : ℝ) ≠ 0 := by positivity
  unfold coefficient factorialProduct
  simp only [List.map_cons, List.prod_cons, Nat.cast_mul, hi]
  field_simp [hOld, hNew]
  ring

/-- Exact factorial evaluation of every iterated simplex monomial.
The induction uses the previously proved beta monomial integral once per
coordinate and does not assume a dimension-eight moment law. -/
theorem nestedMoment_eq (m0 : Nat) (ms : List Nat) (s : ℝ) :
    nestedMoment m0 ms s =
      coefficient m0 ms * s ^ totalDegree m0 ms := by
  induction ms generalizing s with
  | nil =>
      simp [nestedMoment, coefficient, factorialProduct, totalDegree]
  | cons a ms ih =>
      let b := totalDegree m0 ms
      let c := coefficient m0 ms
      have hstep : nestedMoment m0 (a :: ms) s =
          c * betaMonomial a b s := by
        calc
          nestedMoment m0 (a :: ms) s =
              ∫ x in (0 : ℝ)..s, c * (x^a * (s - x)^b) := by
                simp only [nestedMoment]
                congr 1
                funext x
                rw [ih]
                dsimp [c, b]
                ring
          _ = c * betaMonomial a b s := by
                rw [betaMonomial, intervalIntegral.integral_const_mul]
      rw [hstep, betaMonomial_eq]
      have he : totalDegree m0 (a :: ms) = a + b + 1 := by
        simp [totalDegree, b]
        omega
      rw [he]
      rw [← coefficient_cons m0 a ms]
      dsimp [c, b]
      ring

/-- The exact EIGHT-fold nested identity. It is stronger than the
degree-four range required by mixed k=1. -/
theorem nested_eight_factorial (m0 : Nat) (ms : List Nat)
    (hLength : ms.length = 8) (s : ℝ) :
    nestedMoment m0 ms s =
      (((m0.factorial * factorialProduct ms : Nat) : ℝ) /
        ((m0 + ms.sum + 8).factorial : ℝ)) *
          s ^ (m0 + ms.sum + 8) := by
  simpa [coefficient, totalDegree, hLength] using
    nestedMoment_eq m0 ms s

/-- Actual canonical eight-simplex in coordinate form. The set-integral
slice equality to `nestedMoment` is the precise unproved next primitive. -/
def standardSimplex (s : ℝ) : Set (Fin 8 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin 8, x i) ≤ s}

def actualMoment (m0 : Nat) (ms : Fin 8 → Nat) (s : ℝ) : ℝ :=
  ∫ x in standardSimplex s,
    (s - ∑ i : Fin 8, x i)^m0 *
      (∏ i : Fin 8, (x i)^(ms i))

end

end ImbalancedChen.P2Winner9NestedEightSimplexMoment
