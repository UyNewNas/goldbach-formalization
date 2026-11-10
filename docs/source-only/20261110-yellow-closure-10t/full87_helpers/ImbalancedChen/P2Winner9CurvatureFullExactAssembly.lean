import ImbalancedChen.P2Winner9CurvatureExactMomentFloor
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This reconstructs the full exact `T10 + Q_T` rational for a typed nine-vertex
simplex. `T10` follows the pinned plain producer's complete-homogeneous
moment formula. `Q_T` adds all ten signed D2 transverse terms from the
curvature producer. Positive-denominator pairs preserve exact numerators
and denominators through the sum, before one directed Q80 floor. The
following Q96 floor multiplies by the positive exact Jensen factor.

No producer, Lean kernel, checker, or numerical certificate was executed.
No actual row has been supplied with its primitive gap, deviation, and
exact Jensen data. In particular, the row21 literal floors alone cannot
instantiate this theorem. Physical cap, analytic enclosure, and all-row
checks remain separate obligations.
-/

namespace ImbalancedChen.P2Winner9CurvatureFullExactAssembly

open ImbalancedChen.P2Winner9CurvatureExactMomentFloor

/-- Source-level primitive integer data for a physical nine-vertex simplex.
The relation of these integers to actual geometric vertices is a separate
physical reconstruction check. -/
structure SimplexData where
  gaps : Fin 9 → Nat
  y : Fin 9 → Nat
  L : Nat
  U : Nat
  deviations : Fin 10 → Fin 9 → ℤ
  maxima : Fin 10 → Nat
  jensenNum : Nat
  jensenDen : Nat
  gapsPos : 0 < gapTotal gaps
  LPos : 0 < L
  UPos : 0 < U
  maximaPos : ∀ j, 0 < maxima j
  jensenDenPos : 0 < jensenDen

/-- Complete homogeneous degree-k polynomial in the nine integer y-values. -/
def homogeneous (y : Fin 9 → Nat) (k : Nat) : Nat :=
  ∑ α : Fin 9 → Fin (k + 1),
    if (∑ i : Fin 9, (α i).val) = k then
      ∏ i : Fin 9, y i ^ (α i).val
    else 0

def powerMoment (d : SimplexData) (k : Nat) : Nat :=
  ∑ i : Fin 9, d.gaps i * (d.y i)^k

/-- The producer computes this convolution by its in-place h recurrence. -/
def weightedMoment (d : SimplexData) (k : Nat) : Nat :=
  ∑ j ∈ Finset.range (k + 1),
    homogeneous d.y (k - j) * powerMoment d j

def H (d : SimplexData) : Nat := 10 * gapTotal d.gaps

def meanNumerator (d : SimplexData) : Nat :=
  gapTotal d.gaps * (∑ i : Fin 9, d.y i) +
    (∑ i : Fin 9, d.gaps i * d.y i)

def D (d : SimplexData) : Nat := H d * d.U

/-- Signed exact kth Jensen gap numerator in the pinned `joint_ratio` code. -/
def z (d : SimplexData) (k : Nat) : ℤ :=
  (weightedMoment d k : ℤ) * (H d : ℤ)^k -
    (gapTotal d.gaps : ℤ) * ((9 + k).choose k : ℤ) *
      (meanNumerator d : ℤ)^k

def t10Numerator (d : SimplexData) : ℤ :=
  (∑ k ∈ Finset.Icc 2 10, z d k * (D d : ℤ)^(10 - k)) *
    (d.L : ℤ)^10

def t10Denominator (d : SimplexData) : Nat :=
  gapTotal d.gaps * (D d)^10 * d.U^10

theorem t10_denominator_pos (d : SimplexData) :
    0 < t10Denominator d := by
  unfold t10Denominator D H
  have hg := d.gapsPos
  have hu := d.UPos
  positivity

/-- Exact fraction arithmetic retaining the unreduced source numerator
and denominator, so no summary total or decimal is involved. -/
structure ExactFraction where
  num : ℤ
  den : Nat
  denPos : 0 < den

def value (p : ExactFraction) : ℚ := (p.num : ℚ) / p.den

def zero : ExactFraction := ⟨0, 1, by norm_num⟩

def add (a b : ExactFraction) : ExactFraction :=
  ⟨a.num * b.den + b.num * a.den,
    a.den * b.den, Nat.mul_pos a.denPos b.denPos⟩

theorem add_value (a b : ExactFraction) :
    value (add a b) = value a + value b := by
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt a.denPos)
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt b.denPos)
  unfold value add
  push_cast
  field_simp [ha, hb]
  ring

def sumFractions : List ExactFraction → ExactFraction
  | [] => zero
  | p :: ps => add p (sumFractions ps)

theorem sumFractions_value (ps : List ExactFraction) :
    value (sumFractions ps) = (ps.map value).sum := by
  induction ps with
  | nil => simp [sumFractions, zero, value]
  | cons p ps ih => simp [sumFractions, add_value, ih]

def t10 (d : SimplexData) : ExactFraction :=
  ⟨t10Numerator d, t10Denominator d, t10_denominator_pos d⟩

def transverse (d : SimplexData) (j : Fin 10) : ExactFraction :=
  ⟨curvatureNumerator d.gaps (d.deviations j) d.L,
    curvatureDenominator d.gaps d.U (d.maxima j),
    curvature_denominator_pos d.gapsPos d.UPos (d.maximaPos j)⟩

def transverseTerms (d : SimplexData) : List ExactFraction :=
  List.ofFn (fun j : Fin 10 => transverse d j)

/-- Assemble exact T10 and all ten exact Qj fractions before rounding. -/
def total (d : SimplexData) : ExactFraction :=
  add (t10 d) (sumFractions (transverseTerms d))

theorem total_value (d : SimplexData) :
    value (total d) = value (t10 d) +
      ((transverseTerms d).map value).sum := by
  simp [total, add_value, sumFractions_value]

/-- This is the exact producer formula for each transverse summand. -/
theorem transverse_value (d : SimplexData) (j : Fin 10) :
    value (transverse d j) =
      ((d.L : ℚ) / d.U)^10 *
        ((signedMomentNumerator d.gaps (d.deviations j) : ℚ) /
          (220 * (gapTotal d.gaps : ℚ) * (d.maxima j : ℚ)^2)) := by
  exact curvature_summand_fraction d.gaps (d.deviations j)
    d.L d.U (d.maxima j) d.gapsPos d.UPos (d.maximaPos j)

/-- One Q80 floor of the assembled exact fraction, followed by one Q96
floor of the positive Jensen product, gives a directed lower bound for
`J_T * (1 + T10 + Q_T)`. This is conditional on the two integer floor
checks and makes no claim that a stored row satisfies them. -/
theorem total_directed_floor_semantics
    (d : SimplexData) (tFloor raw : Nat)
    (hT : curvatureFloorQ80 (total d).num (total d).den tFloor)
    (hRaw : jensenProductFloorQ96 d.jensenNum d.jensenDen
      tFloor raw) :
    (raw : ℚ) / q96 ≤
      ((d.jensenNum : ℚ) / d.jensenDen) * (1 + value (total d)) := by
  have ht : (tFloor : ℚ) / q80 ≤ value (total d) := by
    simpa [value] using (curvature_floor_Q80_semantics hT).1
  have hr : (raw : ℚ) / q96 ≤
      ((d.jensenNum : ℚ) / d.jensenDen) *
        (1 + (tFloor : ℚ) / q80) := by
    simpa [jensen_product_fraction d.jensenNum d.jensenDen
      tFloor d.jensenDenPos] using
      (jensen_product_floor_Q96_semantics hRaw).1
  calc
    (raw : ℚ) / q96 ≤
        ((d.jensenNum : ℚ) / d.jensenDen) *
          (1 + (tFloor : ℚ) / q80) := hr
    _ ≤ ((d.jensenNum : ℚ) / d.jensenDen) *
        (1 + value (total d)) := by
      apply mul_le_mul_of_nonneg_left (by linarith [ht])
      positivity

end ImbalancedChen.P2Winner9CurvatureFullExactAssembly
