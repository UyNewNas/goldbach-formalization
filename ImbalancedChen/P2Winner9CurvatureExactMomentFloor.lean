import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The curvature note's (D2) signed second-moment numerator is reconstructed
from nine primitive integer vertex gaps and signed affine deviations. For
one of the ten factors, the exact curvature summand in (C) has numerator
`L^10 * N_j` and denominator `B^10 * 220 * G * v_j^2`. These are derived
from the source formula, not copied from a result summary or witness floor.

The two floor lemmas state the directed rational meaning of the exact Q80
curvature-summand floor and the subsequent Q96 Jensen-product floor. They
do not claim that any actual row supplies the required exact inputs or
passes the inequalities. The full T10-plus-ten-summand assembly, physical
cap, analytic enclosure, and 11,026-row checks remain separate.
-/

namespace ImbalancedChen.P2Winner9CurvatureExactMomentFloor

def q80 : Nat := 1208925819614629174706176
def q96 : Nat := 79228162514264337593543950336

def gapTotal (g : Fin 9 → Nat) : Nat := ∑ i, g i

/-- `G(s²+q)+2sp+2w` from the signed Dirichlet-mixture identity (D2).
Signed deviations are essential; a nonnegative-only surrogate is invalid. -/
def signedMomentNumerator (g : Fin 9 → Nat) (b : Fin 9 → ℤ) : ℤ :=
  let s : ℤ := ∑ i, b i
  let q : ℤ := ∑ i, (b i)^2
  let p : ℤ := ∑ i, (g i : ℤ) * b i
  let w : ℤ := ∑ i, (g i : ℤ) * (b i)^2
  (gapTotal g : ℤ) * (s^2 + q) + 2 * s * p + 2 * w

/-- One exact factor contribution to `Q_T`; `B/L` is the vertex maximum
of P and `v/L` is the factor's common deviation maximum. -/
def curvatureNumerator (g : Fin 9 → Nat) (b : Fin 9 → ℤ)
    (L : Nat) : ℤ := (L : ℤ)^10 * signedMomentNumerator g b

def curvatureDenominator (g : Fin 9 → Nat)
    (B v : Nat) : Nat := B^10 * 220 * gapTotal g * v^2

theorem curvature_denominator_pos {g : Fin 9 → Nat} {B v : Nat}
    (hG : 0 < gapTotal g) (hB : 0 < B) (hv : 0 < v) :
    0 < curvatureDenominator g B v := by
  unfold curvatureDenominator
  positivity

/-- Exact rational reconstruction of the single source summand
`(L/B)^10 * N_j/(220 G v_j²)`. -/
theorem curvature_summand_fraction
    (g : Fin 9 → Nat) (b : Fin 9 → ℤ) (L B v : Nat)
    (hG : 0 < gapTotal g) (hB : 0 < B) (hv : 0 < v) :
    (curvatureNumerator g b L : ℚ) /
        (curvatureDenominator g B v : ℚ) =
      ((L : ℚ) / B)^10 *
        ((signedMomentNumerator g b : ℚ) /
          (220 * (gapTotal g : ℚ) * (v : ℚ)^2)) := by
  have hGq : (gapTotal g : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hG)
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv)
  unfold curvatureNumerator curvatureDenominator
  push_cast
  field_simp [hGq, hBq, hvq]
  ring

/-- A directed Q80 floor condition for the exact reconstructed summand.
The signed numerator is retained as an integer until nonnegativity is
established from the source's squared-moment identity. -/
def curvatureFloorQ80 (num : ℤ) (den : Nat) (floor : ℤ) : Prop :=
  0 < den ∧ floor * den ≤ q80 * num ∧
    q80 * num < (floor + 1) * den

theorem curvature_floor_Q80_semantics {num : ℤ} {den : Nat} {floor : ℤ}
    (h : curvatureFloorQ80 num den floor) :
    (floor : ℚ) / q80 ≤ (num : ℚ) / den ∧
    (num : ℚ) / den < ((floor + 1 : ℤ) : ℚ) / q80 := by
  rcases h with ⟨hden, hlo, hhi⟩
  have hdq : (0 : ℚ) < den := by exact_mod_cast hden
  have hq : (0 : ℚ) < q80 := by norm_num [q80]
  constructor
  · apply (div_le_div_iff₀ hq hdq).2
    exact_mod_cast hlo
  · apply (div_lt_div_iff₀ hdq hq).2
    exact_mod_cast hhi

/-- The producer's single downward Q96 rounding after multiplying exact
Jensen `jNum/jDen` by `1 + tFloor/Q80`. -/
def jensenProductNumerator (jNum tFloor : Nat) : Nat :=
  jNum * (q80 + tFloor)

def jensenProductDenominator (jDen : Nat) : Nat := jDen * q80

theorem jensen_product_fraction (jNum jDen tFloor : Nat)
    (hj : 0 < jDen) :
    (jensenProductNumerator jNum tFloor : ℚ) /
        jensenProductDenominator jDen =
      ((jNum : ℚ) / jDen) * (1 + (tFloor : ℚ) / q80) := by
  have hdq : (jDen : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hq : (q80 : ℚ) ≠ 0 := by norm_num [q80]
  unfold jensenProductNumerator jensenProductDenominator
  push_cast
  field_simp [hdq, hq]
  ring

def jensenProductFloorQ96 (jNum jDen tFloor raw : Nat) : Prop :=
  0 < jDen ∧
  raw * jensenProductDenominator jDen ≤
    q96 * jensenProductNumerator jNum tFloor ∧
  q96 * jensenProductNumerator jNum tFloor <
    (raw + 1) * jensenProductDenominator jDen

theorem jensen_product_floor_Q96_semantics
    {jNum jDen tFloor raw : Nat}
    (h : jensenProductFloorQ96 jNum jDen tFloor raw) :
    (raw : ℚ) / q96 ≤
      (jensenProductNumerator jNum tFloor : ℚ) /
        jensenProductDenominator jDen ∧
    (jensenProductNumerator jNum tFloor : ℚ) /
        jensenProductDenominator jDen < ((raw + 1 : Nat) : ℚ) / q96 := by
  rcases h with ⟨hj, hlo, hhi⟩
  have hdq : (0 : ℚ) < (jensenProductDenominator jDen : ℚ) := by
    exact_mod_cast (show 0 < jensenProductDenominator jDen by
      unfold jensenProductDenominator q80
      positivity)
  have hq : (0 : ℚ) < q96 := by norm_num [q96]
  constructor
  · apply (div_le_div_iff₀ hq hdq).2
    exact_mod_cast hlo
  · apply (div_lt_div_iff₀ hdq hq).2
    exact_mod_cast hhi

end ImbalancedChen.P2Winner9CurvatureExactMomentFloor
