import ImbalancedChen.P2Winner9GroupedQ6
import ImbalancedChen.P2Winner9ReducedExactAssembly

/-! Integer dyadic brackets for directed Q80 rounding of the exact
Winner9 correction. Ambiguous brackets use exact rational evaluation. -/

namespace ImbalancedChen.P2Winner9DyadicQ6

open P2Winner9CurvatureFullExactAssembly (SimplexData ExactFraction value add_value sumFractions_value)
open P2Winner9CurvatureExactMomentFloor (q80 curvatureFloorQ80 curvature_floor_Q80_semantics)
open P2Winner9FastExactAssembly (t10Fast total_eq)
open P2Winner9GroupedQ6 (factorMixedFraction q6Grouped totalGrouped total_grouped_eq)
open P2Winner9MixedDegreeSixExactAssembly (total)
open P2Winner9ReducedExactAssembly (totalValueReduced totalValueReduced_eq Q80_of_value)

private def scale : ℕ := 2^144

private theorem scale_pos : 0 < scale := by decide +kernel

private theorem q80_pos : 0 < q80 := by decide +kernel

private def termLower (p : ExactFraction) : ℤ :=
  ((scale : ℤ) * p.num) / (p.den : ℤ)

private theorem term_bounds (p : ExactFraction) :
    (termLower p : ℚ) ≤ (scale : ℚ) * value p ∧
      (scale : ℚ) * value p < (termLower p : ℚ) + 1 := by
  have hd : (0 : ℤ) < (p.den : ℤ) := by exact_mod_cast p.denPos
  have hq : (0 : ℚ) < (p.den : ℚ) := by exact_mod_cast p.denPos
  have hlo : termLower p * (p.den : ℤ) ≤ (scale : ℤ) * p.num :=
    Int.ediv_mul_le _ hd.ne'
  have hhi : (scale : ℤ) * p.num < (termLower p + 1) * (p.den : ℤ) :=
    (Int.ediv_lt_iff_lt_mul hd).mp (by
      change termLower p < termLower p + 1
      omega)
  simp only [value, ← mul_div_assoc]
  constructor
  · apply (le_div_iff₀ hq).mpr
    exact_mod_cast hlo
  · apply (div_lt_iff₀ hq).mpr
    exact_mod_cast hhi

/-- Sum signed lower grid ordinates for the common term and the ten
factor contributions. -/
def lower (d : SimplexData) : ℤ :=
  termLower (t10Fast d) + ∑ j : Fin 10, termLower (factorMixedFraction d j)

private theorem grouped_value_sum (d : SimplexData) :
    value (total d) = value (t10Fast d) + ∑ j : Fin 10, value (factorMixedFraction d j) := by
  rw [← total_eq, ← total_grouped_eq, totalGrouped, add_value, q6Grouped,
    sumFractions_value]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem dyadic_bounds (d : SimplexData) :
    (lower d : ℚ) ≤ (scale : ℚ) * value (total d) ∧
      (scale : ℚ) * value (total d) < (lower d : ℚ) + 11 := by
  rw [grouped_value_sum, mul_add, Finset.mul_sum, lower]
  push_cast
  constructor
  · exact add_le_add (term_bounds (t10Fast d)).1
      (Finset.sum_le_sum fun j _ => (term_bounds (factorMixedFraction d j)).1)
  · have hsum : (∑ j : Fin 10, (scale : ℚ) * value (factorMixedFraction d j)) <
        ∑ j : Fin 10, ((termLower (factorMixedFraction d j) : ℚ) + 1) := by
      apply Finset.sum_lt_sum
      · intro j _
        exact (term_bounds (factorMixedFraction d j)).2.le
      · exact ⟨0, Finset.mem_univ _, (term_bounds (factorMixedFraction d 0)).2⟩
    have h := add_lt_add (term_bounds (t10Fast d)).2 hsum
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    refine h.trans_le ?_
    norm_num
    linarith

private def bracketAt (n ell : ℤ) : Prop :=
  n * (scale : ℤ) ≤ (q80 : ℤ) * ell ∧
    (q80 : ℤ) * (ell + 11) ≤ (n + 1) * (scale : ℤ)

private instance (n ell : ℤ) : Decidable (bracketAt n ell) := by
  unfold bracketAt
  infer_instance

/-- The dyadic bracket lies within the claimed Q80 grid interval. -/
def Q80Bracket (d : SimplexData) (n : ℤ) : Prop := bracketAt n (lower d)

instance (d : SimplexData) (n : ℤ) : Decidable (Q80Bracket d n) :=
  inferInstanceAs (Decidable (bracketAt n (lower d)))

theorem Q80Bracket.bounds (d : SimplexData) (n : ℤ) (h : Q80Bracket d n) :
    (n : ℚ) / q80 ≤ value (total d) ∧ value (total d) < ((n + 1 : ℤ) : ℚ) / q80 := by
  have hq : (0 : ℚ) < q80 := by exact_mod_cast q80_pos
  have hs : (0 : ℚ) < scale := by exact_mod_cast scale_pos
  have hd := dyadic_bounds d
  unfold Q80Bracket bracketAt at h
  have hlo : (n : ℚ) * scale ≤ (q80 : ℚ) * (lower d : ℚ) := by exact_mod_cast h.1
  have hhi : (q80 : ℚ) * ((lower d : ℚ) + 11) ≤ ((n : ℚ) + 1) * scale := by exact_mod_cast h.2
  constructor
  · calc
      (n : ℚ) / q80 ≤ (lower d : ℚ) / scale :=
        (div_le_div_iff₀ hq hs).mpr (by simpa only [mul_comm] using hlo)
      _ ≤ value (total d) := (div_le_iff₀ hs).mpr (by simpa only [mul_comm] using hd.1)
  · calc
      value (total d) < ((lower d : ℚ) + 11) / scale :=
        (lt_div_iff₀ hs).mpr (by simpa only [mul_comm] using hd.2)
      _ ≤ ((n + 1 : ℤ) : ℚ) / q80 := (div_le_div_iff₀ hs hq).mpr (by
        push_cast
        simpa only [mul_comm] using hhi)

theorem Q80Bracket.sound (d : SimplexData) (n : ℤ) (h : Q80Bracket d n) :
    curvatureFloorQ80 (total d).num (total d).den n := by
  obtain ⟨hl, hu⟩ := h.bounds d n
  exact Q80_of_value _ _ hl hu

private def Q80Exact (d : SimplexData) (n : ℤ) : Prop :=
  Int.floor ((q80 : ℚ) * totalValueReduced d) = n

private instance (d : SimplexData) (n : ℤ) : Decidable (Q80Exact d n) := by
  unfold Q80Exact
  infer_instance

/-- Test the integer bracket first, with exact rational evaluation at
grid boundaries that the bracket cannot decide. -/
def Q80Check (d : SimplexData) (n : ℤ) : Prop := Q80Bracket d n ∨ Q80Exact d n

instance (d : SimplexData) (n : ℤ) : Decidable (Q80Check d n) :=
  inferInstanceAs (Decidable (Q80Bracket d n ∨ Q80Exact d n))

theorem Q80Check.iff_source (d : SimplexData) (n : ℤ) :
    Q80Check d n ↔ curvatureFloorQ80 (total d).num (total d).den n := by
  have hq : (0 : ℚ) < q80 := by exact_mod_cast q80_pos
  constructor
  · intro h
    rcases h with h | h
    · exact Q80Bracket.sound d n h
    · unfold Q80Exact at h
      rw [totalValueReduced_eq] at h
      have hh := Int.floor_eq_iff.mp h
      apply Q80_of_value
      · exact (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hh.1)
      · exact (lt_div_iff₀ hq).mpr (by simpa only [Int.cast_add, Int.cast_one, mul_comm] using hh.2)
  · intro h
    apply Or.inr
    unfold Q80Exact
    rw [totalValueReduced_eq, Int.floor_eq_iff]
    have hh := curvature_floor_Q80_semantics h
    change (n : ℚ) / q80 ≤ value (total d) ∧
      value (total d) < ((n + 1 : ℤ) : ℚ) / q80 at hh
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hq).mp hh.1
    · simpa only [Int.cast_add, Int.cast_one, mul_comm] using (lt_div_iff₀ hq).mp hh.2

end ImbalancedChen.P2Winner9DyadicQ6
