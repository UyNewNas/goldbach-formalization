import ImbalancedChen.P2Winner9FastExactAssembly

/-! Exact rational evaluation with normalization at each addition. -/

namespace ImbalancedChen.P2Winner9ReducedExactAssembly

open P2Winner9CurvatureFullExactAssembly (SimplexData ExactFraction value sumFractions_value add_value)
open P2Winner9CurvatureExactMomentFloor (q80 curvatureFloorQ80)
open P2Winner9FastExactAssembly (t10Fast mixedTermFast q6Fast t10_eq q6_eq)
open P2Winner9MixedDegreeSixExactAssembly (total)

/-- Rational addition cancels common factors in the original 70 denominators. -/
def totalValueReduced (d : SimplexData) : ℚ :=
  value (t10Fast d) +
    ((List.ofFn (fun j : Fin 10 => List.ofFn (fun k : Fin 7 => mixedTermFast d j k))).flatten.map
      value).sum

theorem totalValueReduced_eq (d : SimplexData) : totalValueReduced d = value (total d) := by
  rw [total, add_value, ← t10_eq, ← q6_eq, q6Fast, sumFractions_value]
  rfl

/-- Both normalized Q80 grid inequalities imply the original integer test. -/
theorem Q80_of_value (p : ExactFraction) (n : ℤ)
    (hlo : (n : ℚ) / q80 ≤ value p) (hhi : value p < ((n + 1 : ℤ) : ℚ) / q80) :
    curvatureFloorQ80 p.num p.den n := by
  have hd : (0 : ℚ) < p.den := by exact_mod_cast p.denPos
  have hq : (0 : ℚ) < q80 := by norm_num [q80]
  refine ⟨p.denPos, ?_, ?_⟩
  · rw [mul_comm (q80 : ℤ) p.num]
    exact_mod_cast (div_le_div_iff₀ hq hd).mp hlo
  · rw [mul_comm (q80 : ℤ) p.num]
    exact_mod_cast (div_lt_div_iff₀ hd hq).mp hhi

end ImbalancedChen.P2Winner9ReducedExactAssembly
