import ImbalancedChen.P6OriginalLiteralMeshPrices
import ImbalancedChen.CurrentChenP5U9MeshDiscretization

namespace ImbalancedChen.P6OriginalNinthMeshPrice

noncomputable section
open MeasureTheory Set
open P6OriginalLiteralMeshPrices P6OriginalLiteralLogIntegralPrices

theorem actual_ninth_integral :
    currentChenUpsilon9HarmonicIntegral ≤ 4816743300211123/10000000000000000 := by
  rw [currentChenUpsilon9HarmonicIntegral_eq_logIntegral, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (19/125:ℝ) ≤ 59/250)]
  exact ninth_literal_integral

/-- The actual directed upper sum of the named mesh, in the appropriation
at K0. The proof uses its published error rate and the real log primitive. -/
theorem ninth_mesh_passes :
    P2U9DirectedRationalCover.rationalUpper 32 1000000000000000000 ≤
      (3937512077512215599969887 / 1208925819614629174706176 : ℚ)/(67619/10000) := by
  have hm := (P5U9MeshDiscretization.actual_integral_errors_le_rate 32 1000000000000000000
    (by decide)).2
  have habs := (abs_le.mp hm).2
  have hs : 4816743300211123/10000000000000000 +
      P5U9MeshDiscretization.enclosureRate 32 1000000000000000000 ≤
      (3937512077512215599969887/1208925819614629174706176 : ℚ)/(67619/10000) := by
    change _ + rate9 ≤ price9
    exact ninth_budget.le
  have hh : (P2U9DirectedRationalCover.rationalUpper 32 1000000000000000000 : ℝ) ≤
      (4816743300211123/10000000000000000 : ℝ) +
      (P5U9MeshDiscretization.enclosureRate 32 1000000000000000000 : ℝ) := by
    linarith only [habs, actual_ninth_integral]
  apply (Rat.cast_le (K:=ℝ)).mp
  have hsR := (Rat.cast_le (K:=ℝ)).mpr hs
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_add] at hsR ⊢
  exact hh.trans hsR

end
end ImbalancedChen.P6OriginalNinthMeshPrice
