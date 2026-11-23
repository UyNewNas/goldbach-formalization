import ImbalancedChen.P6OriginalLiteralLogIntegralPrices

/-! The original upper-cover error formulas at a fixed finite mesh, and
the strict budgets for the four actual one-dimensional integrals appearing
in the numerical appendix. -/
namespace ImbalancedChen.P6OriginalLiteralMeshPrices

open P6OriginalLiteralLogIntegralPrices

def M : ℚ := 1000000000000000000
def rate7 : ℚ :=
  let width : ℚ := 1/3-59/250
  let dt : ℚ := width/M
  let du : ℚ := ((1-59/250)/2-59/250)/M
  125*(width*(3*dt+4*du))+(40000*(dt+du)+125*(4*(7/66)^(2*32+1)))
def rate8 : ℚ :=
  let a := (417/5000:ℚ)
  let b := (1/3:ℚ)
  let top := (1/2:ℚ)
  (2000000*(top-a)*((b-a)*(top-b))+1000*(b-a)*(1-b-a))/M
def rate9 : ℚ := (189/250)/M+(672/125)*(47/106)^(2*32+1)
def price7 : ℚ := (1672464594622060236183097/1208925819614629174706176)/(67619/10000)
def price8 : ℚ := (4904703865205402441361491/1208925819614629174706176)/(67619/10000)
def price9 : ℚ := (3937512077512215599969887/1208925819614629174706176)/(67619/10000)

/-- The three archived midpoint upper numerators have their common
dyadic denominator 2^80, and are divided by the same original K0. -/
theorem midpoint_endpoints_exact :
    (67619/10000)*price7 = (1672464594622060236183097:ℚ)/2^80 ∧
    (67619/10000)*price8 = (4904703865205402441361491:ℚ)/2^80 ∧
    (67619/10000)*price9 = (3937512077512215599969887:ℚ)/2^80 := by decide +kernel

theorem seventh_budget :
    (2042785889856317+3133582170107)/10000000000000000+rate7 < price7 := by decide +kernel

theorem eighth_budget :
    5999905266705567/10000000000000000+rate8 < price8 := by decide +kernel

theorem ninth_budget :
    4816743300211123/10000000000000000+rate9 < price9 := by decide +kernel

/-- These are strict prices for the real integrals and all three exact
upper-cover discretization errors, before invoking the original cover APIs. -/
theorem literal_three_mesh_budgets :
    ((∫ t in (59/250:ℝ)..(1/3:ℝ), Real.log ((1-2*t)/t)/(t*(1-t))) +
      (∫ t in (2:ℝ)..(132/59:ℝ), (Real.log (t-1)/t)*Real.log ((1-59/250)/((59/250)*(t+1)))) +
        (rate7:ℝ) < (price7:ℝ)) ∧
    ((∫ t in (417/5000:ℝ)..(1/3:ℝ), Real.log (2-3*t)/(t*(1-t))) + (rate8:ℝ) < (price8:ℝ)) ∧
    ((∫ t in (19/125:ℝ)..(59/250:ℝ), Real.log ((1-t-59/250)/(59/250))/(t*(1-t))) +
      (rate9:ℝ) < (price9:ℝ)) := by
  have h7 := (Rat.cast_lt (K:=ℝ)).mpr seventh_budget
  have h8 := (Rat.cast_lt (K:=ℝ)).mpr eighth_budget
  have h9 := (Rat.cast_lt (K:=ℝ)).mpr ninth_budget
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] at h7 h8 h9
  have e8 := eighth_literal_integral
  simp only [div_one] at e8
  exact ⟨by linarith only [seventhPrime_literal_integral,correction_literal_integral,h7],
    by linarith only [e8,h8],by linarith only [ninth_literal_integral,h9]⟩

end ImbalancedChen.P6OriginalLiteralMeshPrices
