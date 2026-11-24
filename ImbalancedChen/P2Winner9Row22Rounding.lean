import ImbalancedChen.P2Winner9FastExactAssembly
import ImbalancedChen.P2Winner9Row22Arithmetic

/-! Original row22 curvature and mixed directed floors on its own typed row. -/

namespace ImbalancedChen.P2Winner9Row22Rounding

open P2Winner9Row22Arithmetic (data reconstructedJensen)
open P2Winner9CurvatureFullExactAssembly (ExactFraction add sumFractions transverseTerms value)
open P2Winner9CurvatureExactMomentFloor
open P2Winner9FastExactAssembly (t10Fast t10_eq totalFast total_eq)

def observedCurvatureTotalQ80 : ℕ := 15389547820376111661547
def observedCurvatureRawQ96 : ℕ := 6447903780770652011
def observedMixedTotalQ80 : ℕ := 18300039665022900361522
def observedMixedRawQ96 : ℕ := 6463231997558714529

private def curvatureTotalFast : ExactFraction :=
  add (t10Fast data) (sumFractions (transverseTerms data))

private theorem curvature_total_eq :
    curvatureTotalFast = P2Winner9CurvatureFullExactAssembly.total data := by
  simp only [curvatureTotalFast, P2Winner9CurvatureFullExactAssembly.total, t10_eq]

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem curvature_fast_rounding :
    curvatureFloorQ80 curvatureTotalFast.num curvatureTotalFast.den observedCurvatureTotalQ80 := by
  unfold curvatureFloorQ80
  decide +kernel

private theorem curvature_jensen_rounding :
    jensenProductFloorQ96 data.jensenNum data.jensenDen
      observedCurvatureTotalQ80 observedCurvatureRawQ96 := by
  change jensenProductFloorQ96 reconstructedJensen.num.toNat reconstructedJensen.den
    observedCurvatureTotalQ80 observedCurvatureRawQ96
  unfold jensenProductFloorQ96
  decide +kernel

theorem row22_original_curvature_rounding :
    curvatureFloorQ80 (P2Winner9CurvatureFullExactAssembly.total data).num
      (P2Winner9CurvatureFullExactAssembly.total data).den observedCurvatureTotalQ80 ∧
    jensenProductFloorQ96 data.jensenNum data.jensenDen
      observedCurvatureTotalQ80 observedCurvatureRawQ96 := by
  rw [← curvature_total_eq]
  exact ⟨curvature_fast_rounding, curvature_jensen_rounding⟩

private theorem mixed_fast_rounding :
    curvatureFloorQ80 (totalFast data).num (totalFast data).den observedMixedTotalQ80 := by
  unfold curvatureFloorQ80
  decide +kernel

private theorem mixed_jensen_rounding :
    jensenProductFloorQ96 data.jensenNum data.jensenDen
      observedMixedTotalQ80 observedMixedRawQ96 := by
  change jensenProductFloorQ96 reconstructedJensen.num.toNat reconstructedJensen.den
    observedMixedTotalQ80 observedMixedRawQ96
  unfold jensenProductFloorQ96
  decide +kernel

theorem row22_original_Q6_rounding :
    curvatureFloorQ80 (P2Winner9MixedDegreeSixExactAssembly.total data).num
      (P2Winner9MixedDegreeSixExactAssembly.total data).den observedMixedTotalQ80 ∧
    jensenProductFloorQ96 data.jensenNum data.jensenDen
      observedMixedTotalQ80 observedMixedRawQ96 := by
  rw [← total_eq]
  exact ⟨mixed_fast_rounding, mixed_jensen_rounding⟩

theorem row22_raw_Q6_arithmetic_lower :
    (observedMixedRawQ96 : ℚ) / q96 ≤
      ((data.jensenNum : ℚ) / data.jensenDen) *
        (1 + value (P2Winner9MixedDegreeSixExactAssembly.total data)) :=
  P2Winner9MixedDegreeSixExactAssembly.mixed_directed_floor_semantics
    data observedMixedTotalQ80 observedMixedRawQ96
    row22_original_Q6_rounding.1 row22_original_Q6_rounding.2

end ImbalancedChen.P2Winner9Row22Rounding
