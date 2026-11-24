import ImbalancedChen.P2Winner9FastExactAssembly
import ImbalancedChen.P2Winner9Row21SourceBridge

/-! Exact directed rounding of the original row21 T10 plus signed Q6 correction. -/

namespace ImbalancedChen.P2Winner9Row21Q6Arithmetic

open P2Winner9Row21SourceBridge (row21)
open P2Winner9Row21Arithmetic (reconstructedJensen)
open P2Winner9CurvatureFullExactAssembly (value)
open P2Winner9CurvatureExactMomentFloor
open P2Winner9FastExactAssembly (totalFast total_eq)

def observedMixedTotalQ80 : ℕ := 18932817790080969734485
def observedMixedRawQ96 : ℕ := 33553775924834770601

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem fast_total_rounding :
    curvatureFloorQ80 (totalFast row21).num (totalFast row21).den observedMixedTotalQ80 := by
  unfold curvatureFloorQ80
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem mixed_jensen_rounding :
    jensenProductFloorQ96 row21.jensenNum row21.jensenDen
      observedMixedTotalQ80 observedMixedRawQ96 := by
  change jensenProductFloorQ96 reconstructedJensen.num.toNat reconstructedJensen.den
    observedMixedTotalQ80 observedMixedRawQ96
  unfold jensenProductFloorQ96
  decide +kernel

theorem row21_original_Q6_rounding :
    curvatureFloorQ80 (P2Winner9MixedDegreeSixExactAssembly.total row21).num
      (P2Winner9MixedDegreeSixExactAssembly.total row21).den observedMixedTotalQ80 ∧
    jensenProductFloorQ96 row21.jensenNum row21.jensenDen
      observedMixedTotalQ80 observedMixedRawQ96 := by
  rw [← total_eq]
  exact ⟨fast_total_rounding, mixed_jensen_rounding⟩

theorem row21_raw_Q6_arithmetic_lower :
    (observedMixedRawQ96 : ℚ) / q96 ≤
      ((row21.jensenNum : ℚ) / row21.jensenDen) *
        (1 + value (P2Winner9MixedDegreeSixExactAssembly.total row21)) :=
  P2Winner9MixedDegreeSixExactAssembly.mixed_directed_floor_semantics
    row21 observedMixedTotalQ80 observedMixedRawQ96
    row21_original_Q6_rounding.1 row21_original_Q6_rounding.2

end ImbalancedChen.P2Winner9Row21Q6Arithmetic
