import ImbalancedChen.P2Winner9Row21SourceBridge
import ImbalancedChen.P2Winner9Row22Arithmetic

/-! Exact rational first moments for the two selected Winner9 rows. -/

namespace ImbalancedChen.P2Winner9SelectedRawMeans

open scoped BigOperators
open P2Winner9SelectedRowEdgeGeometry (row21 row22 row22Volume)
open P2Winner9Row22Arithmetic (RationalVertices rawGap rawP rawFactor)
open P2Winner9CurvatureFullExactAssembly (SimplexData)

def gapIntegral (v : RationalVertices) : ℚ :=
  (∑ i : Fin 9, rawGap v i) / ((9 : ℕ).factorial : ℚ)

/-- The degree-two affine expression uses twice the diagonal moment. -/
def weightedAffineIntegral (v : RationalVertices) (f : Fin 9 → ℚ) : ℚ :=
  ((∑ i : Fin 9, rawGap v i) * (∑ i : Fin 9, f i) +
    ∑ i : Fin 9, rawGap v i * f i) / ((10 : ℕ).factorial : ℚ)

def row21Means (j : Fin 10) : ℚ := P2Winner9Row21RawVertexData.storedMeans[j.val]!

def storedJacobian (volume : ℚ) : ℚ := ((8 : ℕ).factorial : ℚ) * volume

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row21_exact_affine_moments :
    0 < gapIntegral row21 ∧
    weightedAffineIntegral row21 (rawP row21 row21Means) = gapIntegral row21 ∧
    ∀ j : Fin 10,
      weightedAffineIntegral row21 (fun i => rawFactor row21 i j) =
        row21Means j * gapIntegral row21 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row22_exact_affine_moments :
    0 < gapIntegral row22 ∧
    weightedAffineIntegral row22 (rawP row22 P2Winner9Row22Arithmetic.means) =
      gapIntegral row22 ∧
    ∀ j : Fin 10,
      weightedAffineIntegral row22 (fun i => rawFactor row22 i j) =
        P2Winner9Row22Arithmetic.means j * gapIntegral row22 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row21_exact_jensen :
    let d : SimplexData := P2Winner9Row21SourceBridge.row21
    (d.jensenNum : ℚ) / d.jensenDen =
      4 * storedJacobian P2Winner9Row21RawVertexData.physicalVolume * gapIntegral row21 /
        ∏ j : Fin 10, row21Means j := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row22_exact_jensen :
    let d : SimplexData := P2Winner9Row22Arithmetic.data
    (d.jensenNum : ℚ) / d.jensenDen =
      4 * storedJacobian row22Volume * gapIntegral row22 /
        ∏ j : Fin 10, P2Winner9Row22Arithmetic.means j := by
  decide +kernel

end ImbalancedChen.P2Winner9SelectedRawMeans
