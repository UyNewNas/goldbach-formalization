import ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
import ImbalancedChen.P2Winner9CurvatureFullExactAssembly

/-! Reconstruct the original row22 integer scale and signed data from its ordered vertices. -/

namespace ImbalancedChen.P2Winner9Row22Arithmetic

open scoped BigOperators
open P2Winner9SelectedRowEdgeGeometry (row22 row22Volume)
open P2Winner9CurvatureFullExactAssembly (SimplexData)

abbrev RationalVertices := Fin 9 → Fin 8 → ℚ

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def rawR (v : RationalVertices) (i : Fin 9) : ℚ :=
  (1 + v i 0 + v i 3) / 2

def rawM (v : RationalVertices) (i : Fin 9) : ℚ :=
  (1 + v i 1 + v i 3 + v i 7) / 2 - 1 / 1000000

def rawSum (v : RationalVertices) (i : Fin 9) : ℚ := ∑ k : Fin 8, v i k

def rawGap (v : RationalVertices) (i : Fin 9) : ℚ := rawM v i - rawR v i

def rawFactor (v : RationalVertices) (i : Fin 9) (j : Fin 10) : ℚ :=
  Fin.cases (rawR v i - rawSum v i)
    (Fin.cases (rawM v i - rawSum v i) (fun k : Fin 8 => v i k)) j

def rawP (v : RationalVertices) (means : Fin 10 → ℚ) (i : Fin 9) : ℚ :=
  (∑ j : Fin 10, rawFactor v i j / means j) / 10

def rawY (v : RationalVertices) (means : Fin 10 → ℚ) (U : ℚ)
    (i : Fin 9) : ℚ := 1 - rawP v means i / U

def rawDeviation (v : RationalVertices) (means : Fin 10 → ℚ)
    (i : Fin 9) (j : Fin 10) : ℚ :=
  rawFactor v i j / means j - rawP v means i

/-- The source's `ints` construction on the nine actual gap values. -/
def gapDen : Nat :=
  (List.ofFn (fun i : Fin 9 => (rawGap row22 i).den)).foldl Nat.lcm 1

def g (i : Fin 9) : Nat :=
  (rawGap row22 i).num.toNat * (gapDen / (rawGap row22 i).den)

def G : Nat := ∑ i : Fin 9, g i

def columnDen (j : Fin 10) : Nat :=
  (List.ofFn (fun i : Fin 9 => (rawFactor row22 i j).den)).foldl Nat.lcm 1

def ellInt (i : Fin 9) (j : Fin 10) : Nat :=
  (rawFactor row22 i j).num.toNat * (columnDen j / (rawFactor row22 i j).den)

def meanNum (j : Fin 10) : Nat :=
  G * (∑ i : Fin 9, ellInt i j) + ∑ i : Fin 9, g i * ellInt i j

def computedMeans (j : Fin 10) : ℚ := (meanNum j : ℚ) / (10 * G * columnDen j)

/-- Literal row22 `gap_weighted_means` values; data transcription only. -/
def means : Fin 10 → ℚ :=
  ![((577637705887096607 : ℚ) / 11578849671480000000), ((2247037326827454443 : ℚ) / 38596165571600000000), ((234767748712392229153 : ℚ) / 2084192940866400000000), ((27938293278857716721 : ℚ) / 260524117608300000000), ((108089626526730803819 : ℚ) / 1042096470433200000000), ((18072940253656771157 : ℚ) / 297741848695200000000), ((901094636466229069 : ℚ) / 15438466228640000000), ((1929335299193979307 : ℚ) / 42534549813600000000), ((882788654227555807 : ℚ) / 33082427632800000000), ((5110669782824725501 : ℚ) / 231576993429600000000)]

def L : Nat := (List.ofFn (fun j : Fin 10 => meanNum j)).foldl Nat.lcm 1

def pv (i : Fin 9) : Nat :=
  G * ∑ j : Fin 10, ellInt i j * (L / meanNum j)

def U : Nat := (List.ofFn (fun i : Fin 9 => pv i)).foldl max 0

def y (i : Fin 9) : Nat := U - pv i

def ai (i : Fin 9) (j : Fin 10) : Nat :=
  10 * G * ellInt i j * (L / meanNum j)

/-- The transverse numerator stays in ℤ; there is no Nat truncation. -/
def b (j : Fin 10) (i : Fin 9) : ℤ := (ai i j : ℤ) - pv i

def vmax (j : Fin 10) : Nat :=
  max U ((List.ofFn (fun i : Fin 9 => ai i j)).foldl max 0)

def reconstructedJensen : ℚ :=
  4 * row22Volume * ((G : ℚ) / (9 * gapDen)) / ∏ j : Fin 10, computedMeans j

/-- Typed primitive data for the original row22 witness. -/
def data : SimplexData := {
  gaps := g
  y := y
  L := L
  U := U
  deviations := b
  maxima := vmax
  jensenNum := reconstructedJensen.num.toNat
  jensenDen := reconstructedJensen.den
  gapsPos := by decide +kernel
  LPos := by decide +kernel
  UPos := by decide +kernel
  maximaPos := by decide +kernel
  jensenDenPos := by decide +kernel
}

def upper : ℚ := (data.U : ℚ) / data.L

/-- The exact reconstructed means agree with the original stored values. -/
theorem means_match_source : ∀ j : Fin 10, computedMeans j = means j := by
  decide +kernel

def VertexNormalization (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (gapDen : Nat) : Prop :=
  0 < gapDen ∧
    ∀ i : Fin 9,
      rawGap v i = (d.gaps i : ℚ) / gapDen ∧
      rawY v means upper i = (d.y i : ℚ) / d.U ∧
      ∀ j : Fin 10, rawDeviation v means i j = (d.deviations j i : ℚ) / d.L

theorem row22_vertex_normalization :
    VertexNormalization row22 means upper data gapDen := by
  unfold VertexNormalization
  decide +kernel

end ImbalancedChen.P2Winner9Row22Arithmetic
