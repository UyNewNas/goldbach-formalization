import ImbalancedChen.P2Winner9HomogeneousRecurrence
import ImbalancedChen.P2Winner9Row21RawVertexData
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

/-! Kernel replay of the row21 curvature arithmetic from the original
parent-nine witness data and the proved coefficient recurrence. -/

namespace ImbalancedChen.P2Winner9Row21Arithmetic

open P2Winner9Row21RawVertexData
open P2Winner9HomogeneousRecurrence (prefixCoefficients homogeneousFast homogeneousFast_eq_source)
open scoped BigOperators

def sumNat (f : Fin n → Nat) : Nat := (List.ofFn f).sum
def sumInt (f : Fin n → Int) : Int := (List.ofFn f).sum
def sumRat (f : Fin n → Rat) : Rat := (List.ofFn f).foldl (· + ·) 0
def prodRat (f : Fin n → Rat) : Rat := (List.ofFn f).foldl (· * ·) 1

def coord (i : Fin 9) (j : Nat) : ℚ :=
  (coords[i.val]!)[j]!

def S (i : Fin 9) : ℚ := sumRat (fun j : Fin 8 => coord i j.val)
def R (i : Fin 9) : ℚ := (1 + coord i 0 + coord i 3) / 2
def M (i : Fin 9) : ℚ :=
  (1 + coord i 1 + coord i 3 + coord i 7) / 2 - 1 / 1000000

def physicalGap (i : Fin 9) : ℚ := M i - R i

def physicalFactor (i : Fin 9) (j : Fin 10) : ℚ :=
  if j.val = 0 then R i - S i
  else if j.val = 1 then M i - S i
  else coord i (j.val - 2)

def storedGap (i : Fin 9) : ℚ :=
  (gapNum[i.val]! : ℚ) / gapDen[i.val]!

def storedFactor (i : Fin 9) (j : Fin 10) : ℚ :=
  ((factorNum[i.val]!)[j.val]! : ℚ) / (factorDen[i.val]!)[j.val]!

/-- The producer's `ints` uses the least common multiple of normalized
rational denominators. -/
def gapCommonDen : Nat :=
  (List.ofFn (fun i : Fin 9 => (storedGap i).den)).foldl Nat.lcm 1

def g (i : Fin 9) : Nat :=
  (storedGap i).num.toNat * (gapCommonDen / (storedGap i).den)

def G : Nat := sumNat (fun i : Fin 9 => g i)

def columnDen (j : Fin 10) : Nat :=
  (List.ofFn (fun i : Fin 9 => (storedFactor i j).den)).foldl Nat.lcm 1

def ellInt (i : Fin 9) (j : Fin 10) : Nat :=
  (storedFactor i j).num.toNat *
    (columnDen j / (storedFactor i j).den)

def meanNumerator (j : Fin 10) : Nat :=
  G * sumNat (fun i : Fin 9 => ellInt i j) +
    sumNat (fun i : Fin 9 => g i * ellInt i j)

def mean (j : Fin 10) : ℚ :=
  (meanNumerator j : ℚ) / (10 * G * columnDen j)

/-- Source `L=lcm(*ns)` and its integer P vertex numerators. -/
def L : Nat :=
  (List.ofFn (fun j : Fin 10 => meanNumerator j)).foldl Nat.lcm 1

def pv (i : Fin 9) : Nat :=
  G * sumNat (fun j : Fin 10 => ellInt i j * (L / meanNumerator j))

def U : Nat :=
  (List.ofFn (fun i : Fin 9 => pv i)).foldl max 0

def y (i : Fin 9) : Nat := U - pv i

/-- Exact normalized factor and signed transverse deviation at each
vertex; the latter is never cast to Nat. -/
def ai (i : Fin 9) (j : Fin 10) : Nat :=
  10 * G * ellInt i j * (L / meanNumerator j)

def b (j : Fin 10) (i : Fin 9) : ℤ :=
  (ai i j : ℤ) - pv i

def v (j : Fin 10) : Nat :=
  max U ((List.ofFn (fun i : Fin 9 => ai i j)).foldl max 0)

def reconstructedJensen : ℚ :=
  4 * physicalVolume * ((G : ℚ) / (9 * gapCommonDen)) /
    prodRat (fun j : Fin 10 => mean j)

def q80 : Nat := 1208925819614629174706176
def q96 : Nat := 79228162514264337593543950336

/-- Complete-homogeneous coefficients through degree 10. -/
def coefficientTable : List Nat := prefixCoefficients 10 9 y

def homogeneous (k : Nat) : Nat := coefficientTable[k]?.getD 0

def powerMoment (k : Nat) : Nat := sumNat (fun i : Fin 9 => g i * (y i)^k)

def weightedMoment (k : Nat) : Nat :=
  ((List.range (k + 1)).map (fun j => homogeneous (k - j) * powerMoment j)).sum

def H : Nat := 10 * G

def t10MeanNumerator : Nat :=
  G * sumNat (fun i : Fin 9 => y i) + sumNat (fun i : Fin 9 => g i * y i)

def D : Nat := H * U

def z (k : Nat) : ℤ :=
  (weightedMoment k : ℤ) * (H : ℤ)^k -
    (G : ℤ) * ((9 + k).choose k : ℤ) * (t10MeanNumerator : ℤ)^k

def t10Numerator : ℤ :=
  ((List.range' 2 9).map (fun k => z k * (D : ℤ)^(10 - k))).sum * (L : ℤ)^10

def t10Denominator : Nat := G * D^10 * U^10

def signedMomentNumerator (j : Fin 10) : ℤ :=
  let s := sumInt (b j)
  let q := sumInt (fun i => (b j i)^2)
  let p := sumInt (fun i => (g i : ℤ) * b j i)
  let w := sumInt (fun i => (g i : ℤ) * (b j i)^2)
  (G : ℤ) * (s^2 + q) + 2 * s * p + 2 * w

def curvatureNumerator (j : Fin 10) : ℤ := (L : ℤ)^10 * signedMomentNumerator j

def curvatureDenominator (j : Fin 10) : Nat := U^10 * 220 * G * (v j)^2

structure ExactFraction where
  num : ℤ
  den : Nat

def addFrac (a b : ExactFraction) : ExactFraction :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩

def sumFractions (ps : List ExactFraction) : ExactFraction :=
  ps.foldr addFrac ⟨0, 1⟩

def total : ExactFraction :=
  addFrac ⟨t10Numerator, t10Denominator⟩
    (sumFractions (List.ofFn (fun j : Fin 10 =>
      ⟨curvatureNumerator j, curvatureDenominator j⟩)))

def observedTotalTFloorQ80 : Nat := 16007085917676593648460
def observedCurvatureRawQ96 : Nat := 33473824252327663860

def curvatureFloorQ80 (num : ℤ) (den : Nat) (floor : ℤ) : Prop :=
  0 < den ∧ floor * den ≤ q80 * num ∧
    q80 * num < (floor + 1) * den

def jensenProductNumerator (jNum tFloor : Nat) : Nat :=
  jNum * (q80 + tFloor)

def jensenProductDenominator (jDen : Nat) : Nat := jDen * q80

def jensenProductFloorQ96 (jNum jDen tFloor raw : Nat) : Prop :=
  0 < jDen ∧
  raw * jensenProductDenominator jDen ≤
    q96 * jensenProductNumerator jNum tFloor ∧
  q96 * jensenProductNumerator jNum tFloor <
    (raw + 1) * jensenProductDenominator jDen

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row21_physical_vertex_identity :
    simplexId = sourcePosition ∧ vertexIds.size = 9 ∧
    (∀ i : Fin 9, physicalGap i = storedGap i ∧
      ∀ j : Fin 10, physicalFactor i j = storedFactor i j) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row21_source_reconstruction :
    (∀ i : Fin 9, 0 ≤ storedGap i) ∧
    (∀ i : Fin 9, ∀ j : Fin 10, 0 < storedFactor i j) ∧
    (∀ i : Fin 9, (g i : ℚ) / gapCommonDen = storedGap i) ∧
    (∀ i : Fin 9, ∀ j : Fin 10,
      (ellInt i j : ℚ) / columnDen j = storedFactor i j) ∧
    (∀ j : Fin 10, mean j = storedMeans[j.val]!) ∧
    (G : ℚ) / (9 * gapCommonDen) = storedMeanGap ∧
    reconstructedJensen = storedJensen ∧
    0 < reconstructedJensen ∧
    ((reconstructedJensen.num.toNat : ℚ) /
      reconstructedJensen.den) = reconstructedJensen ∧
    (∀ j : Fin 10,
      (G : ℤ) * sumInt (b j) +
        sumInt (fun i : Fin 9 => (g i : ℤ) * b j i) = 0) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row21_positive_primitives :
    0 < G ∧ 0 < L ∧ 0 < U ∧ (∀ j, 0 < v j) ∧ 0 < reconstructedJensen.den := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row21_exact_jensen_rounding :
    jensenProductFloorQ96 reconstructedJensen.num.toNat reconstructedJensen.den
      observedTotalTFloorQ80 observedCurvatureRawQ96 := by
  unfold jensenProductFloorQ96
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem row21_exact_total_rounding :
    curvatureFloorQ80 total.num total.den observedTotalTFloorQ80 := by
  unfold curvatureFloorQ80
  decide +kernel

/-- Each value in the shared row table is the original homogeneous coefficient. -/
private theorem coefficient_agreement :
    ∀ k : Fin 11, homogeneous k = homogeneousFast y k := by
  decide +kernel

theorem coefficient_eq_source (k : ℕ) (hk : k ≤ 10) :
    homogeneous k =
      ∑ exponents : Fin 9 → Fin (k + 1),
        if (∑ i : Fin 9, (exponents i).val) = k then
          ∏ i : Fin 9, y i ^ (exponents i).val
        else 0 := by
  let i : Fin 11 := ⟨k, Nat.lt_succ_of_le hk⟩
  refine (coefficient_agreement i).trans ?_
  exact homogeneousFast_eq_source y k

end ImbalancedChen.P2Winner9Row21Arithmetic
