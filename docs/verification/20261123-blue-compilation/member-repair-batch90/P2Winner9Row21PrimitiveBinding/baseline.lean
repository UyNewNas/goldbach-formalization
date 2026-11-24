import ImbalancedChen.P2Winner9Row21RawVertexData
import ImbalancedChen.P2Winner9CurvatureFullExactAssembly
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is a literal row21 primitive-binding proposal, not an evaluated row
certificate. The nine rational coordinate vectors and stored vertex values
come from the SHA-guarded parent-nine witness in its original vertex-ID
order. The definitions below mirror the pinned producer's `physical`,
`ints`, and `simplex_data` formulas. No producer, Lean `decide`, numerical
replay, checker, or kernel was run. Closed source-identity propositions are
present for later compilation and diagnostic failure reporting.

Physical cap validity, the exact T10/Q80 and Q96 floor assertions, analytic
enclosure, and the other 11,025 rows remain separate.
-/

namespace ImbalancedChen.P2Winner9Row21PrimitiveBinding

open ImbalancedChen.P2Winner9Row21RawVertexData
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor

def coord (i : Fin 9) (j : Nat) : ℚ :=
  (coords[i.val]!).get! j

def S (i : Fin 9) : ℚ := ∑ j : Fin 8, coord i j.val
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
  (factorNum[i.val]![j.val]! : ℚ) / factorDen[i.val]![j.val]!

/-- Exact source-coordinate check against the saved vertex values. Closed
`decide` proposal only; it has not been evaluated. -/
theorem row21_physical_vertex_identity_proposal :
    simplexId = sourcePosition ∧ vertexIds.size = 9 ∧
    (∀ i : Fin 9, physicalGap i = storedGap i ∧
      ∀ j : Fin 10, physicalFactor i j = storedFactor i j) := by
  decide

/-- The producer's `ints` uses the least common multiple of normalized
rational denominators. Lean's exact rational normalization is not run here. -/
def gapCommonDen : Nat :=
  (List.ofFn (fun i : Fin 9 => (storedGap i).den)).foldl Nat.lcm 1

def g (i : Fin 9) : Nat :=
  (storedGap i).num.toNat * (gapCommonDen / (storedGap i).den)

def G : Nat := ∑ i : Fin 9, g i

def columnDen (j : Fin 10) : Nat :=
  (List.ofFn (fun i : Fin 9 => (storedFactor i j).den)).foldl Nat.lcm 1

def ellInt (i : Fin 9) (j : Fin 10) : Nat :=
  (storedFactor i j).num.toNat *
    (columnDen j / (storedFactor i j).den)

def meanNumerator (j : Fin 10) : Nat :=
  G * (∑ i : Fin 9, ellInt i j) +
    (∑ i : Fin 9, g i * ellInt i j)

def mean (j : Fin 10) : ℚ :=
  (meanNumerator j : ℚ) / (10 * G * columnDen j)

/-- Source `L=lcm(*ns)` and its integer P vertex numerators. -/
def L : Nat :=
  (List.ofFn (fun j : Fin 10 => meanNumerator j)).foldl Nat.lcm 1

def pv (i : Fin 9) : Nat :=
  G * (∑ j : Fin 10,
    ellInt i j * (L / meanNumerator j))

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
    (∏ j : Fin 10, mean j)

/-- All equalities are exact rational identities required before this
simplex can instantiate the Phase10 typed input. No certificate result is
deduced merely from the saved Q96 floor. -/
theorem row21_source_reconstruction_proposal :
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
      (G : ℤ) * (∑ i : Fin 9, b j i) +
        (∑ i : Fin 9, (g i : ℤ) * b j i) = 0) := by
  decide

/-- The typed Phase10 input is wholly determined by raw row21 geometry
and the source arithmetic formulas. Its proof fields are closed proposals;
they have not been checked or executed. -/
def row21SimplexData : SimplexData := {
  gaps := g
  y := y
  L := L
  U := U
  deviations := b
  maxima := v
  jensenNum := reconstructedJensen.num.toNat
  jensenDen := reconstructedJensen.den
  gapsPos := by decide
  LPos := by decide
  UPos := by decide
  maximaPos := by decide
  jensenDenPos := by decide
}

/-- The actual curvature witness's row21 Q80 and raw Q96 fields. These are
copied literals, not inferred from the summary totals. Their equality to
the exact source reconstruction is a closed, unexecuted obligation. -/
def observedTotalTFloorQ80 : Nat := 16007085917676593648460
def observedCurvatureRawQ96 : Nat := 33473824252327663860

theorem row21_exact_rounding_proposal :
    curvatureFloorQ80 (total row21SimplexData).num
      (total row21SimplexData).den observedTotalTFloorQ80 ∧
    jensenProductFloorQ96 row21SimplexData.jensenNum
      row21SimplexData.jensenDen observedTotalTFloorQ80
      observedCurvatureRawQ96 := by
  decide

end ImbalancedChen.P2Winner9Row21PrimitiveBinding
