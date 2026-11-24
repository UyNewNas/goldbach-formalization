import ImbalancedChen.P2Winner9Row21RawVertexData
import ImbalancedChen.P2Winner9CurvatureFullExactAssembly
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.List
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
  (coords[i.val]!)[j]!

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
  ((factorNum[i.val]!)[j.val]! : ℚ) / (factorDen[i.val]!)[j.val]!

/-- Exact source-coordinate check against the saved vertex values. Closed
`decide` proposal only; it has not been evaluated. -/
theorem row21_physical_vertex_identity_proposal :
    simplexId = sourcePosition ∧ vertexIds.size = 9 ∧
    (∀ i : Fin 9, physicalGap i = storedGap i ∧
      ∀ j : Fin 10, physicalFactor i j = storedFactor i j) := by
  decide +kernel

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
  decide +kernel

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
  gapsPos := by decide +kernel
  LPos := by decide +kernel
  UPos := by decide +kernel
  maximaPos := by decide +kernel
  jensenDenPos := by decide +kernel
}

/-- Reindex the original bounded exponent enumeration by the existing exact
sum-k tuple enumeration. Only the implementation of the finite sum changes
inside the proof; every original term appears exactly once. -/
private theorem homogeneous_eq_exact_antidiagonal (nodes : Fin 9 → Nat) (k : Nat) :
    homogeneous nodes k =
      ∑ α ∈ Finset.Nat.antidiagonalTuple 9 k, ∏ i : Fin 9, nodes i ^ α i := by
  classical
  unfold homogeneous
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun (α : Fin 9 → Fin (k + 1)) _ => fun i : Fin 9 => (α i).val) ?_ ?_ ?_ ?_
  · intro α hα
    exact Finset.Nat.mem_antidiagonalTuple.mpr (Finset.mem_filter.mp hα).2
  · intro α _ β _ h
    funext i
    exact Fin.ext (congrFun h i)
  · intro β hβ
    have hsum : (∑ i : Fin 9, β i) = k :=
      Finset.Nat.mem_antidiagonalTuple.mp hβ
    have hbound (i : Fin 9) : β i ≤ k := by
      calc
        β i ≤ ∑ j : Fin 9, β j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (β j)) (Finset.mem_univ i)
        _ = k := hsum
    let α : Fin 9 → Fin (k + 1) :=
      fun i => ⟨β i, Nat.lt_succ_of_le (hbound i)⟩
    refine ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change (∑ i : Fin 9, β i) = k
      exact hsum
    · rfl
  · intro α _
    rfl

/-- The original complete-homogeneous prefix convolution, using the
existing pair antidiagonal rather than enumerating rejected tuples. -/
private def exactPrefixH : List Nat → Nat → Nat
  | [], k => if k = 0 then 1 else 0
  | a :: as, k =>
      ((List.Nat.antidiagonal k).map fun p =>
        a ^ p.1 * exactPrefixH as p.2).sum

private theorem exactPrefixH_zero (as : List Nat) : exactPrefixH as 0 = 1 := by
  induction as with
  | nil => simp [exactPrefixH]
  | cons a as ih => simp [exactPrefixH, ih]

/-- The producer's original h[k] += a*h[k-1] prefix identity, without
any division, archive value, distinctness or nonzero-node premise. -/
private theorem exactPrefixH_cons_succ (a : Nat) (as : List Nat) (k : Nat) :
    exactPrefixH (a :: as) (k + 1) =
      exactPrefixH as (k + 1) + a * exactPrefixH (a :: as) k := by
  simp only [exactPrefixH, List.Nat.antidiagonal_succ,
    List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
    Prod.map_apply, id_eq, Nat.succ_eq_add_one, pow_zero, one_mul]
  congr 1
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [pow_succ]
  ring

private theorem antidiagonalTuple_sum_eq_prefixH {n : Nat}
    (nodes : Fin n → Nat) (k : Nat) :
    ((List.Nat.antidiagonalTuple n k).map
      (fun α => ∏ i : Fin n, nodes i ^ α i)).sum =
        exactPrefixH (List.ofFn nodes) k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [List.Nat.antidiagonalTuple, exactPrefixH, List.ofFn]
  | succ n ih =>
      rw [List.ofFn_succ, exactPrefixH]
      simp only [List.Nat.antidiagonalTuple, List.map_flatMap,
        List.map_map, Function.comp_def, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, List.flatMap, List.sum_flatten,
        List.sum_map_mul_left, ih]

/-- Nat.rec retains the preceding coefficient in the original prefix
recurrence. This is an exact proof representation, not a new moment. -/
private def exactPrefixRec : List Nat → Nat → Nat
  | [] => fun k => if k = 0 then 1 else 0
  | a :: as =>
      Nat.rec 1 (fun k previous => exactPrefixRec as (k + 1) + a * previous)

private theorem exactPrefixH_eq_rec (as : List Nat) (k : Nat) :
    exactPrefixH as k = exactPrefixRec as k := by
  induction as generalizing k with
  | nil => rfl
  | cons a as ih =>
      induction k with
      | zero =>
          rw [exactPrefixH_zero]
          rfl
      | succ k ihk =>
          rw [exactPrefixH_cons_succ]
          change exactPrefixH as (k + 1) + a * exactPrefixH (a :: as) k =
            exactPrefixRec as (k + 1) + a * exactPrefixRec (a :: as) k
          rw [ih, ihk]

private theorem homogeneous_eq_exact_prefixRec (nodes : Fin 9 → Nat) (k : Nat) :
    homogeneous nodes k = exactPrefixRec (List.ofFn nodes) k := by
  calc
    homogeneous nodes k =
        ∑ α ∈ Finset.Nat.antidiagonalTuple 9 k, ∏ i : Fin 9, nodes i ^ α i :=
      homogeneous_eq_exact_antidiagonal nodes k
    _ = ((List.Nat.antidiagonalTuple 9 k).map
        (fun α => ∏ i : Fin 9, nodes i ^ α i)).sum := by rfl
    _ = exactPrefixH (List.ofFn nodes) k := antidiagonalTuple_sum_eq_prefixH nodes k
    _ = exactPrefixRec (List.ofFn nodes) k := exactPrefixH_eq_rec _ _

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
  unfold curvatureFloorQ80 jensenProductFloorQ96
  refine ⟨⟨(total row21SimplexData).denPos, ?_, ?_⟩,
    row21SimplexData.jensenDenPos, ?_, ?_⟩
  · simp only [total, add, t10, t10Numerator, z, weightedMoment,
      homogeneous_eq_exact_prefixRec] <;> decide +kernel
  · simp only [total, add, t10, t10Numerator, z, weightedMoment,
      homogeneous_eq_exact_prefixRec] <;> decide +kernel
  · decide +kernel
  · decide +kernel

end ImbalancedChen.P2Winner9Row21PrimitiveBinding
