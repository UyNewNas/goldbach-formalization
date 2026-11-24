import ImbalancedChen.P5OriginalTaylorAffineRatioDerivatives
import ImbalancedChen.P5OriginalTaylorWeightDerivatives
import ImbalancedChen.P5OriginalParentJensenRawFields

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original pilot's rational expression, reconstructed from its actual
ten-column source row, independently of the subdivision old/new fields.
No integral inequality is a field of the finite predicate below.  The
closed archive binding is a separate source, and remains UNEVALUATED.
-/
namespace ImbalancedChen.P5OriginalTaylorRationalData
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthCorrelatedRawBoxGates
open P5OriginalTaylorAffineBranchBinding P5OriginalParentJensenRawFields

def evalQ (a : Affine5) (t : Fin 5 → ℚ) : ℚ :=
  a.constant + ∑ i, a.coefficient i * t i

def midpointQ (raw : FifthWireRow) : Fin 5 → ℚ :=
  fun i => (raw.lower i + raw.upper i) / 2

def newSide (raw : FifthWireRow) : Bool :=
  (activeSide raw (maskSlots 5 raw.mask.toNat)).getD false

def oldSides (raw : FifthWireRow) : OldSides :=
  fun I => (activeSide raw (liftOldMask I)).getD false

/-- Python's list is W first, followed by numeric masks 1,...,15. -/
def oldCandidates : List (Option OldMask) :=
  none :: (List.range 15).map (fun k => some (maskSlots 4 (k + 1)))

/-- Strict comparison preserves the first winner when midpoint values tie. -/
def selected (raw : FifthWireRow) : Option OldMask :=
  oldCandidates.foldl (fun winner candidate =>
    if evalQ (selectedOldPlane (oldSides raw) winner) (midpointQ raw) <
        evalQ (selectedOldPlane (oldSides raw) candidate) (midpointQ raw)
    then candidate else winner) none

def newAffine (raw : FifthWireRow) : Affine5 := newPlane raw (newSide raw)
def oldAffine (raw : FifthWireRow) : Affine5 :=
  selectedOldPlane (oldSides raw) (selected raw)

def BranchChecks (raw : FifthWireRow) : Prop :=
  activeSide raw (maskSlots 5 raw.mask.toNat) = some (newSide raw) ∧
  (∀ I ∈ P1LiteralVariableFifthCompactSupplier.oldMasks,
    activeSide raw (liftOldMask I) = some (oldSides raw I)) ∧
  (match selected raw with
    | none => True
    | some I => I ∈ P1LiteralVariableFifthCompactSupplier.oldMasks) ∧
  0 ≤ ((oldAffine raw).sub inheritedWPlane).lower raw.lower raw.upper ∧
  (∀ I ∈ P1LiteralVariableFifthCompactSupplier.oldMasks,
    0 ≤ ((oldAffine raw).sub (tentPlane (liftOldMask I) (oldSides raw I))).lower
      raw.lower raw.upper) ∧
  0 < ((newAffine raw).sub (oldAffine raw)).lower raw.lower raw.upper

instance (raw : FifthWireRow) : Decidable (BranchChecks raw) := by
  unfold BranchChecks
  infer_instance

theorem branchFacts (raw : FifthWireRow) (h : BranchChecks raw) :
    BranchFacts raw (newSide raw) (oldSides raw) (selected raw) := by
  rcases h with ⟨hn, ho, hp, hW, hall, hg⟩
  exact ⟨hn, ho, hp, hW, hall, hg⟩

abbrev Vertex := Fin 5 → Bool
/-- Explicit computable 32-corner list; no quotient representative or
Classical finite enumeration is used in the archive decision bodies. -/
def vertices : List Vertex :=
  (List.range 32).map (fun n i => Nat.testBit n i.val)
def cornerQ (raw : FifthWireRow) (b : Vertex) : Fin 5 → ℚ :=
  fun i => if b i then raw.upper i else raw.lower i

def argumentQ (a : Affine5) (t : Fin 5 → ℚ) : ℚ :=
  (evalQ a t - ∑ i, t i) / t 4

def newArgumentQ (raw : FifthWireRow) (t : Fin 5 → ℚ) : ℚ :=
  argumentQ (newAffine raw) t
def oldArgumentQ (raw : FifthWireRow) (t : Fin 5 → ℚ) : ℚ :=
  argumentQ (oldAffine raw) t

def vertexMin (f : Vertex → ℚ) : ℚ :=
  vertices.foldl (fun a b => min a (f b)) (f (fun _ => false))
def vertexMax (f : Vertex → ℚ) : ℚ :=
  vertices.foldl (fun a b => max a (f b)) (f (fun _ => false))

def newMin (raw : FifthWireRow) : ℚ :=
  vertexMin (fun b => newArgumentQ raw (cornerQ raw b))
def newMax (raw : FifthWireRow) : ℚ :=
  vertexMax (fun b => newArgumentQ raw (cornerQ raw b))
def oldMin (raw : FifthWireRow) : ℚ :=
  vertexMin (fun b => oldArgumentQ raw (cornerQ raw b))
def oldMax (raw : FifthWireRow) : ℚ :=
  vertexMax (fun b => oldArgumentQ raw (cornerQ raw b))
def aMin (raw : FifthWireRow) : ℚ := min (newMin raw) (oldMin raw)
def gap (raw : FifthWireRow) : ℚ := vertexMax (fun b =>
  newArgumentQ raw (cornerQ raw b) - oldArgumentQ raw (cornerQ raw b))

def residualPlane (a : Affine5) : Affine5 := a.sub (indicatorAffine 1 Finset.univ)
def coordinatePlane (q : ℚ) : Affine5 := ⟨0, fun i => if i = 4 then q else 0⟩
def ratioLowerCheck (raw : FifthWireRow) (a : Affine5) (q : ℚ) : Prop :=
  0 ≤ ((residualPlane a).sub (coordinatePlane q)).lower raw.lower raw.upper
def ratioUpperCheck (raw : FifthWireRow) (a : Affine5) (q : ℚ) : Prop :=
  0 ≤ ((coordinatePlane q).sub (residualPlane a)).lower raw.lower raw.upper
def gapUpperCheck (raw : FifthWireRow) : Prop :=
  0 ≤ ((coordinatePlane (gap raw)).sub ((newAffine raw).sub (oldAffine raw))).lower
    raw.lower raw.upper

def logLower14Q (x : ℚ) : ℚ :=
  2 * ∑ k ∈ Finset.range 14, ((x - 1) / (x + 1)) ^ (2 * k + 1) / (2 * (k : ℚ) + 1)
def logUpper14Q (x : ℚ) : ℚ :=
  let z := (x - 1) / (x + 1)
  logLower14Q x + 2 * z ^ 29 / (29 * (1 - z ^ 2))

def m1Q (raw : FifthWireRow) : ℚ :=
  (aMin raw / (aMin raw - 1) - logLower14Q (aMin raw - 1)) / aMin raw ^ 2
def m2Q (raw : FifthWireRow) : ℚ :=
  2 / (aMin raw ^ 2 * (aMin raw - 1)) + 1 / (aMin raw * (aMin raw - 1) ^ 2)

def residualCoefficientQ (a : Affine5) (i : Fin 5) : ℚ := a.coefficient i - 1
def DQ (raw : FifthWireRow) (a : Affine5) (sMax : ℚ) (i : Fin 5) : ℚ :=
  if i = 4 then (sMax - residualCoefficientQ a i) / raw.lower 4
  else |residualCoefficientQ a i| / raw.lower 4
def EQ (raw : FifthWireRow) (a : Affine5) (sMax : ℚ) (i : Fin 5) : ℚ :=
  if i = 4 then 2 * DQ raw a sMax i / raw.lower 4 else 0
def TQ (raw : FifthWireRow) (i : Fin 5) : ℚ :=
  (|residualCoefficientQ (newAffine raw) i - residualCoefficientQ (oldAffine raw) i| +
    if i = 4 then gap raw else 0) / raw.lower 4
def powerQ (i : Fin 5) : ℚ := if i = 4 then 2 else 1
def kQ (raw : FifthWireRow) (i : Fin 5) : ℚ := powerQ i / raw.lower i
def qQ (raw : FifthWireRow) (i : Fin 5) : ℚ :=
  powerQ i * (powerQ i + 1) / raw.lower i ^ 2
def weightQ (t : Fin 5 → ℚ) : ℚ := 4 / ((∏ i, t i) * t 4)
def wmaxQ (raw : FifthWireRow) : ℚ := weightQ raw.lower
def midpointLowerQ (raw : FifthWireRow) : ℚ :=
  let sn := newArgumentQ raw (midpointQ raw)
  let so := oldArgumentQ raw (midpointQ raw)
  weightQ (midpointQ raw) * (logLower14Q (sn - 1) / sn - logUpper14Q (so - 1) / so)

/-- The original complete weighted diagonal Hessian expression, with the
new/old derivative cancellation and the fifth-coordinate power two. -/
def hessianQ (raw : FifthWireRow) (i : Fin 5) : ℚ :=
  let dn := DQ raw (newAffine raw) (newMax raw) i
  let do := DQ raw (oldAffine raw) (oldMax raw) i
  let en := EQ raw (newAffine raw) (newMax raw) i
  let eo := EQ raw (oldAffine raw) (oldMax raw) i
  let di := min (m1Q raw * (dn + do))
    (m1Q raw * TQ raw i + m2Q raw * gap raw * do)
  let dii := m2Q raw * (dn * dn + do * do) + m1Q raw * (en + eo)
  wmaxQ raw * (qQ raw i * (m1Q raw * gap raw) + 2 * kQ raw i * di + dii)

def widthQ (raw : FifthWireRow) : ℚ := 1 / (raw.grid : ℚ)
def remainderQ (raw : FifthWireRow) : ℚ := widthQ raw ^ 2 * (∑ i, hessianQ raw i) / 24
def taylorLowerQ (raw : FifthWireRow) : ℚ :=
  widthQ raw ^ 5 * (midpointLowerQ raw - remainderQ raw)
def taylorFloorZ (raw : FifthWireRow) : ℤ :=
  ((2 : ℚ) ^ 80 * taylorLowerQ raw).floor

/-- Finite source data only: original branches, positive endpoints, genuine
ratio/gap affine inequalities, and the original no-interior-seam condition.
The supplementary affine inequalities are rational forms of the vertex
bounds and are checked, rather than assuming the resulting real ranges. -/
def TaylorFiniteFacts (raw : FifthWireRow) : Prop :=
  raw.grid = 400 ∧ (∀ i, 0 < raw.lower i) ∧ BranchChecks raw ∧
  2 ≤ aMin raw ∧ 0 ≤ gap raw ∧
  ratioLowerCheck raw (newAffine raw) (aMin raw) ∧
  ratioLowerCheck raw (oldAffine raw) (aMin raw) ∧
  ratioUpperCheck raw (newAffine raw) (newMax raw) ∧
  ratioUpperCheck raw (oldAffine raw) (oldMax raw) ∧
  newMax raw ≤ 4 ∧ oldMax raw ≤ 4 ∧ gapUpperCheck raw ∧
  (∀ k ∈ ([2, 3, 4] : List ℚ),
    ¬ (newMin raw < k ∧ k < newMax raw) ∧
    ¬ (oldMin raw < k ∧ k < oldMax raw))

instance (raw : FifthWireRow) : Decidable (TaylorFiniteFacts raw) := by
  unfold TaylorFiniteFacts ratioLowerCheck ratioUpperCheck gapUpperCheck
  infer_instance

/-- A pilot bound is used only after its finite smooth-box tests and the
original strict comparison with the unrounded old Jensen expression. -/
def available (raw : FifthWireRow) : Prop :=
  TaylorFiniteFacts raw ∧ parentJensenRationalQ raw < taylorLowerQ raw
instance (raw : FifthWireRow) : Decidable (available raw) := by
  unfold available
  infer_instance

/-- Absent Taylor data contributes zero, exactly as overrides.get(i,0).
The archive max binding also checks positivity of the retained old floor. -/
def availableTaylorFloorZ (raw : FifthWireRow) : ℤ :=
  if available raw then taylorFloorZ raw else 0

theorem available_branchFacts (raw : FifthWireRow) (h : available raw) :
    BranchFacts raw (newSide raw) (oldSides raw) (selected raw) :=
  branchFacts raw h.1.2.2.1

noncomputable section
open Set P5OriginalTaylorAffineRatioDerivatives

theorem evalQ_cast (a : Affine5) (t : Fin 5 → ℚ) :
    (evalQ a t : ℝ) = a.eval (fun i => (t i : ℝ)) := by
  simp [evalQ, Affine5.eval]

theorem argumentQ_cast (a : Affine5) (t : Fin 5 → ℚ) :
    (argumentQ a t : ℝ) = affineArgument a (fun i => (t i : ℝ)) := by
  simp [argumentQ, affineArgument, P5OldFifthPointwiseQ.residual,
    P5OldFifthPointwiseQ.sum5, evalQ_cast]

theorem coordinatePlane_eval (q : ℚ) (t : Fin 5 → ℝ) :
    (coordinatePlane q).eval t = (q : ℝ) * t 4 := by
  simp [coordinatePlane, Affine5.eval, ite_mul]

theorem residualPlane_eval (a : Affine5) (t : Fin 5 → ℝ) :
    (residualPlane a).eval t = a.eval t - P5OldFifthPointwiseQ.sum5 t := by
  rw [residualPlane, Affine5.eval_sub]
  simp [indicatorAffine, Affine5.eval, P5OldFifthPointwiseQ.sum5]

theorem ratioLowerCheck_sound (raw : FifthWireRow) (a : Affine5) (q : ℚ)
    (h : ratioLowerCheck raw a q) (t : Fin 5 → ℝ)
    (ht : t ∈ rawClosedBox raw) (h4 : 0 < t 4) :
    (q : ℝ) ≤ affineArgument a t := by
  have hl := Affine5.lower_le_eval ((residualPlane a).sub (coordinatePlane q))
    raw.lower raw.upper t (fun i => (ht i).1) (fun i => (ht i).2)
  have hh : (0 : ℝ) ≤
      (((residualPlane a).sub (coordinatePlane q)).lower raw.lower raw.upper : ℚ) := by
    exact_mod_cast h
  rw [Affine5.eval_sub, residualPlane_eval, coordinatePlane_eval] at hl
  apply (le_div_iff₀ h4).2
  change (q : ℝ) * t 4 ≤ a.eval t - P5OldFifthPointwiseQ.sum5 t
  linarith

theorem ratioUpperCheck_sound (raw : FifthWireRow) (a : Affine5) (q : ℚ)
    (h : ratioUpperCheck raw a q) (t : Fin 5 → ℝ)
    (ht : t ∈ rawClosedBox raw) (h4 : 0 < t 4) :
    affineArgument a t ≤ (q : ℝ) := by
  have hl := Affine5.lower_le_eval ((coordinatePlane q).sub (residualPlane a))
    raw.lower raw.upper t (fun i => (ht i).1) (fun i => (ht i).2)
  have hh : (0 : ℝ) ≤
      (((coordinatePlane q).sub (residualPlane a)).lower raw.lower raw.upper : ℚ) := by
    exact_mod_cast h
  rw [Affine5.eval_sub, residualPlane_eval, coordinatePlane_eval] at hl
  apply (div_le_iff₀ h4).2
  change a.eval t - P5OldFifthPointwiseQ.sum5 t ≤ (q : ℝ) * t 4
  linarith

theorem gapUpperCheck_sound (raw : FifthWireRow) (h : gapUpperCheck raw)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) (h4 : 0 < t 4) :
    affineArgument (newAffine raw) t - affineArgument (oldAffine raw) t ≤
      (gap raw : ℝ) := by
  have hl := Affine5.lower_le_eval
    ((coordinatePlane (gap raw)).sub ((newAffine raw).sub (oldAffine raw)))
    raw.lower raw.upper t (fun i => (ht i).1) (fun i => (ht i).2)
  have hh : (0 : ℝ) ≤
      (((coordinatePlane (gap raw)).sub ((newAffine raw).sub (oldAffine raw))).lower
        raw.lower raw.upper : ℚ) := by exact_mod_cast h
  rw [Affine5.eval_sub, coordinatePlane_eval, Affine5.eval_sub] at hl
  unfold affineArgument P5OldFifthPointwiseQ.residual
  rw [← sub_div]
  apply (div_le_iff₀ h4).2
  linarith

/-- Actual closed-box ranges, derived from primitive rational data.
There is no analytic range hypothesis supplied by the caller. -/
theorem actual_ranges (raw : FifthWireRow) (h : TaylorFiniteFacts raw)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) :
    0 < t 4 ∧ (2 : ℝ) ≤ (aMin raw : ℝ) ∧
    (aMin raw : ℝ) ≤ affineArgument (oldAffine raw) t ∧
    affineArgument (oldAffine raw) t < affineArgument (newAffine raw) t ∧
    affineArgument (newAffine raw) t ≤ (4 : ℝ) ∧
    affineArgument (newAffine raw) t ≤ (newMax raw : ℝ) ∧
    affineArgument (oldAffine raw) t ≤ (oldMax raw : ℝ) ∧
    affineArgument (newAffine raw) t - affineArgument (oldAffine raw) t ≤ (gap raw : ℝ) := by
  rcases h with ⟨_, hp, hb, ha, _, hnL, hoL, hnU, hoU, hn4, _, hg, _⟩
  have h4 : 0 < t 4 := (show (0 : ℝ) < (raw.lower 4 : ℝ) by exact_mod_cast hp 4).trans_le (ht 4).1
  have hlo := ratioLowerCheck_sound raw _ _ hoL t ht h4
  have hnu := ratioUpperCheck_sound raw _ _ hnU t ht h4
  have hou := ratioUpperCheck_sound raw _ _ hoU t ht h4
  have hdelta := gapUpperCheck_sound raw hg t ht h4
  have hb' := (branchFacts raw hb).strict_gain
  have hlow := Affine5.lower_le_eval ((newAffine raw).sub (oldAffine raw))
    raw.lower raw.upper t (fun i => (ht i).1) (fun i => (ht i).2)
  have hstrict : (oldAffine raw).eval t < (newAffine raw).eval t := by
    have hbR : (0 : ℝ) <
        (((newAffine raw).sub (oldAffine raw)).lower raw.lower raw.upper : ℚ) := by
      exact_mod_cast hb'
    rw [Affine5.eval_sub] at hlow
    linarith
  have hargs : affineArgument (oldAffine raw) t < affineArgument (newAffine raw) t := by
    apply (div_lt_div_iff_of_pos_right h4).2
    exact sub_lt_sub_right hstrict _
  exact ⟨h4, by exact_mod_cast ha, hlo, hargs,
    hnu.trans (by exact_mod_cast hn4), hnu, hou, hdelta⟩

theorem logLower14Q_cast (x : ℚ) :
    (logLower14Q x : ℝ) = P5OriginalTaylorLogBounds.logLower14 (x : ℝ) := by
  simp [logLower14Q, P5OriginalTaylorLogBounds.logLower14,
    P5OriginalTaylorLogBounds.partial14, P5OriginalTaylorLogBounds.oddTerm]

theorem logUpper14Q_cast (x : ℚ) :
    (logUpper14Q x : ℝ) = P5OriginalTaylorLogBounds.logUpper14 (x : ℝ) := by
  simp [logUpper14Q, P5OriginalTaylorLogBounds.logUpper14,
    P5OriginalTaylorLogBounds.upper14, P5OriginalTaylorLogBounds.logLower14,
    logLower14Q_cast]

end
end ImbalancedChen.P5OriginalTaylorRationalData
