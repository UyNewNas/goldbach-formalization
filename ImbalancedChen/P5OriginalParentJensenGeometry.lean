import ImbalancedChen.P5OriginalParentJensenRawFields
import ImbalancedChen.P5OriginalChildIntegerWireBinding
import ImbalancedChen.P1OriginalFifthCorrelatedRawBoxGates

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original grid400 parent's own d/A/B and midpoint-frozen source picks.
The finite facts below contain rational geometry only.  They contain no
integral, Jensen inequality, saved-old licence, or Taylor branch claim.
The complete archive supplier lives in ArchiveGeometry, separately from
these exact rational-to-real conversions.  No child d/A/B is substituted.
-/
namespace ImbalancedChen.P5OriginalParentJensenGeometry
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthCorrelatedRawBoxGates
open P5OriginalParentJensenRawFields
open P5OriginalChildIntegerWireBinding
open P5NamedFifthPayloadSemantics
open P5OldFifthFrozenUpperSurrogate P5OldFifthFrozenGapConcavity
open P5OldFifthFiveCoordinateTree P5OldFifthOneCoordinateVertexChord
open P5OldFifthChildGapIntegral
open P5OldFifthPointwiseQ P1OriginalFifthRawBoxSelectorEquivalence

/-- SAME raw A/B, subtracted from the SAME selected tent plane before
coefficient-sign minimization. This retains the fifth denominator. -/
def parentRatioDeficit (raw : FifthWireRow) (side : Bool) : Affine5 :=
  ((indicatorAffine 1 Finset.univ).add
    (indicatorAffine (parentBQ raw) {4})).sub
      (tentPlane (maskSlots 5 raw.mask.toNat) side)

/-- The original saved vertex sum, original integer/rational midpoint
argmin agreement, and one affine upper-plane licence on the whole parent.
Each entry is decidable arithmetic on the original ten-column row. -/
def ParentGeometryFacts (raw : FifthWireRow) : Prop :=
  (raw.vertexGapSum : ℚ) = parentDQ raw ∧
  (∀ I : OldMask, originalPick raw I = sourcePick raw I) ∧
  (0 ≤ (parentRatioDeficit raw false).lower raw.lower raw.upper ∨
    0 ≤ (parentRatioDeficit raw true).lower raw.lower raw.upper)

instance (raw : FifthWireRow) : Decidable (ParentGeometryFacts raw) := by
  unfold ParentGeometryFacts
  infer_instance

noncomputable section
open Set
open scoped Classical

def parentVertex (raw : FifthWireRow) (ε : VertexChoice) (i : Fin 5) : ℝ :=
  if ε i then (raw.upper i : ℝ) else (raw.lower i : ℝ)

theorem cast_parentVertexQ (raw : FifthWireRow) (ε : VertexChoice) :
    (fun i => (parentVertexQ raw ε i : ℝ)) = parentVertex raw ε := by
  funext i
  by_cases hi : ε i <;> simp [parentVertexQ, parentVertex, hi]

/-- Reuses the actual frozen-gap cast, including all fifteen old planes
and W. The parent numerator scale is 32*400, never 32*1600. -/
theorem cast_parentDQ (raw : FifthWireRow) :
    (parentDQ raw : ℝ) = ∑ w : Word, (32 * 400 : ℝ) *
      frozenGap (sourcePicks raw) raw (parentVertex raw (wordChoice w)) := by
  unfold parentDQ
  push_cast
  apply Finset.sum_congr rfl
  intro w _
  rw [cast_gapQ, cast_parentVertexQ]

theorem parent_vertex_gap_sum (raw : FifthWireRow) (hf : ParentGeometryFacts raw) :
    (raw.vertexGapSum : ℝ) = ∑ w : Word, (32 * 400 : ℝ) *
      frozenGap (sourcePicks raw) raw (parentVertex raw (wordChoice w)) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) hf.1
  simpa only [Rat.cast_intCast, cast_parentDQ] using h

theorem parent_picks_eq_original_integer (raw : FifthWireRow)
    (hf : ParentGeometryFacts raw) (I : OldMask) :
    sourcePicks raw I = originalPick raw I := (hf.2.1 I).symm

theorem parentVertex_mem_rawClosedBox (raw : FifthWireRow) (hg : 0 < raw.grid)
    (ε : VertexChoice) : parentVertex raw ε ∈ rawClosedBox raw := by
  intro i
  have ho : (raw.lower i : ℝ) ≤ (raw.upper i : ℝ) :=
    Rat.cast_le.mpr (raw_endpoints_ordered raw hg i)
  by_cases hi : ε i <;> simp [parentVertex, hi, ho]

/-- Convert the existing exact affine lower operator; no sampled-vertex
extremum principle or new desired ratio inequality is assumed. -/
theorem parent_new_ratio (raw : FifthWireRow)
    (hf : ParentGeometryFacts raw)
    (hlo : ∀ i : Fin 5, 0 < (raw.lower i : ℝ))
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) :
    residual (rawCandidate 0 raw t) t ≤ (parentBQ raw : ℝ) := by
  have hside (side : Bool)
      (hs : 0 ≤ (parentRatioDeficit raw side).lower raw.lower raw.upper) :
      residual (rawCandidate 0 raw t) t ≤ (parentBQ raw : ℝ) := by
    have hlower : (0 : ℝ) ≤
        ((parentRatioDeficit raw side).lower raw.lower raw.upper : ℝ) :=
      Rat.cast_nonneg.mpr hs
    have heval := (parentRatioDeficit raw side).lower_le_eval
      raw.lower raw.upper t (fun i => (ht i).1) (fun i => (ht i).2)
    have hdef : (parentRatioDeficit raw side).eval t =
        sum5 t + (parentBQ raw : ℝ) * t 4 -
          (tentPlane (maskSlots 5 raw.mask.toNat) side).eval t := by
      simp [parentRatioDeficit, Affine5.eval_sub, Affine5.eval_add,
        indicatorAffine_eval, sum5]
    have hcap : rawCandidate 0 raw t ≤
        (tentPlane (maskSlots 5 raw.mask.toNat) side).eval t := by
      rw [tentPlane_eval]
      simp only [rawCandidate, mul_zero, sub_zero, VariableEnvelope.v_eq_min]
      cases side
      · exact min_le_left _ _
      · exact min_le_right _ _
    have ht4 : 0 < t 4 := (hlo 4).trans_le (ht 4).1
    apply (div_le_iff₀ ht4).mpr
    rw [hdef] at heval
    dsimp [residual]
    linarith
  rcases hf.2.2 with hA | hC
  · exact hside false hA
  · exact hside true hC

/-- The producer's e is its OWN 32-vertex mean divided by the parent u5.
This equality does not assert a Jensen/integral estimate. -/
theorem parentEQ_eq (raw : FifthWireRow) (hg : raw.grid = 400)
    (hf : ParentGeometryFacts raw) (h5 : 0 < raw.lo 4) :
    (parentEQ raw : ℝ) =
      ((∑ w : Word, frozenGap (sourcePicks raw) raw
        (parentVertex raw (wordChoice w))) / 32) / (raw.upper 4 : ℝ) := by
  have hd := parent_vertex_gap_sum raw hf
  rw [← Finset.mul_sum] at hd
  have h5R : (0 : ℝ) < (raw.lo 4 : ℝ) := by exact_mod_cast h5
  have hn : (raw.lo 4 : ℝ) + 1 ≠ 0 := by linarith
  simp only [parentEQ, FifthWireRow.upper, hg]
  push_cast
  rw [hd]
  field_simp [hn]
  <;> ring

end
end ImbalancedChen.P5OriginalParentJensenGeometry
