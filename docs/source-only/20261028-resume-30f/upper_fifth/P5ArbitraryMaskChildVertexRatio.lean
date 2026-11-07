import ImbalancedChen.P5OriginalChildIntegerWireBinding
import ImbalancedChen.P5OldFifthActualChildJensenIntegral

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
Actual whole-child two-plane ratio implication for ARBITRARY original
fifth masks. No mask28 or two-named-parent formula is used. The affine
vertex lemma follows by choosing each maximizing coordinate endpoint;
positive denominators then give the actual linear-fractional inequality.
-/
namespace ImbalancedChen.P5ArbitraryMaskChildVertexRatio
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P5OriginalChildIntegerWireBinding P5NamedFifthPayloadSemantics
open P5OldFifthExact64ChildTiling P5OldFifthFiveCoordinateTree
open P5OldFifthOneCoordinateVertexChord P5OldFifthPointwiseQ
open P5OldFifthChildGapIntegral

def sideAlphaQ (side : Bool) : ℚ := if side then 57 / 64 else 1 / 2
def sideBetaQ (side : Bool) : ℚ := if side then -3 / 2 else 1 / 2

def planeValueQ (raw : FifthWireRow) (side : Bool) (t : Fin 5 → ℚ) : ℚ :=
  sideAlphaQ side + sideBetaQ side * ∑ i ∈ maskSlots 5 raw.mask.toNat, t i

def vertexRatioQ (raw : FifthWireRow) (side : Bool) (t : Fin 5 → ℚ) : ℚ :=
  (planeValueQ raw side t - ∑ i : Fin 5, t i) / t 4

def originalChosenSide (raw : FifthWireRow) (c : ChildIndex) : Bool :=
  let a := originalPlaneMax raw c false
  let cc := originalPlaneMax raw c true
  decide (cc.num * a.den < a.num * cc.den)

def originalRatioQ (raw : FifthWireRow) (c : ChildIndex) : ℚ :=
  ((originalFields raw c).A : ℚ) / ((originalFields raw c).B : ℚ)

def wordOfChoice (ε : VertexChoice) : Word := (ε 0, ε 1, ε 2, ε 3, ε 4)

theorem wordChoice_wordOfChoice (ε : VertexChoice) : wordChoice (wordOfChoice ε) = ε := by
  funext i
  fin_cases i <;> simp [wordChoice, wordOfChoice]

noncomputable section
open Set
open scoped Classical

def planeValue (raw : FifthWireRow) (side : Bool) (t : Fin 5 → ℝ) : ℝ :=
  (sideAlphaQ side : ℝ) + (sideBetaQ side : ℝ) *
    ∑ i ∈ maskSlots 5 raw.mask.toNat, t i

/-- No convexity/extremum conclusion is assumed. Each coordinate chooses
its endpoint from the actual sign of the same affine coefficient. -/
theorem affine_vertex_upper
    (raw : FifthWireRow) (c : ChildIndex) (α β B : ℝ)
    (hvertex : ∀ ε : VertexChoice,
      α + β * (∑ i ∈ maskSlots 5 raw.mask.toNat, vertexPoint raw c ε i) -
        sum5 (vertexPoint raw c ε) - B * vertexPoint raw c ε 4 ≤ 0)
    (t : Fin 5 → ℝ)
    (ht : t ∈ Icc (childLeft raw c) (childRight raw c)) :
    α + β * (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) - sum5 t - B * t 4 ≤ 0 := by
  let I := maskSlots 5 raw.mask.toNat
  let coeff : Fin 5 → ℝ := fun i =>
    β * (if i ∈ I then 1 else 0) - 1 - if i = 4 then B else 0
  let ε : VertexChoice := fun i => decide (0 ≤ coeff i)
  have heval (x : Fin 5 → ℝ) :
      α + β * (∑ i ∈ I, x i) - sum5 x - B * x 4 =
        α + ∑ i : Fin 5, coeff i * x i := by
    have hI : (∑ i : Fin 5, if i ∈ I then x i else 0) = ∑ i ∈ I, x i := by
      rw [← Finset.sum_filter]
      simp
    have hp (i : Fin 5) : coeff i * x i =
        β * (if i ∈ I then x i else 0) - x i - (if i = 4 then B * x i else 0) := by
      by_cases hi : i ∈ I <;> by_cases h4 : i = 4 <;>
        simp [coeff, hi, h4] <;> ring
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hI]
    simp [sum5] <;> ring
  have hcoord : ∀ i : Fin 5, coeff i * t i ≤ coeff i * vertexPoint raw c ε i := by
    intro i
    by_cases hc : 0 ≤ coeff i
    · simpa [vertexPoint, ε, hc] using mul_le_mul_of_nonneg_left (ht.2 i) hc
    · simpa [vertexPoint, ε, hc] using
        mul_le_mul_of_nonpos_left (ht.1 i) (le_of_not_ge hc)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5))) (fun i _ => hcoord i)
  have hv := hvertex ε
  change α + β * (∑ i ∈ I, vertexPoint raw c ε i) -
    sum5 (vertexPoint raw c ε) - B * vertexPoint raw c ε 4 ≤ 0 at hv
  rw [heval] at hv
  change α + β * (∑ i ∈ I, t i) - sum5 t - B * t 4 ≤ 0
  rw [heval]
  linarith

/-- A or C is always an upper plane for the SAME actual selected mask. -/
theorem actual_candidate_le_plane (raw : FifthWireRow) (side : Bool) (t : Fin 5 → ℝ) :
    rawCandidate 0 raw t ≤ planeValue raw side t := by
  simp only [rawCandidate, mul_zero, sub_zero, VariableEnvelope.v_eq_min]
  cases side
  · have hp : planeValue raw false t =
        VariableEnvelope.A (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) := by
      simp [planeValue, sideAlphaQ, sideBetaQ, VariableEnvelope.A] <;> ring
    rw [hp]
    exact min_le_left _ _
  · have hp : planeValue raw true t =
        VariableEnvelope.C (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) := by
      simp [planeValue, sideAlphaQ, sideBetaQ, VariableEnvelope.C] <;> ring
    rw [hp]
    exact min_le_right _ _

/-- The input is a PURE RATIONAL vertex comparison for an original
integer-selected plane. The conclusion is the actual whole-child bound;
no desired Jensen bound, count, integral or physical density is a premise. -/
theorem actual_child_ratio_of_rational_vertices
    (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i, 0 < childLeft raw c i)
    (side : Bool) (B : ℚ)
    (hvertex : ∀ w : Word,
      vertexRatioQ raw side (childVertexQ raw c (wordChoice w)) ≤ B)
    (t : Fin 5 → ℝ)
    (ht : t ∈ Icc (childLeft raw c) (childRight raw c)) :
    residual (rawCandidate 0 raw t) t ≤ (B : ℝ) := by
  have hreal (ε : VertexChoice) :
      (planeValue raw side (vertexPoint raw c ε) - sum5 (vertexPoint raw c ε)) /
          vertexPoint raw c ε 4 ≤ (B : ℝ) := by
    have hq := hvertex (wordOfChoice ε)
    rw [wordChoice_wordOfChoice] at hq
    have hr := Rat.cast_le.mpr hq
    simp only [vertexRatioQ, planeValueQ] at hr
    push_cast at hr
    change (planeValue raw side (fun i => (childVertexQ raw c ε i : ℝ)) -
      sum5 (fun i => (childVertexQ raw c ε i : ℝ))) /
      (childVertexQ raw c ε 4 : ℝ) ≤ (B : ℝ) at hr
    have hlast := congrFun (cast_childVertexQ raw c ε) (4 : Fin 5)
    rw [hlast] at hr
    simpa only [cast_childVertexQ] using hr
  have hlin (ε : VertexChoice) :
      (sideAlphaQ side : ℝ) + (sideBetaQ side : ℝ) *
          (∑ i ∈ maskSlots 5 raw.mask.toNat, vertexPoint raw c ε i) -
        sum5 (vertexPoint raw c ε) - (B : ℝ) * vertexPoint raw c ε 4 ≤ 0 := by
    have hv := vertexPoint_mem_closed raw c ε
    have hv4 : 0 < vertexPoint raw c ε 4 := (hleft 4).trans_le (hv 4).1
    have hh := (div_le_iff₀ hv4).mp (hreal ε)
    dsimp [planeValue] at hh
    linarith
  have hpoint := affine_vertex_upper raw c (sideAlphaQ side) (sideBetaQ side) B hlin t ht
  have hcap := actual_candidate_le_plane raw side t
  have ht4 : 0 < t 4 := (hleft 4).trans_le (ht.1 4)
  apply (div_le_iff₀ ht4).mpr
  dsimp [residual, planeValue] at *
  linarith

end
end ImbalancedChen.P5ArbitraryMaskChildVertexRatio
