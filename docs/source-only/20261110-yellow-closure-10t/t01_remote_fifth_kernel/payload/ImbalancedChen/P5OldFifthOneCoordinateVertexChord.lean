import ImbalancedChen.P5OldFifthFrozenGapConcavity
import ImbalancedChen.P5OldFifthExact64ChildTiling

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED / ZERO FORMAL CREDIT.

One exact coordinate of the 5-dimensional child vertex interpolation.
The child endpoints are the ACTUAL grid1600 integer numerators from the
saved (2,2,2,2,4) subdivision, not generic rectangle parameters.
For t inside that half-open child, its coordinate barycentric fraction
lies in [0,1], t is the mixture of its two coordinate endpoint points,
and the Phase8 concrete frozen gap satisfies the corresponding chord.

This source does not yet iterate five coordinates, integrate the 32
product barycentric weights, or claim the archived integer d bound.
-/

namespace ImbalancedChen.P5OldFifthOneCoordinateVertexChord

noncomputable section
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity

abbrev Point := Fin 5 → ℝ

def childLeft (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) : ℝ :=
  (childLeftNumer raw c i : ℝ) / 1600

def childRight (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) : ℝ :=
  (childRightNumer raw c i : ℝ) / 1600

theorem child_span (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) :
    childRight raw c i - childLeft raw c i = (width i : ℝ) / 1600 := by
  simp [childRight, childLeft, childRightNumer]
  ring

theorem child_span_pos (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) :
    0 < childRight raw c i - childLeft raw c i := by
  rw [child_span]
  have hw : 0 < width i := by fin_cases i <;> norm_num [width]
  exact div_pos (by exact_mod_cast hw) (by norm_num)

def coordinateFraction (raw : FifthWireRow) (c : ChildIndex)
    (i : Fin 5) (t : Point) : ℝ :=
  (t i - childLeft raw c i) /
    (childRight raw c i - childLeft raw c i)

theorem coordinateFraction_bounds (raw : FifthWireRow) (c : ChildIndex)
    (i : Fin 5) (t : Point) (ht : t ∈ childBox raw c) :
    0 ≤ coordinateFraction raw c i ∧ coordinateFraction raw c i ≤ 1 := by
  have hi : childLeft raw c i ≤ t i ∧ t i < childRight raw c i := ht i
  have hs := child_span_pos raw c i
  constructor
  · exact div_nonneg (sub_nonneg.mpr hi.1) hs.le
  · exact (div_le_one hs).2 (by linarith [hi.2])

def lowerEndpointPoint (raw : FifthWireRow) (c : ChildIndex)
    (i : Fin 5) (t : Point) : Point :=
  Function.update t i (childLeft raw c i)

def upperEndpointPoint (raw : FifthWireRow) (c : ChildIndex)
    (i : Fin 5) (t : Point) : Point :=
  Function.update t i (childRight raw c i)

/-- The right endpoint need not belong to the half-open child, but the
frozen gap is globally defined and can be evaluated at that closure point. -/
theorem coordinate_mix_endpoints (raw : FifthWireRow) (c : ChildIndex)
    (i : Fin 5) (t : Point) :
    mix (coordinateFraction raw c i t)
      (lowerEndpointPoint raw c i t) (upperEndpointPoint raw c i t) = t := by
  funext k
  by_cases hk : k = i
  · subst k
    simp only [mix, lowerEndpointPoint, upperEndpointPoint, Function.update_same]
    let a := childLeft raw c i
    let b := childRight raw c i
    have hab : b - a ≠ 0 := (child_span_pos raw c i).ne'
    change (1 - coordinateFraction raw c i t) * a +
      coordinateFraction raw c i t * b = t i
    calc
      (1 - coordinateFraction raw c i t) * a +
          coordinateFraction raw c i t * b =
        a + coordinateFraction raw c i t * (b - a) := by ring
      _ = t i := by
        change a + ((t i - a) / (b - a)) * (b - a) = t i
        field_simp [hab]
        ring
  · simp [mix, lowerEndpointPoint, upperEndpointPoint, hk]
    ring

/-- One genuine coordinate chord for the exact saved child and the
script's frozen concave gap. No integral inequality is assumed. -/
theorem frozenGap_oneCoordinateChord (picks : ParentPicks)
    (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5)
    (t : Point) (ht : t ∈ childBox raw c) :
    (1 - coordinateFraction raw c i t) *
        frozenGap picks raw (lowerEndpointPoint raw c i t) +
      coordinateFraction raw c i t *
        frozenGap picks raw (upperEndpointPoint raw c i t) ≤
          frozenGap picks raw t := by
  have hq := coordinateFraction_bounds raw c i t ht
  have h := frozenGap_concave_pair picks raw
    (coordinateFraction raw c i t) hq.1 hq.2
    (lowerEndpointPoint raw c i t) (upperEndpointPoint raw c i t)
  rw [coordinate_mix_endpoints raw c i t] at h
  exact h

end
end ImbalancedChen.P5OldFifthOneCoordinateVertexChord
