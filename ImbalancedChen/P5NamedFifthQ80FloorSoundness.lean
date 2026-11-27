import ImbalancedChen.P5NamedFifthChildSpecificRatio
import ImbalancedChen.P5OriginalSharpDirectedLog
import ImbalancedChen.P5NamedAllChildrenSelectedJensen
import ImbalancedChen.P2DirectedLogRounding

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
Symbolic directed-log/Q80 soundness on the FULL two-parent 128-child
family, using each actual improved child b, actual signed integer d,
and the original sharp 1/9 upper tail. Negative/zero d uses exactly zero.
No checker execution, integer total, adopted full J5 or target reserve is
assumed. The final theorem keeps the original selected-owner clipping
charged through the same actual omitted/retained-volume reserve.
-/
namespace ImbalancedChen.P5NamedFifthQ80FloorSoundness

open scoped BigOperators
open P5NamedFifthPayloadSemantics P5NamedFifthAllChildren
open P5NamedFifthChildSpecificRatio P5OriginalSharpDirectedLog
open P5OldFifthExact64ChildTiling
open P5OldFifthChildGapIntegral P5OldFifthPointwiseQ
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateBarycentric (childVolume)
open P5OldFifthActualChildJensenIntegral
open P5ChildSelectedOwnerJensenReserve
open P5NamedAllChildrenSelectedJensen
open P1OriginalPrefixRowDecodeSoundness
open P1FifthPositivePartActualOwner
open ImbalancedChen.Certificates.P2DirectedLogRounding

def lower3Q (x : ℚ) : ℚ := 2 * (x + x ^ 3 / 3 + x ^ 5 / 5)
def upper4Q (x : ℚ) : ℚ :=
  2 * (x + x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 / 7 + x ^ 9 / (9 * (1 - x ^ 2)))

def directedQQ (b e : ℚ) : ℚ :=
  let a := b - e
  let z := e / (2 * (b - 1) - e)
  let y := (a - 2) / a
  (a * lower3Q z - e * upper4Q y) / (a * b)

/-- Original exact 4*n*prod(width)/(h5*prod(hi)) prefactor. -/
def prefactorQ (b : Bool) (c : ChildIndex) : ℚ :=
  (4 * 1600 * ∏ i : Fin 5, (width i : ℚ)) /
    ((childRightNumer (namedParent b) c 4 : ℚ) *
      ∏ i : Fin 5, (childRightNumer (namedParent b) c i : ℚ))

def childMinorantQ (b : Bool) (c : ChildIndex) : ℚ :=
  prefactorQ b c * directedQQ (childBQ b c) (childEQ b c)

def childFloorZ (b : Bool) (c : ChildIndex) : ℤ :=
  if 0 < sourceChildD (namedParent b) c then
    Int.floor (childMinorantQ b c * dyadicScale 80) else 0

def childFloorQ (b : Bool) (c : ChildIndex) : ℚ :=
  (childFloorZ b c : ℚ) / dyadicScale 80

/-- Directed downward rounding loses less than 2^-80 on the actual
rational expression. No historical stored floor provenance is asserted. -/
theorem childFloorQ_le_active_minorant (b : Bool) (c : ChildIndex)
    (hd : 0 < sourceChildD (namedParent b) c) :
    childFloorQ b c ≤ childMinorantQ b c := by
  simpa [childFloorQ, childFloorZ, hd, roundDown] using
    roundDown_le 80 (childMinorantQ b c)

noncomputable section
open Set MeasureTheory
open scoped Classical

private theorem cast_lower3Q (x : ℚ) : (lower3Q x : ℝ) = lower3 (x : ℝ) := by
  simp [lower3Q, lower3]
private theorem cast_upper4Q (x : ℚ) : (upper4Q x : ℝ) = upper4 (x : ℝ) := by
  simp [upper4Q, upper4]

/-- No logarithmic endpoint is assumed: the real-log bound is inherited
from the proved original sharp directed expression. -/
theorem directedQQ_le_Q (b e : ℚ) (hb : 2 < b) (he0 : 0 ≤ e) (he : e ≤ b - 2) :
    (directedQQ b e : ℝ) ≤ Q (b : ℝ) (e : ℝ) := by
  have h := directed_Q_lower (b : ℝ) (e : ℝ)
    (by exact_mod_cast hb) (by exact_mod_cast he0) (by exact_mod_cast he)
  simpa [directedQQ, cast_lower3Q, cast_upper4Q] using h

theorem cast_prefactorQ (b : Bool) (c : ChildIndex) :
    (prefactorQ b c : ℝ) =
      childVolume (namedParent b) c * childPrefactor (namedParent b) c := by
  symm
  simpa [prefactorQ] using child_volume_mul_prefactor_integerScale
    (namedParent b) c (named_childLeft_pos b c)

private theorem upper4Q_le_scaled (a : ℚ) (ha2 : 2 ≤ a) (ha4 : a ≤ 4) :
    upper4Q ((a - 2) / a) ≤ 2 * a / (a + 2) := by
  have ha : 0 < a := by linarith
  let y : ℚ := (a - 2) / a
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr ha2) ha.le
  have hyhalf : y ≤ 1 / 2 := by
    apply (div_le_iff₀ ha).mpr
    linarith
  have hden : 0 < 1 - y ^ 2 := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hyhalf)]
  have hgap : 2 * y - (1 - y ^ 2) * upper4Q y =
      4 / 3 * y ^ 3 + 4 / 15 * y ^ 5 + 4 / 35 * y ^ 7 + 4 / 63 * y ^ 9 := by
    unfold upper4Q
    field_simp [ne_of_gt hden] <;> ring
  have hgap0 : 0 ≤ 4 / 3 * y ^ 3 + 4 / 15 * y ^ 5 +
      4 / 35 * y ^ 7 + 4 / 63 * y ^ 9 := by positivity
  have hupper : upper4Q y ≤ 2 * y / (1 - y ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hgap]
  have htwo : 0 < 2 - y := by linarith
  have hfrac : 2 * y / (1 - y ^ 2) ≤ 2 / (2 - y) := by
    apply (div_le_div_iff₀ hden htwo).mpr
    nlinarith
  have hscale : 2 / (2 - y) = 2 * a / (a + 2) := by
    have hdeneq : 2 - y = (a + 2) / a := by
      dsimp only [y]
      field_simp [ha.ne'] <;> ring
    rw [hdeneq]
    field_simp [ha.ne', show a + 2 ≠ 0 by linarith] <;> ring
  exact hupper.trans (hfrac.trans_eq hscale)

private theorem directedQQ_nonneg (b e : ℚ)
    (hb2 : 2 < b) (hb4 : b ≤ 4) (he0 : 0 ≤ e) (he : e ≤ b - 2) :
    0 ≤ directedQQ b e := by
  let a : ℚ := b - e
  let D : ℚ := 2 * (b - 1) - e
  let z : ℚ := e / D
  let y : ℚ := (a - 2) / a
  have ha2 : 2 ≤ a := by dsimp only [a]; linarith
  have ha4 : a ≤ 4 := by dsimp only [a]; linarith
  have ha0 : 0 ≤ a := by linarith
  have hD : 0 < D := by dsimp only [D]; linarith
  have hDa : D ≤ a + 2 := by dsimp only [D, a]; linarith
  have hz : 0 ≤ z := div_nonneg he0 hD.le
  have hlow : 2 * z ≤ lower3Q z := by
    unfold lower3Q
    nlinarith [pow_nonneg hz 3, pow_nonneg hz 5]
  have hfrac : 2 * a / (a + 2) ≤ 2 * a / D :=
    div_le_div_of_nonneg_left (by positivity) hD hDa
  have hu : upper4Q y ≤ 2 * a / D :=
    (upper4Q_le_scaled a ha2 ha4).trans hfrac
  have humul := mul_le_mul_of_nonneg_left hu he0
  have hlmul := mul_le_mul_of_nonneg_left hlow ha0
  have hscale : a * (2 * z) = e * (2 * a / D) := by
    dsimp only [z]
    ring
  rw [hscale] at hlmul
  have hnum : 0 ≤ a * lower3Q z - e * upper4Q y := by linarith
  change 0 ≤ (a * lower3Q z - e * upper4Q y) / (a * b)
  exact div_nonneg hnum (mul_nonneg ha0 (by linarith))

/-- Signs derived from the SAME actual geometry and original directed
expression, without recomputing the original child d values. -/
theorem all_prefactors_nonneg : ∀ b : Bool, ∀ c : ChildIndex, 0 ≤ prefactorQ b c := by
  intro b c
  have hr : (0 : ℝ) ≤ (prefactorQ b c : ℝ) := by
    rw [cast_prefactorQ]
    exact mul_nonneg (P5OldFifthChildQJensen.childVolume_pos (namedParent b) c).le
      (childPrefactor_nonneg (namedParent b) c (named_childLeft_pos b c))
  exact_mod_cast hr

theorem all_active_minorants_nonneg :
    ∀ b : Bool, ∀ c : ChildIndex,
      0 < sourceChildD (namedParent b) c → 0 ≤ childMinorantQ b c := by
  intro b c hd
  have he := all_active_e_ranges b c hd.le
  exact mul_nonneg (all_prefactors_nonneg b c)
    (directedQQ_nonneg (childBQ b c) (childEQ b c)
      (all_child_ratio_ranges b c).1 (all_child_ratio_ranges b c).2.2 he.1 he.2)

theorem childFloorQ_nonneg (b : Bool) (c : ChildIndex) : 0 ≤ childFloorQ b c := by
  by_cases hd : 0 < sourceChildD (namedParent b) c
  · have hn : 0 ≤ Int.floor (childMinorantQ b c * dyadicScale 80) :=
      Int.floor_nonneg.mpr (mul_nonneg (all_active_minorants_nonneg b c hd)
        (dyadicScale_pos 80).le)
    unfold childFloorQ childFloorZ
    rw [if_pos hd]
    exact div_nonneg (by exact_mod_cast hn) (dyadicScale_pos 80).le
  · simp [childFloorQ, childFloorZ, hd]

/-- Original zero fallback and actual improved b_C are both preserved.
Every sign/range/d-identity obligation is supplied from the concrete family. -/
theorem childFloorQ_le_actual_certified_Jensen (b : Bool) (c : ChildIndex) :
    (childFloorQ b c : ℝ) ≤
      certifiedChildJensen (sourcePicks (namedParent b)) (namedParent b) c
        (childBQ b c) (sourceChildD (namedParent b) c) := by
  by_cases hd : 0 < sourceChildD (namedParent b) c
  · have hr : (childFloorQ b c : ℝ) ≤ (childMinorantQ b c : ℝ) := by
      exact_mod_cast childFloorQ_le_active_minorant b c hd
    have he := all_active_e_ranges b c hd.le
    have hQ := directedQQ_le_Q (childBQ b c) (childEQ b c)
      (all_child_ratio_ranges b c).1 he.1 he.2
    have hp : (0 : ℝ) ≤ (prefactorQ b c : ℝ) := by
      exact_mod_cast all_prefactors_nonneg b c
    have hmul := mul_le_mul_of_nonneg_left hQ hp
    rw [certifiedChildJensen, if_pos hd.le]
    calc
      _ ≤ (childMinorantQ b c : ℝ) := hr
      _ ≤ (prefactorQ b c : ℝ) * Q (childBQ b c) (childEQ b c) := by
        simpa [childMinorantQ] using hmul
      _ = _ := by rw [cast_prefactorQ, childEQ_eq_actual_scale]
  · by_cases hz : sourceChildD (namedParent b) c = 0
    · simp [childFloorQ, childFloorZ, hd, certifiedChildJensen, hz, Q]
    · have hneg : ¬ 0 ≤ sourceChildD (namedParent b) c := by omega
      simp [childFloorQ, childFloorZ, hd, certifiedChildJensen, hneg]

/-- All128 actual floors have whole-child kernel semantics, with no
assumed child-specific hnew, e interval, integer d or logarithm bound. -/
theorem childFloorQ_le_whole_actual_kernel (b : Bool) (c : ChildIndex) :
    (childFloorQ b c : ℝ) ≤
      ∫ t in childBox (namedParent b) c,
        P5OldFifthFrozenUpperSurrogate.frozenUpperPositiveKernel
          (sourcePicks (namedParent b)) (namedParent b) t := by
  have hb2 : (2 : ℝ) < (childBQ b c : ℝ) := by
    exact_mod_cast (all_child_ratio_ranges b c).1
  have hb4 : (childBQ b c : ℝ) ≤ 4 := by
    exact_mod_cast (all_child_ratio_ranges b c).2.2
  exact (childFloorQ_le_actual_certified_Jensen b c).trans
    (certifiedChildJensen_le_whole (sourcePicks (namedParent b)) (namedParent b) c
      (named_childLeft_pos b c) hb2 hb4 (actual_child_new_ratio b c)
      (sourceChildD (namedParent b) c) (namedChild_hd b c))

/-- Complete symbolic 64-child floor sum minus the SAME actual owner
reserve. Child-specific improved b values may vary with c. No common
parent b is silently substituted, and no unclipped floor is relabelled
as an owner-clipped gain. -/
theorem all64_Q80_floors_minus_reserve_le_original_owner_sum
    (b : Bool) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Owner m)) :
    (∑ c : ChildIndex, (childFloorQ b c : ℝ)) -
        namedReserveTotal b e chi m omega J5 ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral (namedParent b) e chi m omega j := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ChildIndex)) (fun c _ => by
    have hb2 : (2 : ℝ) < (childBQ b c : ℝ) := by
      exact_mod_cast (all_child_ratio_ranges b c).1
    have hb4 : (childBQ b c : ℝ) ≤ 4 := by
      exact_mod_cast (all_child_ratio_ranges b c).2.2
    exact (sub_le_sub_right (childFloorQ_le_actual_certified_Jensen b c)
      (childOwnerReserve (namedParent b) c e chi m omega J5)).trans
      (certified_child_sub_reserve_le_clipped_owner_sum
        (sourcePicks (namedParent b)) (namedParent b) (named_grid b)
        (named_positive_indices b) (named_upper_bound b) c hb2 hb4
        (actual_child_new_ratio b c) (sourceChildD (namedParent b) c)
        (namedChild_hd b c) e chi m omega J5))
  rw [Finset.sum_comm] at hs
  have heq :
      (∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        ∑ c : ChildIndex, ∫ t in childOwnerDomain (namedParent b) c e chi m omega j,
          literalPositiveRawKernel e (namedParent b) t) =
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral (namedParent b) e chi m omega j := by
    apply Finset.sum_congr rfl
    intro j _
    exact (positive_rawOwnerIntegral_eq_sum_64_children (namedParent b)
      (named_grid b) (named_positive_indices b) e chi m omega j).symm
  rw [heq] at hs
  simpa only [namedReserveTotal, Finset.sum_sub_distrib] using hs

end
end ImbalancedChen.P5NamedFifthQ80FloorSoundness
