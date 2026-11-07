import ImbalancedChen.P1OriginalPrefixRowFiniteCheckSoundness

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

Bounded original-program semantics bridge, not a whole certificate.
Read-only source: certify_fourth_prefix_stronger.py,
SHA256 25069573985d30beae59a1a2a89ddeb79e56f696e78a5fae5153de0bb8bd378a.
Its N=204800, D=32*N, lower/diff/vlines/OLD and correlated delta tests
are modeled exactly below. The integer OLD order [1,3,7,5,6,B] is explicitly
permuted to the mathematical six order [1,3,7,B,5,6]. The singleton B piece
may be duplicated inside max: max x x=x, without changing its endpoint test.

No derivative, integration, floating cost, gain, or actual data is evaluated.
This module only supplies the correlated-gap conjunct, not the remaining
cube/gate/residual/domain/disjointness conjuncts of full geometry acceptance.
-/

namespace ImbalancedChen.P1OriginalFourthIntegerGapSemantics
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open scoped BigOperators

noncomputable section
open scoped Classical

/-- Source constant numerator is D-scaled; coefficient numerator is32-scaled. -/
structure IntegerAffine where
  constant : ℤ
  coefficient : Fin 4 → ℤ

def endpoint (x : Fin 4 → ℕ) : QEndpoint := fun i => (x i : ℚ) / 204800

def IntegerAffine.toAffine (a : IntegerAffine) : Affine :=
  ⟨(a.constant : ℚ) / 6553600, fun i => (a.coefficient i : ℚ) / 32⟩

def IntegerAffine.sub (a b : IntegerAffine) : IntegerAffine :=
  ⟨a.constant - b.constant, fun i => a.coefficient i - b.coefficient i⟩

/-- Source lower(): positive coefficients select lo, negative select hi.
The source skips coefficient0; the zero summand here is identical. -/
def IntegerAffine.lower (a : IntegerAffine) (lo hi : Fin 4 → ℕ) : ℤ :=
  a.constant + ∑ i, if 0 < a.coefficient i then a.coefficient i * (lo i : ℤ)
    else a.coefficient i * (hi i : ℤ)

theorem toAffine_sub (a b : IntegerAffine) :
    (a.sub b).toAffine = a.toAffine.sub b.toAffine := by
  apply congrArg₂ Affine.mk
  · simp only [IntegerAffine.toAffine, IntegerAffine.sub, Affine.sub, Int.cast_sub]
    ring
  · funext i
    simp only [IntegerAffine.toAffine, IntegerAffine.sub, Affine.sub, Int.cast_sub]
    ring

/-- Exact shared-affine endpoint scaling. Correlated coefficient differences
are formed before this lower-bound operation. No independent cap ranges occur. -/
theorem lower_scaled (a : IntegerAffine) (lo hi : Fin 4 → ℕ) :
    a.toAffine.lower (endpoint lo) (endpoint hi) = (a.lower lo hi : ℚ) / 6553600 := by
  have hterm (i : Fin 4) :
      (if 0 ≤ a.toAffine.coefficient i then a.toAffine.coefficient i * endpoint lo i
        else a.toAffine.coefficient i * endpoint hi i) =
      ((if 0 < a.coefficient i then a.coefficient i * (lo i : ℤ)
        else a.coefficient i * (hi i : ℤ) : ℤ) : ℚ) / 6553600 := by
    change (if 0 ≤ (a.coefficient i : ℚ) / 32 then
        (a.coefficient i : ℚ) / 32 * ((lo i : ℚ) / 204800)
      else (a.coefficient i : ℚ) / 32 * ((hi i : ℚ) / 204800)) = _
    by_cases hz : a.coefficient i = 0
    · simp [hz]
    by_cases hp : 0 < a.coefficient i
    · have hq : 0 ≤ (a.coefficient i : ℚ) / 32 := by
        have : (0 : ℚ) < (a.coefficient i : ℚ) := by exact_mod_cast hp
        positivity
      simp only [if_pos hq, if_pos hp]
      push_cast
      ring
    · have hn : a.coefficient i < 0 := by omega
      have hq : ¬ 0 ≤ (a.coefficient i : ℚ) / 32 := by
        have : (a.coefficient i : ℚ) < 0 := by exact_mod_cast hn
        linarith
      simp only [if_neg hq, if_neg hp]
      push_cast
      ring
  calc
    a.toAffine.lower (endpoint lo) (endpoint hi) =
        (a.constant : ℚ) / 6553600 + ∑ i,
          ((if 0 < a.coefficient i then a.coefficient i * (lo i : ℤ)
            else a.coefficient i * (hi i : ℤ) : ℤ) : ℚ) / 6553600 := by
      unfold Affine.lower
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (a.lower lo hi : ℚ) / 6553600 := by
      rw [← Finset.sum_div]
      simp only [IntegerAffine.lower, Int.cast_add, Int.cast_sum]
      ring

theorem lower_positive_iff (a : IntegerAffine) (lo hi : Fin 4 → ℕ) :
    (0 : ℚ) < a.toAffine.lower (endpoint lo) (endpoint hi) ↔ 0 < a.lower lo hi := by
  rw [lower_scaled]
  constructor
  · intro h
    have : (0 : ℚ) < (a.lower lo hi : ℚ) := by linarith
    exact_mod_cast this
  · intro h
    have : (0 : ℚ) < (a.lower lo hi : ℚ) := by exact_mod_cast h
    positivity

theorem correlated_pair_positive_iff (a b : IntegerAffine) (lo hi : Fin 4 → ℕ) :
    (0 : ℚ) < max (a.toAffine.lower (endpoint lo) (endpoint hi))
      (b.toAffine.lower (endpoint lo) (endpoint hi)) ↔
      (0 : ℤ) < max (a.lower lo hi) (b.lower lo hi) := by
  simp only [lt_max_iff, lower_positive_iff]

/-- Literal vlines numerator pair: (16N,16e), (57N/2,-48e). -/
def sourceTent (I : Finset (Fin 4)) (side : Bool) : IntegerAffine :=
  if side then ⟨5836800, fun i => if i ∈ I then -48 else 0⟩
  else ⟨3276800, fun i => if i ∈ I then 16 else 0⟩

theorem sourceTent_toAffine (I : Finset (Fin 4)) (side : Bool) :
    (sourceTent I side).toAffine = tentPlane I side := by
  cases side
  · apply congrArg₂ Affine.mk
    · norm_num [sourceTent, IntegerAffine.toAffine, tentPlane]
    · funext i
      by_cases hi : i ∈ I <;> norm_num [sourceTent, IntegerAffine.toAffine, tentPlane, hi]
  · apply congrArg₂ Affine.mk
    · norm_num [sourceTent, IntegerAffine.toAffine, tentPlane]
    · funext i
      by_cases hi : i ∈ I <;> norm_num [sourceTent, IntegerAffine.toAffine, tentPlane, hi]

/-- The original B(t3) line has numerator (153N/8,[0,0,-12,0]). -/
def sourceB : IntegerAffine := ⟨3916800, ![0,0,-12,0]⟩

/-- Six pieces in the existing mathematical order, before source-order reindexing. -/
def sourceOld (j : Fin 6) (side : Bool) : IntegerAffine :=
  if j = 3 then sourceB else sourceTent (oldMask j) side

theorem sourceOld_toAffine (j : Fin 6) (side : Bool) :
    (sourceOld j side).toAffine = oldPiece j side := by
  by_cases hj : j = 3
  · subst j
    apply congrArg₂ Affine.mk
    · norm_num [sourceOld, sourceB, IntegerAffine.toAffine, oldPiece]
    · funext i
      fin_cases i <;> norm_num [sourceOld, sourceB, IntegerAffine.toAffine, oldPiece]
  · simp only [sourceOld, oldPiece, if_neg hj]
    exact sourceTent_toAffine _ _

/-- Source OLD order [mask1,mask3,mask7,mask5,mask6,B], unchanged. -/
def pythonToCommon : Fin 6 → Fin 6 := ![0,1,2,4,5,3]
def commonToPython : Fin 6 → Fin 6 := ![0,1,2,5,3,4]

theorem pythonToCommon_commonToPython (j : Fin 6) :
    pythonToCommon (commonToPython j) = j := by
  fin_cases j <;> rfl

def programOldPiece (j : Fin 6) (side : Bool) : IntegerAffine :=
  sourceOld (pythonToCommon j) side

theorem programOldPiece_order (side : Bool) :
    (fun j => programOldPiece j side) =
      ![sourceTent {0} side, sourceTent {0,1} side, sourceTent {0,1,2} side,
        sourceTent {0,2} side, sourceTent {1,2} side, sourceB] := by
  funext j
  fin_cases j <;> rfl

/-- The min-old/min-new/max-oldpiece integer delta is positive exactly when
each correlated max here is positive. B is its original singleton piece. -/
def integerCorrelatedGapRows (raw : FourthWireRow) : Prop :=
  ∀ j : Fin 6, ∀ side : Bool, (0 : ℤ) <
    max (((sourceTent raw.toProducerRow.selected side).sub
      (programOldPiece j false)).lower raw.lo raw.hi)
      (((sourceTent raw.toProducerRow.selected side).sub
        (programOldPiece j true)).lower raw.lo raw.hi)

/-- Scalar version of the source's three reductions for delta:
min over the six old pieces, min over the two new lines, max over old lines.
The sixth old component's two identical B lines represent its singleton. -/
def integerDelta (raw : FourthWireRow) : ℤ :=
  Finset.univ.inf' (show (Finset.univ : Finset (Fin 6)).Nonempty from ⟨0, by simp⟩)
    (fun j => min
      (max (((sourceTent raw.toProducerRow.selected false).sub
        (programOldPiece j false)).lower raw.lo raw.hi)
        (((sourceTent raw.toProducerRow.selected false).sub
          (programOldPiece j true)).lower raw.lo raw.hi))
      (max (((sourceTent raw.toProducerRow.selected true).sub
        (programOldPiece j false)).lower raw.lo raw.hi)
        (((sourceTent raw.toProducerRow.selected true).sub
          (programOldPiece j true)).lower raw.lo raw.hi)))

theorem integerDelta_pos_iff (raw : FourthWireRow) :
    0 < integerDelta raw ↔ integerCorrelatedGapRows raw := by
  constructor
  · intro h j side
    have hj := (Finset.lt_inf'_iff _).mp h j (Finset.mem_univ j)
    cases side
    · exact hj.trans_le (min_le_left _ _)
    · exact hj.trans_le (min_le_right _ _)
  · intro h
    apply (Finset.lt_inf'_iff _).mpr
    intro j _hj
    exact lt_min (h j false) (h j true)

def rationalCorrelatedGapRows (raw : FourthWireRow) : Prop :=
  ∀ j : Fin 6, ∀ side : Bool, (0 : ℚ) <
    max (((tentPlane raw.toProducerRow.selected side).sub (oldPiece j false)).lower
      raw.toProducerRow.lower raw.toProducerRow.upper)
      (((tentPlane raw.toProducerRow.selected side).sub (oldPiece j true)).lower
        raw.toProducerRow.lower raw.toProducerRow.upper)

theorem literal_correlated_pair_positive_iff (raw : FourthWireRow) (j : Fin 6)
    (side : Bool) :
    (0 : ℚ) < max
      (((tentPlane raw.toProducerRow.selected side).sub (oldPiece j false)).lower
        raw.toProducerRow.lower raw.toProducerRow.upper)
      (((tentPlane raw.toProducerRow.selected side).sub (oldPiece j true)).lower
        raw.toProducerRow.lower raw.toProducerRow.upper) ↔
    (0 : ℤ) < max
      (((sourceTent raw.toProducerRow.selected side).sub (sourceOld j false)).lower raw.lo raw.hi)
      (((sourceTent raw.toProducerRow.selected side).sub (sourceOld j true)).lower raw.lo raw.hi) := by
  have h := correlated_pair_positive_iff
    ((sourceTent raw.toProducerRow.selected side).sub (sourceOld j false))
    ((sourceTent raw.toProducerRow.selected side).sub (sourceOld j true)) raw.lo raw.hi
  simpa only [toAffine_sub, sourceTent_toAffine, sourceOld_toAffine] using h

/-- The literal source integer correlated tests and the common finite
rational gap conjunct are equivalent, without a full geometry hypothesis. -/
theorem integerCorrelatedGapRows_iff (raw : FourthWireRow) :
    integerCorrelatedGapRows raw ↔ rationalCorrelatedGapRows raw := by
  constructor
  · intro h j side
    apply (literal_correlated_pair_positive_iff raw j side).mpr
    have hp := h (commonToPython j) side
    simpa only [programOldPiece, pythonToCommon_commonToPython] using hp
  · intro h j side
    exact (literal_correlated_pair_positive_iff raw (pythonToCommon j) side).mp
      (h (pythonToCommon j) side)

/-- A positive integer shared-affine delta supplies the genuine real
correlated gap. The cube, all gates and residual tests are still separate. -/
theorem integerCorrelatedGapRows_gapLower_pos (raw : FourthWireRow)
    (h : integerCorrelatedGapRows raw) :
    0 < gapLower raw.toProducerRow.selected raw.toProducerRow.lower raw.toProducerRow.upper := by
  have hq := (integerCorrelatedGapRows_iff raw).mp h
  unfold gapLower
  apply (Finset.lt_inf'_iff _).mpr
  intro j _hj
  apply lt_min
  · change (0 : ℝ) < max _ _
    exact_mod_cast hq j false
  · change (0 : ℝ) < max _ _
    exact_mod_cast hq j true

/-- The literal positive integer delta acceptance supplies precisely the
common real correlated-gap predicate, without assuming whole geometry. -/
theorem integerDelta_gapLower_pos (raw : FourthWireRow) (h : 0 < integerDelta raw) :
    0 < gapLower raw.toProducerRow.selected raw.toProducerRow.lower raw.toProducerRow.upper :=
  integerCorrelatedGapRows_gapLower_pos raw ((integerDelta_pos_iff raw).mp h)

end
end ImbalancedChen.P1OriginalFourthIntegerGapSemantics
