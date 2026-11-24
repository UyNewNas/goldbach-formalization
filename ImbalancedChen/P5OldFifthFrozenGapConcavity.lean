import ImbalancedChen.P5OldFifthFrozenUpperSurrogate

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED / ZERO FORMAL CREDIT.

One concrete analytic predecessor to the archived 32-vertex Jensen mean:
the exact saved-mask new cap M_P is concave, the parent-fixed fifteen-plane
old upper envelope is convex, and S5+2t5 is affine. Consequently the
script's child gap g_P=M_P-max(U_P,S5+2t5) is concave on the whole real
five-space, with the parent picks held fixed across all 64 children.

This does NOT yet turn the 32 vertex values into the UNIFORM child mean,
does not use d/A/B or prove the Q_b integral bound, and supplies no
numeric floor or original selected-owner claim.
-/

namespace ImbalancedChen.P5OldFifthFrozenGapConcavity

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P1OriginalVariableFourthContinuation
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1LiteralVariableFifthCompactSupplier
open P5OldFifthFrozenUpperSurrogate

abbrev Point := Fin 5 → ℝ

def mix (w : ℝ) (x y : Point) : Point :=
  fun i => (1 - w) * x i + w * y i

theorem mix_sum {ι : Type*} (S : Finset ι) (index : ι → Fin 5)
    (w : ℝ) (x y : Point) :
    (∑ i ∈ S, mix w x y (index i)) =
      (1 - w) * (∑ i ∈ S, x (index i)) +
        w * (∑ i ∈ S, y (index i)) := by
  simp only [mix, Finset.sum_add_distrib, Finset.mul_sum]

theorem A_mix (w a b : ℝ) :
    VariableEnvelope.A ((1 - w) * a + w * b) =
      (1 - w) * VariableEnvelope.A a + w * VariableEnvelope.A b := by
  dsimp [VariableEnvelope.A]
  ring

theorem C_mix (w a b : ℝ) :
    VariableEnvelope.C ((1 - w) * a + w * b) =
      (1 - w) * VariableEnvelope.C a + w * VariableEnvelope.C b := by
  dsimp [VariableEnvelope.C]
  ring

theorem B_mix (w a b : ℝ) :
    VariableEnvelope.B ((1 - w) * a + w * b) =
      (1 - w) * VariableEnvelope.B a + w * VariableEnvelope.B b := by
  dsimp [VariableEnvelope.B, VariableEnvelope.cap]
  ring

theorem pickedUpperPlane_mix (choice : Fin 3) (w a b : ℝ) :
    pickedUpperPlane choice ((1 - w) * a + w * b) =
      (1 - w) * pickedUpperPlane choice a +
        w * pickedUpperPlane choice b := by
  fin_cases choice
  · simpa [pickedUpperPlane] using A_mix w a b
  · simpa [pickedUpperPlane] using C_mix w a b
  · simp [pickedUpperPlane]
    ring

private theorem v_le_A (s : ℝ) : VariableEnvelope.v s ≤ VariableEnvelope.A s := by
  simpa [VariableEnvelope.v_eq_min] using
    (min_le_left (VariableEnvelope.A s) (VariableEnvelope.C s))

private theorem v_le_C (s : ℝ) : VariableEnvelope.v s ≤ VariableEnvelope.C s := by
  simpa [VariableEnvelope.v_eq_min] using
    (min_le_right (VariableEnvelope.A s) (VariableEnvelope.C s))

/-- The global min of the two affine new-cap planes is concave. -/
theorem v_concave_pair (w a b : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    (1 - w) * VariableEnvelope.v a + w * VariableEnvelope.v b ≤
      VariableEnvelope.v ((1 - w) * a + w * b) := by
  have h1 : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  have hA : (1 - w) * VariableEnvelope.v a + w * VariableEnvelope.v b ≤
      VariableEnvelope.A ((1 - w) * a + w * b) := by
    rw [A_mix]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (v_le_A a) h1)
      (mul_le_mul_of_nonneg_left (v_le_A b) hw0)
  have hC : (1 - w) * VariableEnvelope.v a + w * VariableEnvelope.v b ≤
      VariableEnvelope.C ((1 - w) * a + w * b) := by
    rw [C_mix]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (v_le_C a) h1)
      (mul_le_mul_of_nonneg_left (v_le_C b) hw0)
  rw [VariableEnvelope.v_eq_min]
  exact le_min hA hC

theorem oldSubsetSum_mix (I : OldMask) (w : ℝ) (x y : Point) :
    oldSubsetSum I (mix w x y) =
      (1 - w) * oldSubsetSum I x + w * oldSubsetSum I y := by
  exact mix_sum I (fun i : Fin 4 => i.castSucc) w x y

theorem newMaskSum_mix (raw : FifthWireRow) (w : ℝ) (x y : Point) :
    (∑ i ∈ maskSlots 5 raw.mask.toNat, mix w x y i) =
      (1 - w) * (∑ i ∈ maskSlots 5 raw.mask.toNat, x i) +
        w * (∑ i ∈ maskSlots 5 raw.mask.toNat, y i) := by
  exact mix_sum (maskSlots 5 raw.mask.toNat) id w x y

theorem rawCandidate_zero_concave_pair (raw : FifthWireRow)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (x y : Point) :
    (1 - w) * rawCandidate 0 raw x + w * rawCandidate 0 raw y ≤
      rawCandidate 0 raw (mix w x y) := by
  simp only [rawCandidate, mul_zero, sub_zero]
  rw [newMaskSum_mix]
  exact v_concave_pair w _ _ hw0 hw1

/-- All 15 fixed old upper planes, plus the B(t3) seed, form a convex max. -/
theorem frozenParentUpper_convex_pair (picks : ParentPicks)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (x y : Point) :
    frozenParentUpper picks (mix w x y) ≤
      (1 - w) * frozenParentUpper picks x +
        w * frozenParentUpper picks y := by
  have h1 : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  unfold frozenParentUpper
  apply finiteMax_le
  · have hx := finiteMax_seed_le oldMasks (fun _ => True)
      (fun I => pickedUpperPlane (picks I) (oldSubsetSum I x))
      (VariableEnvelope.B (x 2))
    have hy := finiteMax_seed_le oldMasks (fun _ => True)
      (fun I => pickedUpperPlane (picks I) (oldSubsetSum I y))
      (VariableEnvelope.B (y 2))
    change VariableEnvelope.B ((1 - w) * x 2 + w * y 2) ≤ _
    rw [B_mix]
    exact add_le_add (mul_le_mul_of_nonneg_left hx h1)
      (mul_le_mul_of_nonneg_left hy hw0)
  · intro I hI _
    have hx := finiteMax_row_le oldMasks (fun _ => True)
      (fun J => pickedUpperPlane (picks J) (oldSubsetSum J x))
      (VariableEnvelope.B (x 2)) I hI trivial
    have hy := finiteMax_row_le oldMasks (fun _ => True)
      (fun J => pickedUpperPlane (picks J) (oldSubsetSum J y))
      (VariableEnvelope.B (y 2)) I hI trivial
    rw [oldSubsetSum_mix, pickedUpperPlane_mix]
    exact add_le_add (mul_le_mul_of_nonneg_left hx h1)
      (mul_le_mul_of_nonneg_left hy hw0)

def ownCubeThreshold (t : Point) : ℝ := (∑ i : Fin 5, t i) + 2 * t 4

theorem ownCubeThreshold_mix (w : ℝ) (x y : Point) :
    ownCubeThreshold (mix w x y) =
      (1 - w) * ownCubeThreshold x + w * ownCubeThreshold y := by
  unfold ownCubeThreshold
  rw [mix_sum (Finset.univ : Finset (Fin 5)) id]
  dsimp [mix]
  ring

def frozenCeiling (picks : ParentPicks) (t : Point) : ℝ :=
  max (frozenParentUpper picks t) (ownCubeThreshold t)

theorem frozenCeiling_convex_pair (picks : ParentPicks)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (x y : Point) :
    frozenCeiling picks (mix w x y) ≤
      (1 - w) * frozenCeiling picks x + w * frozenCeiling picks y := by
  have h1 : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  unfold frozenCeiling
  apply max_le
  · exact (frozenParentUpper_convex_pair picks w hw0 hw1 x y).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) h1)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hw0))
  · rw [ownCubeThreshold_mix]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (le_max_right _ _) h1)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hw0)

/-- Exactly the script's unbuffered child gap, before vertex averaging. -/
def frozenGap (picks : ParentPicks) (raw : FifthWireRow) (t : Point) : ℝ :=
  rawCandidate 0 raw t - frozenCeiling picks t

theorem frozenGap_concave_pair (picks : ParentPicks) (raw : FifthWireRow)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (x y : Point) :
    (1 - w) * frozenGap picks raw x + w * frozenGap picks raw y ≤
      frozenGap picks raw (mix w x y) := by
  have hnew := rawCandidate_zero_concave_pair raw w hw0 hw1 x y
  have hold := frozenCeiling_convex_pair picks w hw0 hw1 x y
  unfold frozenGap
  calc
    (1 - w) * (rawCandidate 0 raw x - frozenCeiling picks x) +
        w * (rawCandidate 0 raw y - frozenCeiling picks y) =
      ((1 - w) * rawCandidate 0 raw x + w * rawCandidate 0 raw y) -
        ((1 - w) * frozenCeiling picks x + w * frozenCeiling picks y) := by ring
    _ ≤ rawCandidate 0 raw (mix w x y) -
          frozenCeiling picks (mix w x y) := sub_le_sub hnew hold

end
end ImbalancedChen.P5OldFifthFrozenGapConcavity
