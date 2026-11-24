import ImbalancedChen.P1FifthPositivePartActualOwner

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED / ZERO FORMAL CREDIT.

The archived fifth Jensen evaluator does not use the exact old15 profile:
it freezes one of three globally valid affine upper planes for each of
the fifteen nonempty old fourth masks at the original grid400 parent.
This source defines that SAME parent-fixed envelope and proves its
positive-part kernel is pointwise below the root's positive-part literal
kernel at e=0. It is a necessary direction for the archived Jensen floor.

The substantive whole-child vertex/Jensen/Q_b lower bound and the
rational exact_floor certificate are NOT claimed here. Nor is the
surrogate asserted equal to the literal positive-part kernel: a chosen
upper plane may be strictly above the true old v branch.
-/

namespace ImbalancedChen.P5OldFifthFrozenUpperSurrogate

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P1OriginalVariableFourthContinuation
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1LiteralVariableFifthCompactSupplier
open P1FifthUnitBoxLiteralGainLower
open P1FifthPositivePartActualOwner

abbrev Point := Fin 5 → ℝ
abbrev OldMask := Finset (Fin 4)
abbrev ParentPicks := OldMask → Fin 3

/-- The three script choices: the two affine sides of v and its global cap. -/
def pickedUpperPlane (choice : Fin 3) (s : ℝ) : ℝ :=
  if choice.val = 0 then VariableEnvelope.A s
  else if choice.val = 1 then VariableEnvelope.C s
  else VariableEnvelope.cap

theorem v_le_pickedUpperPlane (choice : Fin 3) (s : ℝ) :
    VariableEnvelope.v s ≤ pickedUpperPlane choice s := by
  fin_cases choice
  · simpa [pickedUpperPlane, VariableEnvelope.v_eq_min] using
      (min_le_left (VariableEnvelope.A s) (VariableEnvelope.C s))
  · simpa [pickedUpperPlane, VariableEnvelope.v_eq_min] using
      (min_le_right (VariableEnvelope.A s) (VariableEnvelope.C s))
  · simpa [pickedUpperPlane] using VariableEnvelope.v_le_cap s

/-- The parent picks are constant on all 64 children, exactly as archived.
The seed B(t2)=153/256-3t2/8 is the unselected old fourth branch. -/
def frozenParentUpper (picks : ParentPicks) (t : Point) : ℝ :=
  finiteMax oldMasks (fun _ => True)
    (fun I => pickedUpperPlane (picks I) (oldSubsetSum I t))
    (VariableEnvelope.B (t 2))

theorem rawFourth_le_frozenParentUpper (picks : ParentPicks) (t : Point) :
    rawFourth t ≤ frozenParentUpper picks t := by
  unfold rawFourth
  apply finiteMax_le
  · exact finiteMax_seed_le oldMasks (fun _ => True)
      (fun I => pickedUpperPlane (picks I) (oldSubsetSum I t))
      (VariableEnvelope.B (t 2))
  · intro I hI _
    exact (v_le_pickedUpperPlane (picks I) (oldSubsetSum I t)).trans
      (finiteMax_row_le oldMasks (fun _ => True)
        (fun J => pickedUpperPlane (picks J) (oldSubsetSum J t))
        (VariableEnvelope.B (t 2)) I hI trivial)

/-- Concrete archived old-plane surrogate, before the Jensen Q_b minorant.
The new level is the actual saved-mask rawCandidate at zero buffer. -/
def frozenUpperPositiveKernel (picks : ParentPicks) (raw : FifthWireRow)
    (t : Point) : ℝ :=
  max 0
    ((primeOwnCubeGatedProfile (rawCandidate 0 raw t) t -
        primeOwnCubeGatedProfile (frozenParentUpper picks t) t) *
      ∏ i, 1 / t i)

theorem frozenUpperPositiveKernel_nonneg (picks : ParentPicks)
    (raw : FifthWireRow) (t : Point) :
    0 ≤ frozenUpperPositiveKernel picks raw t := by
  exact le_max_left _ _

/-- The archived upper-plane choice can only REDUCE the positive gain.
No equality between the surrogate and literalPositiveRawKernel is used. -/
theorem frozenUpperPositiveKernel_le_literalPositiveRawKernel
    (picks : ParentPicks) (raw : FifthWireRow) (t : Point)
    (ht : ∀ i : Fin 5, 0 < t i) :
    frozenUpperPositiveKernel picks raw t ≤
      literalPositiveRawKernel 0 raw t := by
  have hlevel : rawFourth t ≤ frozenParentUpper picks t :=
    rawFourth_le_frozenParentUpper picks t
  have hprofile := p1PrimeOwnCubeGatedProfile_mono t
    (ht (Fin.last 4)) hlevel
  have hweight : 0 ≤ ∏ i : Fin 5, 1 / t i :=
    Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le)
  have hdiff :
      (primeOwnCubeGatedProfile (rawCandidate 0 raw t) t -
          primeOwnCubeGatedProfile (frozenParentUpper picks t) t) *
        (∏ i : Fin 5, 1 / t i) ≤
      (primeOwnCubeGatedProfile (rawCandidate 0 raw t) t -
          primeOwnCubeGatedProfile (old5 0 t) t) *
        (∏ i : Fin 5, 1 / t i) := by
    apply mul_le_mul_of_nonneg_right _ hweight
    have hold : old5 0 t = rawFourth t := by simp [old5]
    rw [hold]
    exact sub_le_sub_left hprofile _
  unfold frozenUpperPositiveKernel literalPositiveRawKernel literalRawKernel
  exact max_le_max le_rfl hdiff

end
end ImbalancedChen.P5OldFifthFrozenUpperSurrogate
