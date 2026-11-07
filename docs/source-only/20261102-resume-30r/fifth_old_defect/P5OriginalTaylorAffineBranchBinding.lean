import ImbalancedChen.P1OriginalFifthCorrelatedRawBoxGates
import ImbalancedChen.P5OriginalTaylorActualSignedKernel

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original pilot's active-side and signed affine-dominance checks imply
the required structural identity with the ACTUAL fifteen-tent-plus-W
rawFourth.  Affine evaluation, exact coefficient-sign extrema and the
original tent planes are reused from the existing correlated gate source.

No equality between a chosen affine plane and rawFourth is a premise.
No equality between rawFourth and the dynamic licensed ancestor is used.
The source-only conversion below DOES NOT supply BranchFacts for the
actual archive, and proves no saved Taylor floor or oldBranchDefect bound.
-/
namespace ImbalancedChen.P5OriginalTaylorAffineBranchBinding
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthCorrelatedRawBoxGates

abbrev OldMask := Finset (Fin 4)
abbrev OldSides := OldMask → Bool

def liftOldMask (I : OldMask) : Finset (Fin 5) := I.image Fin.castSucc

/-- Original `active`: ascending is tested first, with its closed endpoint;
descending is tested second. A box crossing the switch returns none. -/
def activeSide (raw : FifthWireRow) (I : Finset (Fin 5)) : Option Bool :=
  if (∑ i ∈ I, raw.upper i) ≤ 25 / 128 then some false
  else if 25 / 128 ≤ ∑ i ∈ I, raw.lower i then some true
  else none

def ActiveOn (raw : FifthWireRow) (I : Finset (Fin 5)) (side : Bool) : Prop :=
  if side then 25 / 128 ≤ ∑ i ∈ I, raw.lower i
  else (∑ i ∈ I, raw.upper i) ≤ 25 / 128

def inheritedWPlane : Affine5 :=
  (constantAffine (153 / 256)).add (indicatorAffine (-3 / 8) {2})

/-- `none` is the original inherited W; `some I` is a nonempty old mask.
Membership is a separate finite source condition, not a new old profile. -/
def selectedOldPlane (sides : OldSides) : Option OldMask → Affine5
  | none => inheritedWPlane
  | some I => tentPlane (liftOldMask I) (sides I)

def newPlane (raw : FifthWireRow) (side : Bool) : Affine5 :=
  tentPlane (maskSlots 5 raw.mask.toNat) side

/-- These are primitive rational branch/dominance checks from the pilot.
They do not contain a real-integral, a floor licence, or a cap equality. -/
structure BranchFacts (raw : FifthWireRow) (newSide : Bool)
    (oldSides : OldSides) (selected : Option OldMask) : Prop where
  new_active : activeSide raw (maskSlots 5 raw.mask.toNat) = some newSide
  old_active : ∀ I ∈ P1LiteralVariableFifthCompactSupplier.oldMasks,
    activeSide raw (liftOldMask I) = some (oldSides I)
  selected_present : match selected with
    | none => True
    | some I => I ∈ P1LiteralVariableFifthCompactSupplier.oldMasks
  dominates_W : 0 ≤ ((selectedOldPlane oldSides selected).sub inheritedWPlane).lower
    raw.lower raw.upper
  dominates_old : ∀ I ∈ P1LiteralVariableFifthCompactSupplier.oldMasks,
    0 ≤ ((selectedOldPlane oldSides selected).sub
      (tentPlane (liftOldMask I) (oldSides I))).lower raw.lower raw.upper
  strict_gain : 0 < ((newPlane raw newSide).sub
    (selectedOldPlane oldSides selected)).lower raw.lower raw.upper

noncomputable section
open Set VariableEnvelope
open scoped Classical
open P1OriginalVariableFourthContinuation
open P1OriginalFifthRawBoxSelectorEquivalence
open P1LiteralVariableFifthCompactSupplier
open P5OldFifthPointwiseQ
open P5OriginalTaylorActualSignedKernel

theorem originalBox_subset_rawClosedBox (raw : FifthWireRow) :
    raw.originalBox ⊆ rawClosedBox raw := by
  intro t ht i
  exact ⟨(ht i).1, (ht i).2.le⟩

theorem activeSide_sound (raw : FifthWireRow) (I : Finset (Fin 5)) (side : Bool)
    (h : activeSide raw I = some side) : ActiveOn raw I side := by
  unfold activeSide at h
  by_cases ha : (∑ i ∈ I, raw.upper i) ≤ 25 / 128
  · rw [if_pos ha] at h
    have hs : side = false := (Option.some.inj h).symm
    subst side
    exact ha
  · rw [if_neg ha] at h
    by_cases hc : 25 / 128 ≤ ∑ i ∈ I, raw.lower i
    · rw [if_pos hc] at h
      have hs : side = true := (Option.some.inj h).symm
      subst side
      exact hc
    · rw [if_neg hc] at h
      cases h

theorem active_tent_eq_plane (raw : FifthWireRow) (I : Finset (Fin 5))
    (side : Bool) (h : ActiveOn raw I side) (t : Fin 5 → ℝ)
    (ht : t ∈ rawClosedBox raw) :
    v (∑ i ∈ I, t i) = (tentPlane I side).eval t := by
  rw [tentPlane_eval]
  cases side
  · change v (∑ i ∈ I, t i) = A (∑ i ∈ I, t i)
    change (∑ i ∈ I, raw.upper i) ≤ (25 / 128 : ℚ) at h
    apply v_eq_A
    have hs : (∑ i ∈ I, t i) ≤ ∑ i ∈ I, (raw.upper i : ℝ) :=
      Finset.sum_le_sum (fun i _ => (ht i).2)
    have hq : (∑ i ∈ I, (raw.upper i : ℝ)) ≤ (25 / 128 : ℝ) := by
      exact_mod_cast h
    exact hs.trans hq
  · change v (∑ i ∈ I, t i) = C (∑ i ∈ I, t i)
    change (25 / 128 : ℚ) ≤ ∑ i ∈ I, raw.lower i at h
    apply v_eq_C
    have hs : (∑ i ∈ I, (raw.lower i : ℝ)) ≤ ∑ i ∈ I, t i :=
      Finset.sum_le_sum (fun i _ => (ht i).1)
    have hq : (25 / 128 : ℝ) ≤ ∑ i ∈ I, (raw.lower i : ℝ) := by
      exact_mod_cast h
    exact hq.trans hs

theorem sum_liftOldMask (I : OldMask) (t : Fin 5 → ℝ) :
    (∑ i ∈ liftOldMask I, t i) = oldSubsetSum I t := by
  unfold liftOldMask oldSubsetSum
  rw [Finset.sum_image]
  exact fun _ _ _ _ h => Fin.castSucc_injective 4 h

theorem inheritedWPlane_eval (t : Fin 5 → ℝ) :
    inheritedWPlane.eval t = B (t 2) := by
  simp [inheritedWPlane, Affine5.eval_add, constantAffine_eval,
    indicatorAffine_eval, B, cap] <;> ring

theorem original_new_eq_affine (raw : FifthWireRow) (side : Bool)
    (h : activeSide raw (maskSlots 5 raw.mask.toNat) = some side)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) :
    rawCandidate 0 raw t = (newPlane raw side).eval t := by
  simpa only [rawCandidate, mul_zero, sub_zero, newPlane] using
    active_tent_eq_plane raw _ side (activeSide_sound raw _ side h) t ht

/-- The exact lower endpoint is used on the signed DIFFERENCE of two
planes. Independent extrema of the two planes are not substituted. -/
theorem affine_dominance_of_lower (raw : FifthWireRow) (a b : Affine5)
    (h : 0 ≤ (a.sub b).lower raw.lower raw.upper)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) : b.eval t ≤ a.eval t := by
  have hlo := (a.sub b).lower_le_eval raw.lower raw.upper t
    (fun i => (ht i).1) (fun i => (ht i).2)
  rw [Affine5.eval_sub] at hlo
  have hq : (0 : ℝ) ≤ ((a.sub b).lower raw.lower raw.upper : ℝ) := by
    exact_mod_cast h
  linarith

/-- The actual old envelope is derived from the source tests. This is
neither an assumed rawFourth equality nor a dynamic-ancestor equality. -/
theorem original_old_eq_selected_affine (raw : FifthWireRow) (newSide : Bool)
    (oldSides : OldSides) (selected : Option OldMask)
    (h : BranchFacts raw newSide oldSides selected)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) :
    rawFourth t = (selectedOldPlane oldSides selected).eval t := by
  have htent (I : OldMask) (hI : I ∈ oldMasks) :
      v (oldSubsetSum I t) = (tentPlane (liftOldMask I) (oldSides I)).eval t := by
    rw [← sum_liftOldMask]
    exact active_tent_eq_plane raw _ _
      (activeSide_sound raw _ _ (h.old_active I hI)) t ht
  apply le_antisymm
  · unfold rawFourth
    apply finiteMax_le
    · rw [← inheritedWPlane_eval]
      exact affine_dominance_of_lower raw _ _ h.dominates_W t ht
    · intro I hI _
      rw [htent I hI]
      exact affine_dominance_of_lower raw _ _ (h.dominates_old I hI) t ht
  · cases selected with
    | none =>
        change inheritedWPlane.eval t ≤ rawFourth t
        rw [inheritedWPlane_eval]
        exact finiteMax_seed_le oldMasks _ _ _
    | some I =>
        have hI : I ∈ oldMasks := h.selected_present
        change (tentPlane (liftOldMask I) (oldSides I)).eval t ≤ rawFourth t
        rw [← htent I hI]
        exact finiteMax_row_le oldMasks _ _ _ I hI trivial

theorem original_new_gt_old (raw : FifthWireRow) (newSide : Bool)
    (oldSides : OldSides) (selected : Option OldMask)
    (h : BranchFacts raw newSide oldSides selected)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) :
    rawFourth t < rawCandidate 0 raw t := by
  rw [original_new_eq_affine raw newSide h.new_active t ht,
    original_old_eq_selected_affine raw newSide oldSides selected h t ht]
  have hlo := ((newPlane raw newSide).sub (selectedOldPlane oldSides selected)).lower_le_eval
    raw.lower raw.upper t (fun i => (ht i).1) (fun i => (ht i).2)
  rw [Affine5.eval_sub] at hlo
  have hq : (0 : ℝ) < (((newPlane raw newSide).sub
      (selectedOldPlane oldSides selected)).lower raw.lower raw.upper : ℝ) := by
    exact_mod_cast h.strict_gain
  linarith

def affineTaylorSignedKernel (new old : Affine5) (t : Fin 5 → ℝ) : ℝ :=
  originalTaylorWeight t *
    (firstF (residual (new.eval t) t) - firstF (residual (old.eval t) t))

/-- This is the original full weighted SIGNED affine Taylor integrand.
Its old branch is now proved to be the actual raw15+W envelope. -/
theorem original_signed_kernel_eq_affine (raw : FifthWireRow) (newSide : Bool)
    (oldSides : OldSides) (selected : Option OldMask)
    (h : BranchFacts raw newSide oldSides selected)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) :
    originalTaylorSignedKernel raw t =
      affineTaylorSignedKernel (newPlane raw newSide) (selectedOldPlane oldSides selected) t := by
  unfold originalTaylorSignedKernel originalTaylorNewArgument originalTaylorOldArgument
  rw [original_new_eq_affine raw newSide h.new_active t ht,
    original_old_eq_selected_affine raw newSide oldSides selected h t ht]
  rfl

end
end ImbalancedChen.P5OriginalTaylorAffineBranchBinding
