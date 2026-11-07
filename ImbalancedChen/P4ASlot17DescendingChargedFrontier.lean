import ImbalancedChen.P2OriginalDescendingEighthLogSemantics
import ImbalancedChen.P2OriginalAscendingEighthCapDictionary
import ImbalancedChen.P4ASameRhoSignedMassLedger
import ImbalancedChen.P4AAll22OriginalKLedger

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The seventeenth all22 saving is the fifteen-cell descending eighth family.
It selects mask 129 = {p1,p8} and cap C(t1+t8)-10^-6, distinct from the
slot-19 mask-138 ascending cap. Here a genuine inherited sixth ancestor is
raised only on descending physical rows. Its old-minus-new signed frontier
sum is then attached to the two literal physical rhos with their common
small weights and their original signed subtraction.

The guard is a structural sufficient region; identification with the exact
fifteen historical cells and the selected rational integral floor remain
separate obligations.
-/

namespace ImbalancedChen.P4ASlot17DescendingChargedFrontierSourceOnly

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators
open P4AAll22OriginalKLedger20261024zSourceOnly
open P2OriginalDescendingEighthLogSemantics

theorem slot17_exact_coefficient :
    currentUpperEighteenGains 16 =
      (467454156274267811817033 / 2^96 : ℝ) := by
  rfl

theorem slot17_selected_mask_sum (t : Point) :
    (∑ i ∈ selectedMask129, t i) = selectedSum t :=
  selectedMask129_sum t

theorem slot17_selected_mask_bits : (2 ^ 0 + 2 ^ 7 : ℕ) = 129 := by
  norm_num

/-- The actual sixth ancestor is used, not the old raw comparison cap. -/
def inheritedSixth (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  P2OriginalAscendingEighthCapDictionary.inheritedExponent lambda6 history

/-- Sufficient real rows for the descending charged leaf. The last two
fields keep the original descending tent side and its strict buffer. -/
structure DescendingRows (t : Point) (current : ℝ) : Prop where
  coordinates : ∀ i, 0 < t i
  lastOrder : t 7 < t 6
  seventhHistory : history7 t < current
  parentUpper : current ≤ oldRaw t
  improvement : oldRaw t < newCap t
  terminal : newCap t - total t < 3 * t 7
  descendingSide : VariableEnvelope.mu < selectedSum t

theorem descending_license {t : Point} {current : ℝ}
    (h : DescendingRows t current) :
    VariableEnvelope.v (∑ i ∈ selectedMask129, t i) - newCap t = eta ∧
      newCap t < VariableEnvelope.v (∑ i ∈ selectedMask129, t i) :=
  selected129_license h.descendingSide

/-- On this physical row the conservative saving has the correct lower
direction against the genuine current sixth-parent residual. -/
theorem physicalKernel_le_inheritedSaving {t : Point} {current : ℝ}
    (h : DescendingRows t current) :
    physicalKernel t ≤
      (actualResidualProfile current t -
        actualResidualProfile (newCap t) t) * ∏ i, 1 / t i := by
  exact physicalKernel_le_actual_parent_saving t current
    h.coordinates h.lastOrder h.seventhHistory h.parentUpper
    h.improvement h.terminal

def raisedExponent (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 8 history
  if DescendingRows t (inheritedSixth lambda6 history) then newCap t
  else inheritedSixth lambda6 history

def oldLevel (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  N ^ inheritedSixth lambda6 history

def raisedLevel (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  N ^ raisedExponent N lambda6 history

theorem inheritedSixth_le_raisedExponent
    (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) :
    inheritedSixth lambda6 history ≤ raisedExponent N lambda6 history := by
  unfold raisedExponent
  dsimp only
  split_ifs with h
  · exact h.parentUpper.trans h.improvement.le
  · exact le_rfl

theorem oldLevel_le_raisedLevel
    (N : ℝ) (hN : 1 ≤ N) (lambda6 : List ℕ → ℝ) (history : List ℕ) :
    oldLevel N lambda6 history ≤ raisedLevel N lambda6 history := by
  exact Real.rpow_le_rpow_of_exponent_le hN
    (inheritedSixth_le_raisedExponent N lambda6 history)

def oldPolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 parent
    (frozenParityRosserPolicy false 8 (oldLevel N lambda6))

def raisedPolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 parent
    (frozenParityRosserPolicy false 8 (raisedLevel N lambda6))

theorem oldPolicy_even (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool)
    (hparent : ∀ pre, parent true pre = true) (pre : List ℕ) :
    oldPolicy N lambda6 parent true pre = true := by
  unfold oldPolicy
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 8 _ _
    hparent (fun q => frozenParityRosserPolicy_upper_even 8 _ q) pre

theorem raisedPolicy_even (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool)
    (hparent : ∀ pre, parent true pre = true) (pre : List ℕ) :
    raisedPolicy N lambda6 parent true pre = true := by
  unfold raisedPolicy
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 8 _ _
    hparent (fun q => frozenParityRosserPolicy_upper_even 8 _ q) pre

/-- Actual old-minus-new signed density on the same rank-eight parent
frontier. Prefix admission for the raised cap follows from monotonicity. -/
theorem slot17_signed_frontier_charge
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ)
    (lambda6 : List ℕ → ℝ) (parent : Bool → List ℕ → Bool)
    (hold : ∀ state ∈ firstExitDepthFrontier 8 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ordinaryRosserPrefixAdmissible false
        (oldLevel (N : ℝ) lambda6 state.selectedPrefix) state.selectedPrefix) :
    firstExitRetainedPolynomial (oldPolicy (N : ℝ) lambda6 parent)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (raisedPolicy (N : ℝ) lambda6 parent)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 8 parent (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z)).map (fun state =>
          actualFrozenFrontierDensityTerm false N cap (oldLevel (N : ℝ) lambda6)
              state.selectedPrefix -
            actualFrozenFrontierDensityTerm false N cap (raisedLevel (N : ℝ) lambda6)
              state.selectedPrefix)).sum := by
  unfold oldPolicy raisedPolicy
  apply firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    false 8 (by omega) parent (raisedLevel (N : ℝ) lambda6)
    (oldLevel (N : ℝ) lambda6) N cap z
  · intro state hstate
    exact ordinaryRosserPrefixAdmissible_mono false state.selectedPrefix
      (oldLevel_le_raisedLevel (N : ℝ) hN lambda6 state.selectedPrefix)
      (hold state hstate)
  · exact hold

/-- Same-rho physical attachment: old-minus-new is the signed frontier
charge plus the literal absolute-mass difference at the shared small
Rosser width. No sign of that width correction is presumed. -/
theorem slot17_physical_frontier_charge
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z L : ℝ)
    (lambda6 : List ℕ → ℝ) (parent : Bool → List ℕ → Bool)
    (hparent : ∀ pre, parent true pre = true)
    (hold : ∀ state ∈ firstExitDepthFrontier 8 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ordinaryRosserPrefixAdmissible false
        (oldLevel (N : ℝ) lambda6 state.selectedPrefix) state.selectedPrefix) :
    let old := oldPolicy (N : ℝ) lambda6 parent false
    let fresh := raisedPolicy (N : ℝ) lambda6 parent false
    let lo := reciprocalTotientDensity (actualSmallRosserSupport N cap 0)
      (actualSmallRosserMinus N cap 0 L)
    let hi := reciprocalTotientDensity (actualSmallRosserSupport N cap 0)
      (actualSmallRosserPlus N cap 0 L)
    physicalDensitySum (actualSmallRoughModuli old N cap 0 z)
        (actualSmallRoughRho old N cap 0 z L) -
      physicalDensitySum (actualSmallRoughModuli fresh N cap 0 z)
        (actualSmallRoughRho fresh N cap 0 z L) =
      ((hi + lo) / 2) *
        ((firstExitDepthFrontier 8 parent (fun p : ℕ => 1 / ((p : ℝ) - 1))
          [] true 1 (roughPrimeUniverse N cap 0 z)).map (fun state =>
            actualFrozenFrontierDensityTerm false N cap (oldLevel (N : ℝ) lambda6)
                state.selectedPrefix -
              actualFrozenFrontierDensityTerm false N cap (raisedLevel (N : ℝ) lambda6)
                state.selectedPrefix)).sum +
      ((hi - lo) / 2) *
        (reciprocalTotientDensity (fixedRoughSupport old N cap 0 z)
            (fun d => |fixedRoughCoefficient old N cap 0 z d|) -
          reciprocalTotientDensity (fixedRoughSupport fresh N cap 0 z)
            (fun d => |fixedRoughCoefficient fresh N cap 0 z d|)) := by
  dsimp only
  have hpair :=
    P4ASameRhoSignedMassLedger.actual_pair_attachment_density_eq_midpoint_ledger
      (oldPolicy (N : ℝ) lambda6 parent false)
      (raisedPolicy (N : ℝ) lambda6 parent false) N cap 0 z L
  dsimp only at hpair
  have hOld :=
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      (oldPolicy (N : ℝ) lambda6 parent)
      (oldPolicy_even (N : ℝ) lambda6 parent hparent) N cap 0 z
  have hNew :=
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      (raisedPolicy (N : ℝ) lambda6 parent)
      (raisedPolicy_even (N : ℝ) lambda6 parent hparent) N cap 0 z
  rw [← hOld, ← hNew,
    slot17_signed_frontier_charge N cap hN z lambda6 parent hold] at hpair
  exact hpair

end
end ImbalancedChen.P4ASlot17DescendingChargedFrontierSourceOnly
