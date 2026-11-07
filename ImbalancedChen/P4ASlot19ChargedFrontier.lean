import ImbalancedChen.P2OriginalThirdMinorantLogDictionary
import ImbalancedChen.P2OriginalAscendingEighthCapDictionary
import ImbalancedChen.P4ASameRhoSignedMassLedger
import ImbalancedChen.P4AAll22OriginalKLedger

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A structural rank-eight charge for the proposed slot-19 mask 138. The action
retains the actual inherited sixth ancestor outside the physical-row guard.
Inside the guard it raises that inherited level to the selected cap
A(t2+t4+t8)-10^-6. Both comparison policies use one parent frontier and the
same small Rosser weights. The physical densities remain those of their own
literal actualSmallRoughRho; signed and absolute masses are never exchanged.

The guard does not claim to be exactly the thirteen historical selected cells.
That selected-domain identification and its rational moment floor remain open.
-/

namespace ImbalancedChen.P4ASlot19ChargedFrontierSourceOnly

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P4AAll22OriginalKLedger20261024zSourceOnly

/-- The literal eighth selected subproduct is p2*p4*p8, mask 138. -/
def selectedMask : Finset (Fin 8) := {1, 3, 7}

theorem selectedMask_sum (t : Point) :
    (∑ i ∈ selectedMask, t i) = selectedSum t := by
  norm_num [selectedMask, selectedSum]

theorem selectedMask_bits : (2 ^ 1 + 2 ^ 3 + 2 ^ 7 : ℕ) = 138 :=
  selected_mask_dictionary

theorem slot19_exact_coefficient :
    finalFourGains 0 = (283388722705335806564439 / 2^96 : ℝ) := by
  rfl

def inheritedSixth (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  P2OriginalAscendingEighthCapDictionary.inheritedExponent lambda6 history

def actionGuard (t : Point) (current : ℝ) : Prop :=
  PhysicalRows t ∧ current ≤ comparisonCap t

def raisedExponent (N : ℝ) (lambda6 : List ℕ → ℝ) (history : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 8 history
  if actionGuard t (inheritedSixth lambda6 history) then newCap t
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
  · exact h.2.trans h.1.improvement
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

/-- Literal old-minus-new signed charge on a single common rank-eight
frontier. The original even node is retained; its residual first exits are
subtracted with the original signs. -/
theorem slot19_signed_frontier_charge
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

/-- Same-rho physical charge. The raw signed part is the actual common
frontier sum above; the remaining width term is the difference of the two
literal absolute rough masses. No sign is assigned to that difference. -/
theorem slot19_physical_frontier_charge
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
    slot19_signed_frontier_charge N cap hN z lambda6 parent hold] at hpair
  exact hpair

end
end ImbalancedChen.P4ASlot19ChargedFrontierSourceOnly
