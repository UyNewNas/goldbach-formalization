import ImbalancedChen.P4AActualSixthFrozenEighthAdmission
import ImbalancedChen.P4ASlot17DescendingChargedFrontier
import ImbalancedChen.P4ASlot19ChargedFrontier

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The original slot17/slot19 comparison policies previously used an extra
rank-eight refreezing of an inherited sixth level. Here that old policy is
identified with the literal sixth parent itself. The new eighth action is
therefore charged to that parent and its actual physical rho. The seventh
history admission is derived by the companion recursion, not assumed.

The arbitrary presieve w remains inside the carrier. At w>0 the charge is
a stopped continuation polynomial, not an unpresieved residual integral.
The absolute-mass width difference retains its own signed subtraction.

The two local original actions are not identified with all 87 adopted
domains. Complete sixth policy payload, domain ownership and selected
integral lower certificates remain OPEN.
-/
namespace ImbalancedChen.P4AOriginalEighthParentPhysicalLedger

noncomputable section
open scoped Classical BigOperators
open P4AActualSixthFrozenEighthAdmission

/-- The literal current parent after the actual rank-six cap has been fixed. -/
def parentPolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  sixthPolicy base (fun pre => N ^ lambda6 pre)

/-- Refreezing a sixth-inherited level at rank eight changes no decision. -/
theorem slot17_old_policy_eq_parent
    (N : ℝ) (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool) :
    P4ASlot17DescendingChargedFrontierSourceOnly.oldPolicy N lambda6
        (parentPolicy N lambda6 base) = parentPolicy N lambda6 base := by
  change firstExitDepthSplicePolicy 8
    (firstExitDepthSplicePolicy 6 base
      (frozenParityRosserPolicy false 6 (fun pre => N ^ lambda6 pre)))
    (frozenParityRosserPolicy false 8 (fun pre => N ^ lambda6 (rosserAncestor 6 pre))) = _
  rw [frozenParityRosserPolicy_nested false 6 8 (by omega) (fun pre => N ^ lambda6 pre)]
  exact firstExitDepthSplicePolicy_absorb_later 6 8 (by omega) base _

theorem slot19_old_policy_eq_parent
    (N : ℝ) (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool) :
    P4ASlot19ChargedFrontierSourceOnly.oldPolicy N lambda6
        (parentPolicy N lambda6 base) = parentPolicy N lambda6 base := by
  change firstExitDepthSplicePolicy 8
    (firstExitDepthSplicePolicy 6 base
      (frozenParityRosserPolicy false 6 (fun pre => N ^ lambda6 pre)))
    (frozenParityRosserPolicy false 8 (fun pre => N ^ lambda6 (rosserAncestor 6 pre))) = _
  rw [frozenParityRosserPolicy_nested false 6 8 (by omega) (fun pre => N ^ lambda6 pre)]
  exact firstExitDepthSplicePolicy_absorb_later 6 8 (by omega) base _

/-- The old residual input for either actual local action is supplied by
its true parent frontier; there is no caller-provided admissibility field. -/
theorem actual_parent_eighth_admissible
    (N cap : ℕ) (w z : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (h : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 8 (parentPolicy (N : ℝ) lambda6 base)
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ lambda6 (rosserAncestor 6 state.selectedPrefix)) state.selectedPrefix :=
  actual_rank_eight_admissible base (fun pre => (N : ℝ) ^ lambda6 pre)
    N cap w z h state hs

inductive Action where
  | descending17
  | ascending19

/-- Actual local original-formula levels, preserving their respective
mask129 descending and mask138 ascending guards and inherited fallback. -/
def actionLevel (a : Action) (N : ℝ) (lambda6 : List ℕ → ℝ) : List ℕ → ℝ :=
  match a with
  | .descending17 => P4ASlot17DescendingChargedFrontierSourceOnly.raisedLevel N lambda6
  | .ascending19 => P4ASlot19ChargedFrontierSourceOnly.raisedLevel N lambda6

def replacement (a : Action) (N : ℝ) (lambda6 : List ℕ → ℝ) :
    Bool → List ℕ → Bool :=
  frozenParityRosserPolicy false 8 (actionLevel a N lambda6)

def actionPolicy (a : Action) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 (parentPolicy N lambda6 base) (replacement a N lambda6)

theorem descending_action_eq_original
    (N : ℝ) (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool) :
    actionPolicy .descending17 N lambda6 base =
      P4ASlot17DescendingChargedFrontierSourceOnly.raisedPolicy N lambda6
        (parentPolicy N lambda6 base) := rfl

theorem ascending_action_eq_original
    (N : ℝ) (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool) :
    actionPolicy .ascending19 N lambda6 base =
      P4ASlot19ChargedFrontierSourceOnly.raisedPolicy N lambda6
        (parentPolicy N lambda6 base) := rfl

theorem parent_even (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    parentPolicy N lambda6 base true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    hbase (fun q => frozenParityRosserPolicy_upper_even 6 _ q) pre

theorem action_even (a : Action) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    actionPolicy a N lambda6 base true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 8 _ _
    (parent_even N lambda6 base hbase)
    (fun q => frozenParityRosserPolicy_upper_even 8 _ q) pre

/-- The entire actual continuation is charged, with original state sign,
remaining smaller labels, and actual incoming mass. Terminal short
branches are retained by both policies and cancel in this definition's
proved dictionary. -/
def charge (a : Action) (N cap : ℕ) (w z : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) : ℝ :=
  ((firstExitDepthFrontier 8 (parentPolicy (N : ℝ) lambda6 base)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z)).map
    (fun state =>
      firstExitRetainedPolynomial (parentPolicy (N : ℝ) lambda6 base)
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix
          state.positive state.mass state.remaining -
        firstExitRetainedPolynomial (replacement a (N : ℝ) lambda6)
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix
          state.positive state.mass state.remaining)).sum

theorem parent_sub_action_eq_charge
    (a : Action) (N cap : ℕ) (w z : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) :
    firstExitRetainedPolynomial (parentPolicy (N : ℝ) lambda6 base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) -
      firstExitRetainedPolynomial (actionPolicy a (N : ℝ) lambda6 base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) =
      charge a N cap w z lambda6 base := by
  unfold actionPolicy charge
  rw [firstExitRetainedPolynomial_eq_terminal_add_frontier 8,
    firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier,
    add_sub_add_left_eq_sub]
  generalize firstExitDepthFrontier 8 (parentPolicy (N : ℝ) lambda6 base)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) = states
  induction states with
  | nil => simp
  | cons state states ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

/-- Literal same-rho physical causal ledger, valid also at fixed w>0.
Each absolute mass belongs to that policy's very own signed rough
coefficient; their difference has no assumed sign. -/
theorem physical_parent_sub_action_eq_charge
    (a : Action) (N cap : ℕ) (w z L : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (hbase : ∀ pre, base true pre = true) :
    let old := parentPolicy (N : ℝ) lambda6 base false
    let fresh := actionPolicy a (N : ℝ) lambda6 base false
    let lo := reciprocalTotientDensity (actualSmallRosserSupport N cap w)
      (actualSmallRosserMinus N cap w L)
    let hi := reciprocalTotientDensity (actualSmallRosserSupport N cap w)
      (actualSmallRosserPlus N cap w L)
    physicalDensitySum (actualSmallRoughModuli old N cap w z)
        (actualSmallRoughRho old N cap w z L) -
      physicalDensitySum (actualSmallRoughModuli fresh N cap w z)
        (actualSmallRoughRho fresh N cap w z L) =
      ((hi + lo) / 2) * charge a N cap w z lambda6 base +
        ((hi - lo) / 2) *
          (reciprocalTotientDensity (fixedRoughSupport old N cap w z)
              (fun d => |fixedRoughCoefficient old N cap w z d|) -
            reciprocalTotientDensity (fixedRoughSupport fresh N cap w z)
              (fun d => |fixedRoughCoefficient fresh N cap w z d|)) := by
  dsimp only
  have hp := P4ASameRhoSignedMassLedger.actual_pair_attachment_density_eq_midpoint_ledger
    (parentPolicy (N : ℝ) lambda6 base false)
    (actionPolicy a (N : ℝ) lambda6 base false) N cap w z L
  dsimp only at hp
  have hOld := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (parentPolicy (N : ℝ) lambda6 base) (parent_even (N : ℝ) lambda6 base hbase) N cap w z
  have hNew := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (actionPolicy a (N : ℝ) lambda6 base) (action_even a (N : ℝ) lambda6 base hbase) N cap w z
  rw [← hOld, ← hNew, parent_sub_action_eq_charge] at hp
  exact hp

end
end ImbalancedChen.P4AOriginalEighthParentPhysicalLedger
