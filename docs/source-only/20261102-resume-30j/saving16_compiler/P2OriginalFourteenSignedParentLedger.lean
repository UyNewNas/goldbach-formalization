import ImbalancedChen.P2OriginalAscendingEighthCapDictionary
import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal saving16 fourteen-cell action on its actual frozen sixth parent.
The old re-freeze is proved equal to the parent and eighth admission is
proved from its real frontier. At positive presieve the signed physical
identity retains the beta-width times absolute-mass correction; only w=0
is identified with the original ordinary residual sum.
-/
namespace ImbalancedChen.P2OriginalFourteenSignedParentLedger
noncomputable section
open scoped Classical BigOperators
open P2OriginalAscendingEighthCapDictionary
open P4AOriginalEighthParentPhysicalLedger

/-- The fourteen ascending indices remain those of SelectedFamilyGuard;
there is no eleven-cell sixth or eighty-seven-cell choice substituted. -/
def policy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (base : Bool → List ℕ → Bool) :
    Bool → List ℕ → Bool :=
  familySourcePolicy N lambda6 patterns (parentPolicy N lambda6 base)

theorem old_refreeze_eq_parent (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) :
    firstExitDepthSplicePolicy 8 (parentPolicy N lambda6 base)
      (frozenParityRosserPolicy false 8 (currentLevel N lambda6)) =
        parentPolicy N lambda6 base := by
  change firstExitDepthSplicePolicy 8
    (firstExitDepthSplicePolicy 6 base
      (frozenParityRosserPolicy false 6 (fun pre => N ^ lambda6 pre)))
    (frozenParityRosserPolicy false 8 (fun pre => N ^ lambda6 (rosserAncestor 6 pre))) = _
  rw [frozenParityRosserPolicy_nested false 6 8 (by omega) (fun pre => N ^ lambda6 pre)]
  exact firstExitDepthSplicePolicy_absorb_later 6 8 (by omega) base _

theorem policy_even (N : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (base : Bool → List ℕ → Bool)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    policy N lambda6 patterns base true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 8 _ _
    (parent_even N lambda6 base hbase)
    (fun q => frozenParityRosserPolicy_upper_even 8 _ q) pre

/-- Exact source identity with the old admissibility premise removed.
Every source state comes from the same sixth-parent frontier. -/
theorem actual_fourteen_parent_saving
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (base : Bool → List ℕ → Bool) :
    firstExitRetainedPolynomial (parentPolicy (N : ℝ) lambda6 base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (policy (N : ℝ) lambda6 patterns base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 8 (parentPolicy (N : ℝ) lambda6 base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)).map
        (fun state => actualEighthResidualDifference N cap (currentLevel (N : ℝ) lambda6)
          (familyNextLevel (N : ℝ) lambda6 patterns) state.selectedPrefix)).sum := by
  have h := actual_fourteen_family_splice_saving N cap hN z lambda6 patterns
    (parentPolicy (N : ℝ) lambda6 base) (fun state hs =>
      actual_parent_eighth_admissible N cap 0 z lambda6 base
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) state hs)
  rw [old_refreeze_eq_parent] at h
  exact h

/-- Independent stopped continuation charge, valid for any presieve.
No difference of physical rho sums is used to define this charge. -/
def charge (N cap : ℕ) (w z : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (base : Bool → List ℕ → Bool) : ℝ :=
  ((firstExitDepthFrontier 8 (parentPolicy (N : ℝ) lambda6 base)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z)).map
    (fun state =>
      firstExitRetainedPolynomial (parentPolicy (N : ℝ) lambda6 base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix
        state.positive state.mass state.remaining -
      firstExitRetainedPolynomial
        (frozenParityRosserPolicy false 8 (familyNextLevel (N : ℝ) lambda6 patterns))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) state.selectedPrefix
        state.positive state.mass state.remaining)).sum

theorem parent_sub_policy_eq_charge (N cap : ℕ) (w z : ℝ)
    (lambda6 : List ℕ → ℝ) (patterns : Fin 15 → Finset (Fin 6) → Bool)
    (base : Bool → List ℕ → Bool) :
    firstExitRetainedPolynomial (parentPolicy (N : ℝ) lambda6 base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) -
      firstExitRetainedPolynomial (policy (N : ℝ) lambda6 patterns base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) =
      charge N cap w z lambda6 patterns base := by
  unfold policy familySourcePolicy charge
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

/-- This is the ordinary integral-facing charge at w=0; no beta factor,
Chen quarter, factorial, or replacement of the actual sixth cap appears. -/
theorem unpresieved_charge_eq_residual_sum (N cap : ℕ) (hN : 1 ≤ (N : ℝ))
    (z : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (base : Bool → List ℕ → Bool) :
    charge N cap 0 z lambda6 patterns base =
      ((firstExitDepthFrontier 8 (parentPolicy (N : ℝ) lambda6 base)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)).map
        (fun state => actualEighthResidualDifference N cap (currentLevel (N : ℝ) lambda6)
          (familyNextLevel (N : ℝ) lambda6 patterns) state.selectedPrefix)).sum := by
  rw [← parent_sub_policy_eq_charge]
  exact actual_fourteen_parent_saving N cap hN z lambda6 patterns base

/-- The exact physical signed compiler correction at w>0. The difference
of absolute rough masses is retained with its actual sign; it is not
silently dropped or identified with the positive saving kernel. -/
theorem physical_parent_sub_fourteen_eq_signed_ledger
    (N cap : ℕ) (w z L : ℝ) (lambda6 : List ℕ → ℝ)
    (patterns : Fin 15 → Finset (Fin 6) → Bool) (base : Bool → List ℕ → Bool)
    (hbase : ∀ pre, base true pre = true) :
    let old := parentPolicy (N : ℝ) lambda6 base false
    let fresh := policy (N : ℝ) lambda6 patterns base false
    let lo := reciprocalTotientDensity (actualSmallRosserSupport N cap w)
      (actualSmallRosserMinus N cap w L)
    let hi := reciprocalTotientDensity (actualSmallRosserSupport N cap w)
      (actualSmallRosserPlus N cap w L)
    physicalDensitySum (actualSmallRoughModuli old N cap w z)
        (actualSmallRoughRho old N cap w z L) -
      physicalDensitySum (actualSmallRoughModuli fresh N cap w z)
        (actualSmallRoughRho fresh N cap w z L) =
      ((hi + lo) / 2) * charge N cap w z lambda6 patterns base +
        ((hi - lo) / 2) *
          (reciprocalTotientDensity (fixedRoughSupport old N cap w z)
              (fun d => |fixedRoughCoefficient old N cap w z d|) -
            reciprocalTotientDensity (fixedRoughSupport fresh N cap w z)
              (fun d => |fixedRoughCoefficient fresh N cap w z d|)) := by
  dsimp only
  have hp := P4ASameRhoSignedMassLedger.actual_pair_attachment_density_eq_midpoint_ledger
    (parentPolicy (N : ℝ) lambda6 base false)
    (policy (N : ℝ) lambda6 patterns base false) N cap w z L
  dsimp only at hp
  have hOld := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (parentPolicy (N : ℝ) lambda6 base) (parent_even (N : ℝ) lambda6 base hbase) N cap w z
  have hNew := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (policy (N : ℝ) lambda6 patterns base)
    (policy_even (N : ℝ) lambda6 patterns base hbase) N cap w z
  rw [← hOld, ← hNew, parent_sub_policy_eq_charge] at hp
  exact hp

end
end ImbalancedChen.P2OriginalFourteenSignedParentLedger
