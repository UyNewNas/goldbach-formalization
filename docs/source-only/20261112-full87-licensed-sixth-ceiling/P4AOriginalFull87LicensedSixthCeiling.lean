import ImbalancedChen.P4AOriginalSixthLicensedFilter
import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
import Mathlib.Tactic

/-!
SOURCE ONLY / UNEVALUATED / UNCOMPILED — no kernel credit.

An actual, history-uniform ceiling for the *accepted new sixth actions*.
Unlike the loose product of the entire rough-prime universe, the upper
bound follows from the ORIGINAL action's own selected-tent licence,
including the finite rounding debit. The real fifth predecessor remains
as a separate seed, including in an inherited or losing-action branch.

This proves neither a global rough-leaf modulus bound nor PP admission:
the full fifth predecessor and the inactive third histories still need
their original stopped-tree estimates. No fresh action, mask, coefficient
class, external theorem or reserve is introduced.
-/

namespace ImbalancedChen.P4AOriginalFull87LicensedSixthCeiling
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P1OriginalVariableFourthContinuation (finiteMax_le)
open P1GuardFrozenFiniteCapAlgebra (rounded)
open P4AOriginalFull87FiniteParentCaps (cap5)
open P4AOriginalSixthActionBank (Action allActions selected endpoint)
open P4AOriginalSixthLicensedFilter
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87FiniteParentPolicy (active)
open P4AOriginalFull87LicensedSixthPolicy (level6Exponent)

/-- The actual accepted action is bounded by the physical envelope with
ONE genuine rounding debit. This is the original selected mask of a,
not a mask inherited by a different or unselected branch. -/
theorem accepted_rounded_endpoint_le_envelope_sub_width
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (a : Action) (ha : Accepted n e q om N pre a) :
    (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ)
      ≤ VariableEnvelope.cap - width n := by
  have hlicense :
      (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ)
        + width n ≤
        VariableEnvelope.v
          (∑ j ∈ selected a, primeHistoryLogCoordinates N 6 pre j) := ha.2.2
  have hglobal :
      VariableEnvelope.v
        (∑ j ∈ selected a, primeHistoryLogCoordinates N 6 pre j)
        ≤ VariableEnvelope.cap :=
    VariableEnvelope.v_le_cap _
  linarith

/-- The actual finiteMax sixth producer never creates a new action cap
above 153/256 - width(n). Its fifth seed is retained literally, not
quietly put under the new-action bound. This holds for every history,
including unlicensed margins and no-accepted-action histories. -/
theorem licensedCap_le_real_fifth_or_envelope
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    licensedCap n e q om N pre ≤
      max (cap5 n e q om N (rosserAncestor 5 pre))
        (VariableEnvelope.cap - width n) := by
  unfold licensedCap
  apply finiteMax_le
  · exact le_max_left _ _
  · intro a _ ha
    exact (accepted_rounded_endpoint_le_envelope_sub_width
      n e q om N pre a ha).trans (le_max_right _ _)

/-- A strict increase over the ORIGINAL inherited fifth predecessor
has a genuine eligible action witness (from the existing producer),
whose own licence forces the entire new sixth cap below the global cap. -/
theorem strict_licensed_update_le_envelope_sub_width
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ)
    (h : cap5 n e q om N (rosserAncestor 5 pre) <
      licensedCap n e q om N pre) :
    licensedCap n e q om N pre ≤ VariableEnvelope.cap - width n := by
  obtain ⟨a, _ha, _eligible, heq, _lower, htent⟩ :=
    strict_update_licensed n e q om N pre h
  have hglobal :
      VariableEnvelope.v
        (∑ j ∈ selected a, primeHistoryLogCoordinates N 6 pre j)
        ≤ VariableEnvelope.cap :=
    VariableEnvelope.v_le_cap _
  linarith

/-- In particular an accepted strict sixth action has a STRICT, fixed
subunit envelope. This does not apply to the inherited fifth seed. -/
theorem strict_licensed_update_lt_physical_cap
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ)
    (h : cap5 n e q om N (rosserAncestor 5 pre) <
      licensedCap n e q om N pre) :
    licensedCap n e q om N pre < (153 / 256 : ℝ) := by
  have hu := strict_licensed_update_le_envelope_sub_width
    n e q om N pre h
  have hw : (0 : ℝ) < width n := width_pos n
  dsimp [VariableEnvelope.cap] at hu
  linarith

/-- The *actual* licensed-sixth policy reads this bound on its own
third-active histories, including histories outside any saved87 owner.
For inactive histories it intentionally uses currentSixthExponent;
no unrelated source mask or bound is attached to that branch. -/
theorem active_real_sixth_level_le_fifth_or_envelope
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ)
    (ha : active e q om N pre) :
    level6Exponent n e q om N pre ≤
      max (cap5 n e q om N (rosserAncestor 5 pre))
        (VariableEnvelope.cap - width n) := by
  simpa only [level6Exponent, if_pos ha] using
    licensedCap_le_real_fifth_or_envelope n e q om N pre

end
end ImbalancedChen.P4AOriginalFull87LicensedSixthCeiling
