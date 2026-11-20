import ImbalancedChen.P4AOriginalSixthWinningAction

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

One original87 schedule now supplies the original fourth/fifth archive
licences AND a cofinal common resolution for ALL original eligible sixth
actions on an explicitly exhausted stratum. Its omitted source volume is
accounted for separately. The same finite-parent policy, raw guards,
certified-box lookup and occurrence state list are reused without change.

The safe stratum is a domain of the licence theorem, not a replacement
policy or a hidden deletion of source states. Original saved-row actual
acceptance/gain binding, fixed winner masks on whole boxes, arithmetic
losses and both reserves remain explicit obligations.
-/
namespace ImbalancedChen.P4AOriginalFull87SixthMarginIntegration
noncomputable section
open scoped Classical BigOperators
open P4AOriginalSixthActionBank P4AOriginalSixthCommonMargin
open P4AOriginalSixthWinningAction P1QuantizedActionLicense
open P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87FiniteParentCaps
open P4AOriginalFull87ActionLicenseIntegration
open P4AOriginalFourthFifthUniformActionLicense
open P4AOriginalFull87CertifiedBoxRealization
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87TrimOmission (totalOmitted)

/-- Output only: every ORIGINAL actual eligible action has its OWN mask
licensed; strict cap6 updates have an actual winner. No input licence,
chosen row, selected-mask witness or changed policy is packaged here. -/
def SixthLicenses (s n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℝ, ∀ pre : List ℕ, pre.length = 8 →
  ∀ c : P4AOriginalFull87SourceDictionary.Cell,
    P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre) →
    primeHistoryLogCoordinates N 8 pre ∈ safe8 (width s) →
      (∀ a : Action, ActualEligible e q om N (rosserAncestor 6 pre) a →
        let t := primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)
        LowerLicense (selected a) t (rounded n (endpoint a t) : ℝ) ∧
        (∀ g : P1QuantizedActionLicense.Gate 6,
          gate (selected a) t g + width s / 2 < (rounded n (endpoint a t) : ℝ)) ∧
        (rounded n (endpoint a t) : ℝ) + width n ≤
          VariableEnvelope.v (∑ j ∈ selected a, t j)) ∧
      (cap5 n e q om N (rosserAncestor 5 pre) <
          cap6 n e q om N (rosserAncestor 6 pre) →
        ∃ a ∈ allActions, ActualEligible e q om N (rosserAncestor 6 pre) a ∧
          cap6 n e q om N (rosserAncestor 6 pre) =
            (rounded n (endpoint a (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre))) : ℝ) ∧
          (∀ g : P1QuantizedActionLicense.Gate 6,
            gate (selected a) (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) g +
              width s / 2 < cap6 n e q om N (rosserAncestor 6 pre)) ∧
          cap6 n e q om N (rosserAncestor 6 pre) + width n ≤
            VariableEnvelope.v (∑ j ∈ selected a,
              primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) j))

theorem sixthLicenses_of_resolution (s n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (hn : 4 * width n < width s) : SixthLicenses s n e q om := by
  intro N pre hlen c hs ht
  refine ⟨?_,?_⟩
  · intro a ha
    exact all_actual_actions_licensed (width s) (width_pos s)
      n hn e q om N pre hlen c hs ht a ha
  · intro hwin
    exact strict_update_licensed (width s) (width_pos s)
      n hn e q om N pre hlen c hs ht hwin

/-- Common sixth margin and n threshold precede even the coarse e/q
schedule. The inherited fourth/fifth threshold may still depend on that
fixed bank; taking max preserves both legitimate quantifier orders.

The existing SourceSupply applies to EVERY original trimmed prime tuple,
including those outside the new safe stratum. Only the additional sixth
square-licence assertion is restricted to the safe stratum. Its omitted
volume is explicit, not equated to a prime-mean/density error. -/
theorem exists_shared_all_action_licensed_schedule
    (epsilonSource epsilonBox epsilonSixth : ℝ)
    (hSource : 0 < epsilonSource) (hBox : 0 < epsilonBox)
    (hSixth : 0 < epsilonSixth) :
    ∃ s r : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalSixthOmitted s (fun _ _ => (1 : ℝ)) < epsilonSixth ∧
      totalOmitted r (fun _ _ => (1 : ℝ)) < epsilonSource ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ om : ℝ, om ≤ 1 / 100 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ArchiveLicenses n e q om ∧ SixthLicenses s n e q om ∧
        ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
          totalBoxOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilonBox ∧
          SourceSupply r n m e q om := by
  obtain ⟨s,hs⟩ := exists_common_volume_margin epsilonSixth hSixth
  obtain ⟨n6,hn6⟩ := exists_resolution (width s) (width_pos s)
  obtain ⟨r,e0,he0,hemax,hsource,hchoose⟩ :=
    exists_shared_action_licensed_schedule epsilonSource epsilonBox hSource hBox
  refine ⟨s,r,e0,he0,hemax,hs s le_rfl,hsource,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hq⟩ := hchoose e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨na,hna⟩ := hq q hqq om hom
  refine ⟨max na n6,?_⟩
  intro n hn
  obtain ⟨ha,hm⟩ := hna n ((le_max_left _ _).trans hn)
  have hsmall : 4 * width n < width s := by
    have h := hn6 n ((le_max_right _ _).trans hn)
    have hp := width_pos n
    linarith
  exact ⟨ha,sixthLicenses_of_resolution s n e q om hsmall,hm⟩

end
end ImbalancedChen.P4AOriginalFull87SixthMarginIntegration
