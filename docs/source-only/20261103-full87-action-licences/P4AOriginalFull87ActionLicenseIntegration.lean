import ImbalancedChen.P4AOriginalFourthFifthUniformActionLicense
import ImbalancedChen.P4AOriginalSixthQuantizedActionLicense
import ImbalancedChen.P4AOriginalFull87CertifiedBoxRealization

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A genuine winning finite-parent action has its OWN original selected mask,
not the mask of an inherited seed or of an arbitrary maximizing upper bound.
The original fourth/fifth archive supplier removes all square-licence and
margin premises at the public schedule. A new quantizer threshold is allowed
AFTER the fixed original e/q bank and BEFORE N. Existing source states and
certified-box lookup are reused unchanged.

Sixth source-square/margin suppliers are imported, but no uniform saved-sixth
archive acceptance or all-sixth margin exhaustion is claimed here. Signed
gains, arithmetic wall losses and compiler/density reserves remain unpaid.
-/
namespace ImbalancedChen.P4AOriginalFull87ActionLicenseIntegration
noncomputable section
open scoped Classical BigOperators
open P1QuantizedActionLicense P1GuardFrozenFiniteCapAlgebra
open P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor
open P4AOriginalCompleteSixthChronology
open P4AOriginalFull87FiniteParentCaps
open P4AOriginalFourthFifthUniformActionLicense
open P4AOriginalFull87CertifiedBoxRealization
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87SevenCubeAdmission
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87TrimOmission (totalOmitted)
open P1AffineCertifiedMesh (accepted)

/-- No new mask is asserted on the inherited/equality branch. When there
is a strict update, the raw eligible original row really attains the new
finite value, and THAT row's full/complementary licences are proved. -/
theorem fourth_winning_row_licensed (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 4) (ha : ArchiveLicenses n e q om)
    (hwin : protect n (originalSeed (data e q om) N pre) (lambda3 (data e q om) N pre) <
      cap4 n e q om N pre) :
    ∃ r ∈ (data e q om).rows4,
      producerEligible (data e q om).licensed4 r (primeHistoryLogCoordinates N 4 pre) ∧
      cap4 n e q om N pre = (rounded n
        (r.bufferedCandidate ((data e q om).e : ℝ) (primeHistoryLogCoordinates N 4 pre)) : ℝ) ∧
      LowerLicense r.selected (primeHistoryLogCoordinates N 4 pre) (cap4 n e q om N pre) ∧
      cap4 n e q om N pre + width n + 2 * ((data e q om).e : ℝ) ≤
        VariableEnvelope.v (∑ i ∈ r.selected, primeHistoryLogCoordinates N 4 pre i) := by
  have heq := fourth_same_guard_image n e q om N pre hlen
  rw [heq] at hwin
  obtain ⟨r,hr,hg,hvalue⟩ := winning_row n
    (originalSeed (data e q om) N pre)
    (protect n (originalSeed (data e q om) N pre) (lambda3 (data e q om) N pre))
    (data e q om).rows4
    (fun r => producerEligible (data e q om).licensed4 r (primeHistoryLogCoordinates N 4 pre))
    (fun r => r.bufferedCandidate ((data e q om).e : ℝ) (primeHistoryLogCoordinates N 4 pre))
    (seed_le_protect _ _ _) hwin
  have hv := heq.trans hvalue
  have hl := ha.1 r hr hg.1 _ hg.2
  exact ⟨r,hr,hg,hv,hv.symm ▸ hl.1,by rw [hv]; exact hl.2⟩

theorem fifth_winning_row_licensed (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5) (ha : ArchiveLicenses n e q om)
    (hwin : cap4 n e q om N (rosserAncestor 4 pre) < cap5 n e q om N pre) :
    ∃ r ∈ (data e q om).rows5,
      P1OriginalVariableFifthContinuation.eligible (data e q om).e (data e q om).chi
        (data e q om).m (data e q om).omega (data e q om).J5 r
        (primeHistoryLogCoordinates N 5 pre) ∧
      cap5 n e q om N pre = (rounded n
        (P1OriginalVariableFifthContinuation.candidate ((data e q om).e : ℝ)
          r.selected (primeHistoryLogCoordinates N 5 pre)) : ℝ) ∧
      LowerLicense r.selected (primeHistoryLogCoordinates N 5 pre) (cap5 n e q om N pre) ∧
      cap5 n e q om N pre + width n + 2 * ((data e q om).e : ℝ) ≤
        VariableEnvelope.v (∑ i ∈ r.selected, primeHistoryLogCoordinates N 5 pre i) := by
  have heq := fifth_same_guard_image n e q om N pre hlen
  have hb : originalSeed (data e q om) N pre ≤ cap4 n e q om N (rosserAncestor 4 pre) := by
    rw [cap4,originalSeed_ancestor _ _ 4 (by decide)]
    exact seed_le_protect _ _ _
  rw [heq] at hwin
  obtain ⟨r,hr,hg,hvalue⟩ := winning_row n (originalSeed (data e q om) N pre)
    (cap4 n e q om N (rosserAncestor 4 pre)) (data e q om).rows5
    (fun r => P1OriginalVariableFifthContinuation.eligible
      (data e q om).e (data e q om).chi (data e q om).m (data e q om).omega
      (data e q om).J5 r (primeHistoryLogCoordinates N 5 pre))
    (fun r => P1OriginalVariableFifthContinuation.candidate ((data e q om).e : ℝ)
      r.selected (primeHistoryLogCoordinates N 5 pre)) hb hwin
  have hv := heq.trans hvalue
  have hl := ha.2 r hr _ hg
  exact ⟨r,hr,hg,hv,hv.symm ▸ hl.1,by rw [hv]; exact hl.2⟩

/-- Raw original87 geometry supplies the saved-sixth half-floor range at
its OWN ancestor. No caller-provided t3 cutoff is needed in this adapter. -/
theorem saved_own_ancestor_license (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (i : P4AOriginalSavedSixthArchive.Row)
    (hi : savedEligible e q om N i (rosserAncestor 6 pre)) :
    LowerLicense (P4AOriginalSixthSquareRows.slots
      (P4AOriginalSavedSixthArchive.selectedMask i))
      (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre))
      (P4AOriginalSavedSixthArchive.endpoint i
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre))) := by
  apply P4AOriginalSixthQuantizedActionLicense.saved_lower_license i _ hi.2.1
  rw [primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) (2 : Fin 6)]
  have ho : StrictAnti (primeHistoryLogCoordinates N 8 pre) :=
    Fin.strictAnti_iff_succ_lt.mpr (source_basic hs).2.2.2
  exact (ho.antitone (show (0 : Fin 8) ≤ 2 by decide)).trans (source_basic hs).1.le

/-- This output repeats the EXISTING boxed-source conclusions verbatim.
It is a conclusion predicate, never an assumption or a replacement tree. -/
def SourceSupply (r n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℕ, 1 < (N : ℝ) → ∀ p : Fin 8 → ℕ,
    (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
    ∀ c : Cell, point (N : ℝ) p ∈ trim c (width r) →
      RealizedHistory e q om (N : ℝ) (pre p) c ∧
      ParentBounds n e q om (N : ℝ) (pre p) c ∧
      ExactLookupParents n m e q om (N : ℝ) (pre p) ∧
      (point (N : ℝ) p ∈ accepted (library n e q om) m →
        BoxedParents n m e q om (N : ℝ) (pre p)) ∧
      (∀ enumerationCap : ℕ, ∀ w z : ℝ,
        w ≤ (N : ℝ) ^ (53 / 13824 : ℝ) →
        (N : ℝ)^VariableEnvelope.mu ≤ z → z ≤ (enumerationCap : ℝ) →
        ∀ weight : ℕ → ℝ,
        canonicalState N enumerationCap w weight p ∈
          P4AOriginalFull87FiniteParentRealization.states
            (width r) n e q om N enumerationCap w z weight c)

/-- Public schedule: actual archive action licences AND the same real
original87 source states. The extra e ceiling and n threshold are proved
from actual row tests. n may depend on fixed e/q/omega, but never on N or a
prime tuple; the fourth/fifth eligibility is never re-run on rounded caps.
Full sixth uniform margin/acceptance and all signed losses remain separate. -/
theorem exists_shared_action_licensed_schedule
    (epsilonSource epsilonBox : ℝ) (hSource : 0 < epsilonSource) (hBox : 0 < epsilonBox) :
    ∃ r : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalOmitted r (fun _ _ => (1 : ℝ)) < epsilonSource ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ om : ℝ, om ≤ 1 / 100 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ArchiveLicenses n e q om ∧
      ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
        totalBoxOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilonBox ∧
        SourceSupply r n m e q om := by
  obtain ⟨r,ns,es,hes,hesMax,hvolume,hchoose⟩ :=
    exists_shared_boxed_source_schedule epsilonSource epsilonBox hSource hBox
  obtain ⟨ea,hea,harchive⟩ := exists_original_archive_action_precision
  refine ⟨r,min es ea,lt_min hes hea,(min_le_left _ _).trans hesMax,hvolume,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hs⟩ := hchoose e he (hee.trans_le (min_le_left _ _))
  refine ⟨q0,hq0,?_⟩
  intro q hq om hom
  obtain ⟨na,hna⟩ := harchive e he (hee.trans_le (min_le_right _ _)) q om
  refine ⟨max ns na,?_⟩
  intro n hn
  refine ⟨hna n ((le_max_right _ _).trans hn),?_⟩
  obtain ⟨m0,hm0⟩ := hs q hq n ((le_max_left _ _).trans hn) om hom
  exact ⟨m0,fun m hm => hm0 m hm⟩

end
end ImbalancedChen.P4AOriginalFull87ActionLicenseIntegration
