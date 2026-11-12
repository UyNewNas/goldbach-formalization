import ImbalancedChen.P4AOriginalFull87FrontierLeafCharge
import ImbalancedChen.P4AOriginalFull87FrontierLeafMembership
import ImbalancedChen.P4AOriginalFull87UnilateralStoppedLevel

/-! The three original P1 high-q books on the same target and the same
unit-weight physical functional. Their zero values are obtained per occurrence
with the sign-selected small factor, before any sharp prime mean is invoked. -/
namespace ImbalancedChen.P4AOriginalFull87FrontierInvoicesZero
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalCompleteSixthChronology (data)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87RawOwnerPartition (actualRawFrontier actualUnownedFrontier)
open P4AOriginalFull87RawTrimSignedHighQ
  (rawOwnedTrimmed rawOwnedTrimOmitted rawSignedHighQ rawOutsideHighQInvoice)
open P4AOriginalFull87ProducerChangeInvoice (licensedSignedHighQ)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply states)
open P4AOriginalFull87LicensedOutsideThreeInvoices
  (licensedFrontier licensedUnowned licensedOwned licensedOwnedTrimOmitted licensedOutsideHighQInvoice)
open P4AOriginalFull87UnmatchedPhysicalLeaves (rawRetainedLeaves licensedRetainedLeaves actualCellCopies)
open P4AOriginalFull87MatchedSuffixDisagreement (actualMatchedExclusiveLeaves actualMatchedExclusiveCharge)
open P4AOriginalFull87ExclusiveLeafSignedCut (exclusiveLeafCost)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (leafHighQCharge highQTest)
open P4AOriginalFull87ThreeClassLeafInvoices
open P4AOriginalFull87FrontierLeafMembership (copies_mem tagged_leaf_mem)
open P4AOriginalFull87FrontierLeafCharge (raw_charge_zero licensed_charge_zero)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy)
open P4AOriginalLicensedSixthSignedLedger (physical)

private theorem sum_zero_on {α : Type*} (l : List α) (f : α → ℝ)
    (hz : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons,hz x (by simp),
        ih (fun y hy => hz y (List.mem_cons_of_mem _ hy)),zero_add]

private theorem add_zero_parts {x y : ℝ} (hx : x = 0) (hy : y = 0) : x + y = 0 := by
  rw [hx,hy,add_zero]

/-- Licensed/outside is supported on its own two filtered occurrence lists.
Raw/outside has different lists. The middle sum has exactly the three
original side-matched leaf charges in each of the 87 source cells. -/
theorem actual_frontier_invoices_zero (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (hsupply : FilteredSourceSupply s r n e q om)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ)^(53/13824 : ℝ)) (hz : (N : ℝ)^mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (he0 : 0 < epsilon) (heps : epsilon ≤ 1/500)
    (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ)) (F : ℕ → ℝ) :
    rawOutsideHighQInvoice (width r) e q om N cap w z ((N : ℝ)^epsilon) X F = 0 ∧
    actualProducerThreeClassLeafBill (width r) n e q om N cap w z ((N : ℝ)^epsilon) X F = 0 ∧
    licensedOutsideHighQInvoice (width r) n e q om N cap w z ((N : ℝ)^epsilon) X F = 0 := by
  classical
  let L := (N : ℝ)^epsilon
  let rawF := actualRawFrontier e q om N cap w z (fun _ => (1 : ℝ))
  let licF := licensedFrontier (width r) n e q om N cap w z
  let charge := leafHighQCharge N cap w L X F
  have rawC (u : FirstExitDepthState ℕ) (hu : u ∈ rawF) :
      ∀ leaf ∈ rawRetainedLeaves e q om N u, charge leaf = 0 :=
    raw_charge_zero e q om N cap w z epsilon he hN heps X hX F u hu
  have licC (u : FirstExitDepthState ℕ) (hu : u ∈ licF) :
      ∀ leaf ∈ licensedRetainedLeaves (width r) n e q om N u, charge leaf = 0 :=
    licensed_charge_zero s r n e q om N cap w z epsilon hsupply he hN hw hz hzcap
      he0 heps X hX F u hu
  have rawAbs (u : FirstExitDepthState ℕ) (hu : u ∈ rawF) :
      |rawSignedHighQ e q om N cap w L X F u| = 0 := by
    have h := raw_only_abs_le_actual_leaf_charge e q om N cap w L X F u
    rw [sum_zero_on (rawRetainedLeaves e q om N u) charge (rawC u hu)] at h
    exact le_antisymm h (abs_nonneg _)
  have licAbs (u : FirstExitDepthState ℕ) (hu : u ∈ licF) :
      |licensedSignedHighQ (width r) n e q om N cap w L X F u| = 0 := by
    have h := licensed_only_abs_le_actual_leaf_charge (width r) n e q om N cap w L X F u
    rw [sum_zero_on (licensedRetainedLeaves (width r) n e q om N u) charge (licC u hu)] at h
    exact le_antisymm h (abs_nonneg _)
  have rawKept (c : Cell) (u : FirstExitDepthState ℕ)
      (hu : u ∈ rawOwnedTrimmed (width r) e q om N cap w z c) : u ∈ rawF :=
    (List.mem_filter.mp (List.mem_filter.mp hu).1).1
  have licKept (c : Cell) (u : FirstExitDepthState ℕ)
      (hu : u ∈ states (width r) n e q om N cap w z (fun _ => (1 : ℝ)) c) : u ∈ licF :=
    (List.mem_filter.mp hu).1
  refine ⟨?_,?_,?_⟩
  · unfold rawOutsideHighQInvoice
    apply add_zero_parts
    · apply sum_zero_on
      intro u hu
      exact rawAbs u (List.mem_filter.mp hu).1
    · apply Finset.sum_eq_zero
      intro c _
      apply sum_zero_on
      intro u hu
      exact rawAbs u (List.mem_filter.mp (List.mem_filter.mp hu).1).1
  · unfold actualProducerThreeClassLeafBill
    apply Finset.sum_eq_zero
    intro c _
    let A := rawOwnedTrimmed (width r) e q om N cap w z c
    let B := states (width r) n e q om N cap w z (fun _ => (1 : ℝ)) c
    let copies := actualCellCopies (width r) n e q om N cap w z c
    have hc (u : FirstExitDepthState ℕ) :
        (u ∈ copies.1 → u ∈ A ∧ u ∈ B) ∧
        (u ∈ copies.2.1 → u ∈ A) ∧ (u ∈ copies.2.2 → u ∈ B) :=
      copies_mem A B u
    unfold actualCellThreeClassLeafBill
    apply add_zero_parts
    · apply add_zero_parts
      · unfold actualCellMatchedLeafBill
        apply sum_zero_on
        intro u hu
        obtain ⟨hmR,hmS⟩ := (hc u).1 hu
        unfold actualMatchedExclusiveCharge
        apply sum_zero_on
        intro tag ht
        let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
        let S := P4AOriginalFull87LicensedSixthPolicy.policy (width r) n e q om (N : ℝ)
        have hleaf := tagged_leaf_mem R S (fun _ => (1 : ℝ))
          u.selectedPrefix u.positive u.mass u.remaining tag ht
        change charge tag.2 = 0
        cases hside : tag.1 with
        | false =>
            apply licC u (licKept c u hmS) tag.2
            simpa [hside,licensedRetainedLeaves,S] using hleaf
        | true =>
            apply rawC u (rawKept c u hmR) tag.2
            simpa [hside,rawRetainedLeaves,R] using hleaf
      · unfold actualCellRawOnlyLeafBill
        apply sum_zero_on
        intro u hu
        exact sum_zero_on _ charge (rawC u (rawKept c u ((hc u).2.1 hu)))
    · unfold actualCellLicensedOnlyLeafBill
      apply sum_zero_on
      intro u hu
      exact sum_zero_on _ charge (licC u (licKept c u ((hc u).2.2 hu)))
  · unfold licensedOutsideHighQInvoice
    apply add_zero_parts
    · apply sum_zero_on
      intro u hu
      exact licAbs u (List.mem_filter.mp hu).1
    · apply Finset.sum_eq_zero
      intro c _
      apply sum_zero_on
      intro u hu
      exact licAbs u (List.mem_filter.mp (List.mem_filter.mp hu).1).1

/-- No high-q discrepancy remains in the full raw-versus-licensed P1
functional. The theorem is uniform in F and uses the same small sieve level. -/
theorem actual_physical_highq_difference_zero (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (hsupply : FilteredSourceSupply s r n e q om)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ)^(53/13824 : ℝ)) (hz : (N : ℝ)^mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (he0 : 0 < epsilon) (heps : epsilon ≤ 1/500)
    (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ)) (F : ℕ → ℝ) :
    physical (eventPolicy true (width r) n e q om N) N cap w z ((N : ℝ)^epsilon) (highQTest X F) -
      physical (eventPolicy false (width r) n e q om N) N cap w z ((N : ℝ)^epsilon) (highQTest X F)
        = 0 := by
  obtain ⟨hR,hM,hS⟩ := actual_frontier_invoices_zero s r n e q om N cap w z epsilon
    hsupply he hN hw hz hzcap he0 heps X hX F
  have h := P4AOriginalFull87UnilateralStoppedLevel.physical_highq_le_frontier
    (width r) n e q om N cap w z epsilon heps he hN X hX F
  simp only [hR,hM,hS,zero_add] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- Discharge FilteredSourceSupply from the original common schedule. Both
omission budgets and all original source/box/sixth tolerances are retained
before e, the history grid, the target and every occurrence. -/
theorem exists_shared_physical_highq_zero (epsSource epsBox epsSixth : ℝ)
    (hSource : 0 < epsSource) (hBox : 0 < epsBox) (hSixth : 0 < epsSixth) :
    ∃ s r : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11/64000 ∧
      P4AOriginalFull87SixthMarginIntegration.totalSixthOmitted s (fun _ _ => (1 : ℝ)) < epsSixth ∧
      P4AOriginalFull87TrimOmission.totalOmitted r (fun _ _ => (1 : ℝ)) < epsSource ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1/100 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
        P4AOriginalFull87AllRankBoxedProvenance.allOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsBox ∧
        FilteredSourceSupply s r n e q om ∧
        ∀ (N cap : ℕ) (w z epsilon : ℝ), 1 < (N : ℝ) →
          w ≤ (N : ℝ)^(53/13824 : ℝ) → (N : ℝ)^mu ≤ z → z ≤ (cap : ℝ) →
          0 < epsilon → epsilon ≤ 1/500 → ∀ X : ℕ, (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ) →
          ∀ F : ℕ → ℝ,
          physical (eventPolicy true (width r) n e q om N) N cap w z ((N : ℝ)^epsilon) (highQTest X F) -
            physical (eventPolicy false (width r) n e q om N) N cap w z ((N : ℝ)^epsilon) (highQTest X F)
              = 0 := by
  obtain ⟨s,r,e0,hp,hmax,h6,h8,hchoose⟩ :=
    P4AOriginalFull87LicensedSixthRealization.exists_shared_licensed_sixth_schedule
      epsSource epsBox epsSixth hSource hBox hSixth
  refine ⟨s,r,e0,hp,hmax,h6,h8,?_⟩
  intro e he hee
  obtain ⟨q0,hq,hReady⟩ := hchoose e he hee
  refine ⟨q0,hq,?_⟩
  intro q hqq om hom
  obtain ⟨n0,hFine⟩ := hReady q hqq om hom
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨_hArchive,_hLicenses,m0,hm⟩ := hFine n hn
  refine ⟨m0,?_⟩
  intro m hm0
  obtain ⟨hboxes,_hSource,_hWinner,_hSaved,_hLower,hs⟩ := hm m hm0
  refine ⟨hboxes,hs,?_⟩
  intro N cap w z epsilon hN hw hz hzcap he0 heps X hX F
  have hdata : 0 ≤ ((data e q om).e : ℝ) := by
    change 0 ≤ (e : ℝ)
    exact_mod_cast he.le
  exact actual_physical_highq_difference_zero s r n e q om N cap w z epsilon hs hdata hN
    hw hz hzcap he0 heps X hX F

end
end ImbalancedChen.P4AOriginalFull87FrontierInvoicesZero
