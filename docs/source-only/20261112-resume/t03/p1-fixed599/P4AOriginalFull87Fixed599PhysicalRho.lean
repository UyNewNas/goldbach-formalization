import ImbalancedChen.P4AOriginalFull87Fixed599Stopped
import ImbalancedChen.P4AOriginalFull87FrontierInvoicesZero
import ImbalancedChen.P4AOriginalFull87FullRhoQBridge
import ImbalancedChen.ActualSmallRoughAttachment

/-! The same two original signed coefficients and one fixed dispersion cut.
Use X=d-1 at an actual positive modulus d, so the endpoint at ceil(N^.599)
is included even when N^.599 is not an integer. -/
namespace ImbalancedChen.P4AOriginalFull87Fixed599PhysicalRho
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalCompleteSixthChronology (data)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices (actualProducerThreeClassLeafBill)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedOutsideHighQInvoice)
open P4AOriginalFull87FullRhoQBridge
  (qProbe positiveQProbe positiveQProbe_eq_qProbe supportedPhysicalRho physical_positive_probe_eq_supported_rho)

/-- The three original absolute invoices and the two whole physical tests
use the same X,F. No sharp prime discrepancy or separate policy support is
assumed. The integer range includes the usual N^.599 ≤ X specialization. -/
theorem actual_invoices_and_physical_599 (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (hs : FilteredSourceSupply s r n e q om)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ)^(53/13824 : ℝ)) (hz : (N : ℝ)^mu ≤ z) (hc : z ≤ (cap : ℝ))
    (hep : 0 < epsilon) (heps : epsilon ≤ 1/1000) (X : ℕ)
    (hX : (N : ℝ)^(599/1000 : ℝ) ≤ ((X+1 : ℕ) : ℝ)) (F : ℕ → ℝ) :
    rawOutsideHighQInvoice (width r) e q om N cap w z ((N : ℝ)^epsilon) X F = 0 ∧
    actualProducerThreeClassLeafBill (width r) n e q om N cap w z ((N : ℝ)^epsilon) X F = 0 ∧
    licensedOutsideHighQInvoice (width r) n e q om N cap w z ((N : ℝ)^epsilon) X F = 0 ∧
    physical (eventPolicy true (width r) n e q om N) N cap w z ((N : ℝ)^epsilon) (highQTest X F) -
      physical (eventPolicy false (width r) n e q om N) N cap w z ((N : ℝ)^epsilon) (highQTest X F) = 0 := by
  obtain ⟨hR,hM,hS⟩ := P4AOriginalFull87FrontierInvoicesZero.actual_frontier_invoices_at_fixed_cuts
    s r n e q om N cap w z epsilon hs he hN hw hz hc hep X (Or.inr ⟨heps,hX⟩) F
  have hstop := P4AOriginalFull87Fixed599Stopped.actual_stopped_599 (width r) n e q om
    N cap w z epsilon he hN heps X hX F
  have h := P4AOriginalFull87EarlyStopPhysicalGap.abs_actual_full_physical_difference_le_stop_and_five_leaf_classes
    (width r) n e q om N cap w z ((N : ℝ)^epsilon) X F
  simp only [hstop,hR,hM,hS,abs_zero,zero_add] at h
  exact ⟨hR,hM,hS,abs_eq_zero.mp (le_antisymm h (abs_nonneg _))⟩

theorem highq_same_supported_rho (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (hs : FilteredSourceSupply s r n e q om)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ)^(53/13824 : ℝ)) (hz : (N : ℝ)^mu ≤ z) (hc : z ≤ (cap : ℝ))
    (hep : 0 < epsilon) (heps : epsilon ≤ 1/1000) (d : ℕ)
    (hd : (N : ℝ)^(599/1000 : ℝ) ≤ (d : ℝ)) :
    supportedPhysicalRho (eventPolicy true (width r) n e q om N) N cap w z ((N : ℝ)^epsilon) d =
    supportedPhysicalRho (eventPolicy false (width r) n e q om N) N cap w z ((N : ℝ)^epsilon) d := by
  have hdpos : 0 < d := by
    exact_mod_cast ((Real.rpow_pos_of_pos (zero_lt_one.trans hN) (599/1000 : ℝ)).trans_le hd)
  let X := d-1
  have hsucc : X+1=d := by dsimp [X]; omega
  have hcut : (N : ℝ)^(599/1000 : ℝ) ≤ ((X+1 : ℕ) : ℝ) := by rw [hsucc]; exact hd
  have probe : highQTest X (qProbe d) = positiveQProbe d := by
    rw [positiveQProbe_eq_qProbe d hdpos]
    funext j
    by_cases hj : j=d
    · subst j
      have hlt : X<d := by omega
      simp [highQTest,hlt]
    · simp [highQTest,qProbe,hj]
  have h := (actual_invoices_and_physical_599 s r n e q om N cap w z epsilon
    hs he hN hw hz hc hep heps X hcut (qProbe d)).2.2.2
  have hR := physical_positive_probe_eq_supported_rho (eventPolicy true (width r) n e q om N)
    N cap w z ((N : ℝ)^epsilon) d hdpos
  have hS := physical_positive_probe_eq_supported_rho (eventPolicy false (width r) n e q om N)
    N cap w z ((N : ℝ)^epsilon) d hdpos
  rw [probe,hR,hS] at h
  exact sub_eq_zero.mp h

/-- Off the displayed finite support the original convolution coefficient
itself is zero. On the support this is the definition of its public probe. -/
private theorem supported_eq_actual (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (d : ℕ) : supportedPhysicalRho P N cap w z L d =
      actualSmallRoughRho (P false) N cap w z L d := by
  unfold supportedPhysicalRho
  by_cases h : d ∈ actualSmallRoughModuli (P false) N cap w z
  · rw [if_pos h]
  · rw [if_neg h]
    exact (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ h).symm

/-- The readback holds on the actual original coefficients at every complete
modulus at or above the fixed threshold, including equality. -/
theorem highq_same_actual_rho (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (hs : FilteredSourceSupply s r n e q om)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ)^(53/13824 : ℝ)) (hz : (N : ℝ)^mu ≤ z) (hc : z ≤ (cap : ℝ))
    (hep : 0 < epsilon) (heps : epsilon ≤ 1/1000) (d : ℕ)
    (hd : (N : ℝ)^(599/1000 : ℝ) ≤ (d : ℝ)) :
    actualSmallRoughRho (eventPolicy true (width r) n e q om N false) N cap w z ((N : ℝ)^epsilon) d =
    actualSmallRoughRho (eventPolicy false (width r) n e q om N false) N cap w z ((N : ℝ)^epsilon) d := by
  simpa only [supported_eq_actual] using highq_same_supported_rho
    s r n e q om N cap w z epsilon hs he hN hw hz hc hep heps d hd

/-- Same original schedule, with every selection made before the even-target
application (the coefficient identity itself holds for all valid targets). -/
theorem exists_original_same_rho_599 (epsSource epsBox epsSixth : ℝ)
    (hs0 : 0<epsSource) (hb0 : 0<epsBox) (ht0 : 0<epsSixth) :
    ∃ s r : ℕ, ∃ e0 : ℝ, 0<e0 ∧ e0≤11/64000 ∧
      P4AOriginalFull87SixthMarginIntegration.totalSixthOmitted s (fun _ _ => (1 : ℝ)) < epsSixth ∧
      P4AOriginalFull87TrimOmission.totalOmitted r (fun _ _ => (1 : ℝ)) < epsSource ∧
      ∀ e : ℚ, 0<e → (e : ℝ)<e0 → ∃ q0 : ℕ, 0<q0 ∧ ∀ q : ℕ, q0≤q →
      ∀ om : ℝ, om≤1/100 → ∃ n0 : ℕ, ∀ n : ℕ, n0≤n → ∃ m0 : ℕ, ∀ m : ℕ, m0≤m →
        P4AOriginalFull87AllRankBoxedProvenance.allOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsBox ∧
        FilteredSourceSupply s r n e q om ∧
        ∀ (N cap : ℕ) (w z epsilon : ℝ), 1<(N : ℝ) →
          w≤(N : ℝ)^(53/13824 : ℝ) → (N : ℝ)^mu≤z → z≤(cap : ℝ) →
          0<epsilon → epsilon≤1/1000 → ∀ d : ℕ, (N : ℝ)^(599/1000 : ℝ)≤(d : ℝ) →
          actualSmallRoughRho (eventPolicy true (width r) n e q om N false) N cap w z ((N : ℝ)^epsilon) d =
          actualSmallRoughRho (eventPolicy false (width r) n e q om N false) N cap w z ((N : ℝ)^epsilon) d := by
  obtain ⟨s,r,e0,he0,hmax,ht,hs,hE⟩ :=
    P4AOriginalFull87FrontierInvoicesZero.exists_shared_physical_highq_zero
      epsSource epsBox epsSixth hs0 hb0 ht0
  refine ⟨s,r,e0,he0,hmax,ht,hs,?_⟩
  intro e he hee
  obtain ⟨q0,hq,hQ⟩ := hE e he hee
  refine ⟨q0,hq,?_⟩
  intro q hqq om hom
  obtain ⟨n0,hFine⟩ := hQ q hqq om hom
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨m0,hM⟩ := hFine n hn
  refine ⟨m0,?_⟩
  intro m hm
  obtain ⟨hboxes,hSupply,_hOldCut⟩ := hM m hm
  refine ⟨hboxes,hSupply,?_⟩
  intro N cap w z eps hN hw hz hc hep heps d hd
  have hd0 : 0 ≤ ((data e q om).e : ℝ) := by change 0 ≤ (e : ℝ); exact_mod_cast he.le
  exact highq_same_actual_rho s r n e q om N cap w z eps hSupply hd0 hN hw hz hc hep heps d hd

end
end ImbalancedChen.P4AOriginalFull87Fixed599PhysicalRho
