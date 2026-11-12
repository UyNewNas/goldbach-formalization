import ImbalancedChen.P1OriginalSharpReceiverClassicalReserve
import ImbalancedChen.P1OriginalOwnedGainSharpSupport
import ImbalancedChen.P4AOriginalFull87Fixed599PhysicalRho
import ImbalancedChen.P4AOriginalFull87PhysicalQAggregateInvoice

/-! Two different physical differences. The first compares the original
raw and licensed full policies. The second is the true saving of the
licensed sixth predecessor over its eighth update on all 87 owned lists.
Both use the true sharp singleton receiver on complete moduli. -/
namespace ImbalancedChen.P1Original87SharpMiddleReserve
noncomputable section
open scoped Classical BigOperators
open Filter VariableEnvelope
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy)
open P4AOriginalFull87EighthPrimeMeanLedger (gain primeMass receiverTest densityTest)
open P4AOriginalFull87SignedSharpReceiver
  (sharpPrimeError full87PhysicalSupport full87PhysicalRhoChange full87_physical_signed_normal_form)
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87PhysicalQAggregateInvoice (pairActualHighQModuli actual_raw_licensed_physical_strict_highq_sum)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87CentreFrozenHN (frozenHN)
open P4AOriginalLicensedSixthSignedLedger (physical)
open P1OriginalSharpReceiverClassicalReserve (cut above eventually_receiver_pair)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy policy)

/-- Complete modulus in the original raw-minus-licensed finite support. -/
def comparisonMiddle (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  let R := eventPolicy true (width r) n e q om N
  let S := eventPolicy false (width r) n e q om N
  ∑ d∈(pairActualHighQModuli R S N cap w z (cut N)).filter (fun d => (d:ℝ)<(N:ℝ)^(599/1000:ℝ)),
    (supportedPhysicalRho R N cap w z L d-supportedPhysicalRho S N cap w z L d)*sharpPrimeError N d

/-- Complete modulus in the original sixth-predecessor-minus-eighth
coefficient. It contains exactly the hitherto unpaid middle sharp test. -/
def savingMiddle (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ d∈(full87PhysicalSupport r n e q om N cap w z).filter
    (fun d => cut N<d ∧ (d:ℝ)<(N:ℝ)^(599/1000:ℝ)),
    full87PhysicalRhoChange r n e q om N cap w z L d*sharpPrimeError N d

def comparisonReceiver (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (w z L : ℝ) (G : ℕ→ℝ) :=
  physical (eventPolicy true (width r) n e q om N) N cap w z L G-
    physical (eventPolicy false (width r) n e q om N) N cap w z L G

theorem both_middle (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (w z ell : ℝ)
    (H : FilteredSourceSupply s r n e q om) (he : 0≤((P4AOriginalCompleteSixthChronology.data e q om).e:ℝ))
    (hN : 1<(N:ℝ)) (hw : w≤(N:ℝ)^(53/13824:ℝ)) (hz : (N:ℝ)^mu≤z) (hc : z≤cap)
    (hpos : 0<ell) (hell : ell≤1/1000) :
    let L := (N:ℝ)^ell
    comparisonReceiver r n e q om N cap w z L (highQTest (cut N) (sharpPrimeError N))=
      comparisonMiddle r n e q om N cap w z L ∧
    gain (width r) n e q om N cap w z L (highQTest (cut N) (sharpPrimeError N))=
      savingMiddle r n e q om N cap w z L := by
  dsimp only
  constructor
  · unfold comparisonReceiver comparisonMiddle
    rw [actual_raw_licensed_physical_strict_highq_sum (width r) n e q om N cap w z
      ((N:ℝ)^ell) (cut N) (sharpPrimeError N),Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : (d:ℝ)<(N:ℝ)^(599/1000:ℝ)
    · rw [if_pos hd]
    · have hsame := P4AOriginalFull87Fixed599PhysicalRho.highq_same_supported_rho
        s r n e q om N cap w z ell H he hN hw hz hc hpos hell d (le_of_not_gt hd)
      dsimp only [eventPolicy] at hsame
      rw [if_neg hd,hsame,sub_self,zero_mul]
  · rw [full87_physical_signed_normal_form,savingMiddle,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hlow : cut N<d
    · by_cases hd : (d:ℝ)<(N:ℝ)^(599/1000:ℝ)
      · simp [highQTest,hlow,hd]
      · have hz' := P1OriginalOwnedGainSharpSupport.same_coefficient_above
          s r n e q om N cap w z ell H he hN hw hz hc hell d (le_of_not_gt hd)
        simp [highQTest,hlow,hd,hz']
    · simp [highQTest,hlow]

/-- Select the actual 87 histories and rectangular provenance once, before
the target. The singleton threshold is uniform in both policies, their
small sieve level, and all rectangle and mesh parameters. -/
theorem exists_original_reserves (u epsSource epsBox epsSixth : ℝ)
    (hu : 0<u) (hs0 : 0<epsSource) (hb0 : 0<epsBox) (ht0 : 0<epsSixth) :
    ∃ s r : ℕ,∃ e0 : ℝ,0<e0 ∧ e0≤11/64000 ∧
    P4AOriginalFull87SixthMarginIntegration.totalSixthOmitted s (fun _ _ => (1:ℝ))<epsSixth ∧
    P4AOriginalFull87TrimOmission.totalOmitted r (fun _ _ => (1:ℝ))<epsSource ∧
    ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ om : ℝ,om≤1/100 → ∃ n0 : ℕ,∀ n≥n0,∃ m0 : ℕ,∀ m≥m0,
    P4AOriginalFull87AllRankBoxedProvenance.allOmitted n e q om m (fun _ _ => (1:ℝ))<epsBox ∧
    FilteredSourceSupply s r n e q om ∧
    ∀ᶠ N : ℕ in atTop,Even N → ∀ (cap : ℕ) (w z ell : ℝ),
    w≤(N:ℝ)^(53/13824:ℝ) → (N:ℝ)^mu≤z → z≤cap → 0<ell → ell≤1/1000 →
      let L := (N:ℝ)^ell
      |comparisonReceiver r n e q om N cap w z L (receiverTest N)-
        primeMass N*comparisonReceiver r n e q om N cap w z L densityTest-
        comparisonMiddle r n e q om N cap w z L|≤u*frozenHN N ∧
      |gain (width r) n e q om N cap w z L (receiverTest N)-
        primeMass N*gain (width r) n e q om N cap w z L densityTest-
        savingMiddle r n e q om N cap w z L|≤u*frozenHN N := by
  obtain ⟨s,r,E,hE,hEmax,ht,hs,HE⟩ :=
    P4AOriginalFull87Fixed599PhysicalRho.exists_original_same_rho_599 epsSource epsBox epsSixth hs0 hb0 ht0
  refine ⟨s,r,E,hE,hEmax,ht,hs,?_⟩
  intro e he heE
  obtain ⟨q0,hq,Hq⟩ := HE e he heE
  refine ⟨q0,hq,?_⟩
  intro q hqq om hom
  obtain ⟨n0,Hn⟩ := Hq q hqq om hom
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨m0,Hm⟩ := Hn n hn
  refine ⟨m0,?_⟩
  intro m hm
  obtain ⟨hboxes,hist,_⟩ := Hm m hm
  refine ⟨hboxes,hist,?_⟩
  filter_upwards [eventually_receiver_pair u hu,eventually_ge_atTop (2:ℕ)] with N hfee hN
  intro hev cap w z ell hw hz hc hp hell
  have hNr : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hdata : 0≤((P4AOriginalCompleteSixthChronology.data e q om).e:ℝ) := by
    change 0≤(e:ℝ)
    exact_mod_cast he.le
  obtain ⟨hRS,h68⟩ := both_middle s r n e q om N cap w z ell hist hdata hNr hw hz hc hp hell
  dsimp only
  rw [←hRS,←h68]
  exact ⟨hfee hev (eventPolicy true (width r) n e q om N) (eventPolicy false (width r) n e q om N)
    cap w z ((N:ℝ)^ell),hfee hev (sixthPolicy n e q om (N:ℝ)) (policy (width r) n e q om (N:ℝ))
    cap w z ((N:ℝ)^ell)⟩

end
end ImbalancedChen.P1Original87SharpMiddleReserve
