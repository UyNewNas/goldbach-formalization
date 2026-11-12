import ImbalancedChen.P1OriginalFourthCofinalGain
import ImbalancedChen.P4AOriginalNewFifthPhysical

namespace ImbalancedChen.P4AOriginalEarlyHistoricalFloors
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P1OriginalFifthMovingScaleLimit (evenTargets)
open P5OriginalFourthFifthSourceInputs (originalRows4 originalAdmission4)
open P5OriginalCommonFourthSourceLedger (originalFourthSaving originalFourthIntegral eventually_original_fourth_error)
open P5OriginalCommonRefinedConstructor (common3 policy4 policy5)
open P4AOriginalNewFifthUnion (original data)
open P4AOriginalFull87RawChronology (fifthSaving rawRoot cutoff)
open P5OriginalCommonPositivePresieve (normalize normalize_sub)

def slots : ℝ := currentUpperEighteenGains 0+currentUpperEighteenGains 1+currentUpperEighteenGains 2

/-- The policy pair before finite-cap rounding, with the same historical
third decisions. The fifth endpoint uses the union of both original banks. -/
def gain (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (common3 (data e q a) N) N-rawRoot (policy5 (data e q a) N) N)

theorem split (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) (hN : 1≤(N:ℝ)) :
    gain e q a N = normalize N (originalFourthSaving (original e q a) N N (cutoff N))+
      fifthSaving e q a N+P4AOriginalNewFifthPhysical.newGain e q a N := by
  let d := data e q a
  have G : P5OriginalCommonFourthFallbackExcision.FourthGeometry d := fun r hr _ =>
    P1OriginalFourthAllRowsAdmission.originalRows4_geometry r hr
  have h4 := P5OriginalCommonFourthFallbackExcision.common_fourth_raw_ledger d G N N hN (cutoff N)
  change rawRoot (policy4 d N) N=rawRoot (common3 d N) N-originalFourthSaving (original e q a) N N (cutoff N) at h4
  rw [P4AOriginalNewFifthPhysical.newGain_eq]
  change normalize N (rawRoot (common3 d N) N-rawRoot (policy5 d N) N) =
    normalize N (originalFourthSaving (original e q a) N N (cutoff N)) + fifthSaving e q a N +
    (normalize N (rawRoot (policy4 d N) N-rawRoot (policy5 d N) N)-fifthSaving e q a N)
  rw [h4]
  unfold normalize
  ring

/-- Cofinal payment of just the three original low-branch numbers
against the historical unrounded ordinary root. The complete old fifth
reserve and both signed ordinary mean errors occur once. -/
theorem historical_payment (eps : ℝ) (heps : 0<eps) :
    ∃ e0 : ℝ,0<e0 ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<e0 →
    ∀ a : ℝ,0<a → a≤1/800 → ∀ qMin mMin : ℕ,∃ q0 : ℕ,0<q0 ∧ qMin≤q0 ∧
    ∀ q≥q0,mMin≤refinedMesh q ∧ logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ (e:ℝ)/20 ∧
    ∀ᶠ N : ℕ in atTop,Even N → slots-eps<gain e q a N := by
  let u := eps/6
  have hu : 0<u := by dsimp [u]; positivity
  obtain ⟨E4,hE4,H4⟩ := P1OriginalFourthCofinalGain.exists_cofinal_original_fourth_gain u hu
  obtain ⟨E5,hE5,_,H5⟩ := P4AActualRefinableArchivePayment.exists_refinable_actual_archive_payment u hu
  obtain ⟨E3,hE3,H3⟩ := P4AOriginalNewFifthPhysical.exists_ordinary_new_gain u hu
  refine ⟨min E4 (min E5 E3),lt_min hE4 (lt_min hE5 hE3),?_⟩
  intro e he hE a ha haa qMin mMin
  rcases lt_min_iff.mp hE with ⟨h4e,hrest⟩
  obtain ⟨h5e,h3e⟩ := lt_min_iff.mp hrest
  have hep : (0:ℚ)<e := by exact_mod_cast he
  have har : a<(19/96:ℝ) := haa.trans_lt (by norm_num)
  obtain ⟨q3,_,h3⟩ := H3 e he h3e
  obtain ⟨q4,h4min,h4⟩ := H4 e hep h4e a ha (haa.trans (by norm_num)) mMin (max qMin q3)
  obtain ⟨q0,hq0,hq4,_,_,hQ⟩ := H5 e he h5e a ha haa q4 mMin
  refine ⟨q0,hq0,(le_max_left _ _).trans (h4min.trans hq4),?_⟩
  intro q hq
  obtain ⟨hm,hstep,hrough,_,_,_,_,hreserve,_⟩ := hQ q hq
  have hfloor := P5OriginalFullFifthFloorIntegral.original_fifth_endpoint_sub_reserve
    e hep.le q ((e:ℝ)/20) a ha har
  have hc : ∀ᶠ N : ℕ in evenTargets,cutoff N≤(N:ℝ) := by
    filter_upwards [(eventually_ge_atTop (1:ℕ)).filter_mono (show evenTargets≤atTop from inf_le_left)] with N hN
    have H : (1:ℝ)≤N := by exact_mod_cast hN
    simpa only [cutoff,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le H (show (19/96:ℝ)≤1 by norm_num)
  have Hfour := eventually_original_fourth_error (original e q a) hep.le ha har hrough (fun N:ℕ=>N) hc u hu
  have Hfive := P5OriginalArchiveCommonRawMean.eventually_actual_common_rawDifference_error
    originalRows4 originalAdmission4 e hep.le q ((e:ℝ)/20) a ha har (fun N:ℕ=>N) hc u hu
  rw [Filter.eventually_inf_principal] at Hfour Hfive
  refine ⟨hm,hstep,?_⟩
  filter_upwards [Hfour,Hfive,h3 q ((le_max_right _ _).trans (h4min.trans (hq4.trans hq))) a ha haa,
    eventually_ge_atTop (2:ℕ)] with N hfn hgn h3n hN
  intro hEven
  have hpos : 0<N ∧ Even N := ⟨by omega,hEven⟩
  have hf := (abs_lt.mp (hfn hpos)).1
  have hg := (abs_lt.mp (hgn hpos)).1
  change -u<normalize N (originalFourthSaving (original e q a) N N (cutoff N))-originalFourthIntegral (original e q a) at hf
  change -u<fifthSaving e q a N-P5OriginalFifthArchiveActualMean.archiveFifthIntegral
    originalRows4 originalAdmission4 e q ((e:ℝ)/20) a at hg
  have hfirst := (h4 q (hq4.trans hq)).2
  rw [split e q a N (by exact_mod_cast (show 1≤N by omega)),slots,
    P4AOriginalFull87SlotTwoFive.original_old_fifth_slot]
  dsimp [u] at *
  linarith only [hfirst,hf,hg,hfloor,hreserve,h3n hEven,heps]

end
end ImbalancedChen.P4AOriginalEarlyHistoricalFloors
