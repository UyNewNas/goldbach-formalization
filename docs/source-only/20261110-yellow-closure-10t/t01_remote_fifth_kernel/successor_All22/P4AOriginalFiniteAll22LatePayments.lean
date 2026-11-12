import ImbalancedChen.P4AOriginalFull87UpperDispatch
import ImbalancedChen.P4AOriginalLaterSixthHighDispatch
import ImbalancedChen.P4AOriginalFiniteAll22Slots

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
One cofinal schedule pays all lower saved/sixth/eighth blocks of the
FINAL finite-bank telescope. Each numerical floor is supplied by its
actual original source;the high-word transport changes no component.
The three early lower slots and two upper slots are separate suppliers.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22LatePayments
noncomputable section
open Filter VariableEnvelope
open scoped Classical BigOperators Topology
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P4AOriginalFiniteAll22RawLedger (lowStage lowerSaved lowerEleven lowerLater lowerEighth)
open P4AOriginalFiniteAll22Slots (laterSlots eighthSlots)

theorem fresh_even (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    ∀ h,fresh (data e q a) omega N true h=true := by
  intro h
  rw [←P4AOriginalFiniteFallbackOccurrence.empty_eq (P4AFallbackCanonicalBanks.bank 0) (data e q a) omega N]
  exact P4AOriginalFiniteFallbackOccurrence.positive _ _ _ _ _

theorem saved_source (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    lowerSaved n e q a omega N=normalize N (P4AOriginalOrderedSavedGain.gain n e q a omega N) :=
  P4AOriginalLaterSixthHighDispatch.dispatch_saved n (data e q a) omega N _ (fresh_even e q a omega N)

theorem later_source (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    lowerLater n e q a omega N=P4AOriginalOrderedLaterPaid.total n (data e q a) omega N :=
  P4AOriginalLaterSixthHighDispatch.dispatch_later n (data e q a) omega N _ (fresh_even e q a omega N)

/-- All four actual lower blocks use the same resolution,buffer,mesh,
early activation,late physical cutoff,target and carrier. No sum-level
mean or licence is an input. -/
theorem exists_common_late_payments (eps : ℝ) (heps : 0<eps) :
    ∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧
    ∀ e : ℚ,0<e → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a omega : ℝ,a≤1/800 → omega≤a → ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      currentUpperEighteenGains 3-eps<lowerSaved n e q a omega N ∧
      P4AOriginalElevenOrderedPayment.originalFloor-eps<lowerEleven n e q a omega N ∧
      laterSlots-eps<lowerLater n e q a omega N ∧
      eighthSlots-eps<lowerEighth r n e q a omega N := by
  obtain ⟨r0,hI⟩ := P4AOriginalR17Full87SavedEndpoint.original_ordinary_saved eps heps
  obtain ⟨n4,h4⟩ := P4AOriginalOrderedSavedGain.exists_original_G4 eps heps
  obtain ⟨n7,h7⟩ := P4AOriginalElevenOrderedPayment.exists_original_G7_ordered_payment eps heps
  obtain ⟨nL,hL⟩ := P4AOriginalOrderedLaterPaid.exists_original_later_payment eps heps
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨nI,hIn⟩ := hI r hr
  refine ⟨max nI (max n4 (max n7 nL)),?_⟩
  intro n hn
  have hnI := (le_max_left nI (max n4 (max n7 nL))).trans hn
  have hn4 := ((le_max_left n4 (max n7 nL)).trans (le_max_right nI (max n4 (max n7 nL)))).trans hn
  have hn7 := ((le_max_left n7 nL).trans ((le_max_right n4 (max n7 nL)).trans
    (le_max_right nI (max n4 (max n7 nL))))).trans hn
  have hnL := ((le_max_right n7 nL).trans ((le_max_right n4 (max n7 nL)).trans
    (le_max_right nI (max n4 (max n7 nL))))).trans hn
  obtain ⟨EI,hEI,hIE⟩ := hIn n hnI
  obtain ⟨E7,hE7,h7E⟩ := h7 n hn7
  obtain ⟨EL,hEL,hLE⟩ := hL n hnL
  refine ⟨min EI (min E7 (min EL (1/64000))),by positivity,?_⟩
  intro e he heE
  have heI := heE.trans_le (min_le_left EI _)
  have he7 := heE.trans_le ((min_le_right EI _).trans (min_le_left E7 _))
  have heL := heE.trans_le ((min_le_right EI _).trans ((min_le_right E7 _).trans (min_le_left EL _)))
  have he4 := heE.trans_le ((min_le_right EI _).trans ((min_le_right E7 _).trans (min_le_right EL _)))
  obtain ⟨qI,hqI,hIQ⟩ := hIE e he heI
  obtain ⟨q7,hq7,h7Q⟩ := h7E e he he7
  obtain ⟨qL,hqL,hLQ⟩ := hLE e he heL
  obtain ⟨q4,hq4,h4Q⟩ := h4 n hn4 e (by exact_mod_cast he) he4
  refine ⟨max qI (max q4 (max q7 qL)),hqI.trans_le (le_max_left _ _),?_⟩
  intro q hq a omega ha hwa
  have hqI' := (le_max_left qI (max q4 (max q7 qL))).trans hq
  have hq4' := ((le_max_left q4 (max q7 qL)).trans (le_max_right qI (max q4 (max q7 qL)))).trans hq
  have hq7' := ((le_max_left q7 qL).trans ((le_max_right q4 (max q7 qL)).trans
    (le_max_right qI (max q4 (max q7 qL))))).trans hq
  have hqL' := ((le_max_right q7 qL).trans ((le_max_right q4 (max q7 qL)).trans
    (le_max_right qI (max q4 (max q7 qL))))).trans hq
  have ha100 : a≤1/100 := ha.trans (by norm_num)
  obtain ⟨NI,hNI,hIN⟩ := hIQ q hqI' a ha100
  obtain ⟨N7,hN7,h7N⟩ := h7Q q hq7' a omega ha100 hwa
  have hmixed := (h4Q q hq4' a ha).and (hLQ q hqL' a omega ha100 hwa)
  obtain ⟨NM,hNM⟩ := eventually_atTop.mp hmixed
  refine ⟨max NI (max N7 NM),hNI.trans (le_max_left _ _),?_⟩
  intro N hN hev
  have hNI' := (le_max_left NI (max N7 NM)).trans hN
  have hN7' := ((le_max_left N7 NM).trans (le_max_right NI (max N7 NM))).trans hN
  have hNM' := ((le_max_right N7 NM).trans (le_max_right NI (max N7 NM))).trans hN
  have h2 := hNI.trans hNI'
  have hNr : 1≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hz : (N:ℝ)^mu≤cutoff N := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num [mu])
  have hcap : cutoff N≤(N:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (19/96:ℝ)≤1)
  obtain ⟨hs,hl⟩ := hNM N hNM'
  refine ⟨?_,?_,?_,?_⟩
  · rw [saved_source]
    exact hs hev omega hwa
  · rw [P4AOriginalFiniteAll22RawLedger.lowerEleven_eq_paid_source]
    exact h7N N hN7' hev
  · rw [later_source]
    exact hl hev
  · rw [P4AOriginalFull87UpperDispatch.lowerEighth_eq_paid_source]
    exact hIN N hNI' hev omega hwa N (cutoff N) hz hcap

end
end ImbalancedChen.P4AOriginalFiniteAll22LatePayments
