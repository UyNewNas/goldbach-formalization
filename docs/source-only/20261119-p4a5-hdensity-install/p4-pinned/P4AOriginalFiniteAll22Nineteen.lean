import ImbalancedChen.P4AOriginalFiniteAll22PaidSixth
import ImbalancedChen.P4AOriginalFull87UpperDispatch
import ImbalancedChen.P4AOriginalFiniteFallbackJointGain
import ImbalancedChen.P4AAll22OriginalKLedger

/-!
SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.

Consume all eight original eighth slots and the two upper-fallback slots
at the same parameters as the nine paid sixth slots. The only remaining
raw-ledger debit is the existing unsigned lowerEarlyDefect for slots 0/1/2.
This is not an unconditional K or hUpper theorem.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22Nineteen

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87Saved86 (savedGain)
open P4AOriginalFiniteAll22RawLedger
  (finalPolicy lowerEarly lowerEarlySlots lowerEarlyDefect lowerEighth upperFallback upperFallbackSlots)
open P4AOriginalFiniteAll22PaidSixth (paidSixthSlots)
open P4AAll22OriginalKLedger20261024zSourceOnly
  (quotedAll22Raw finalFourGains)

/-- All 87 original records and both successive seed increments occupy
exactly the final eight original slots. No seed increment is added again. -/
theorem savedGain_eq_final_eight_slots :
    (savedGain : ℝ) =
      (∑ j : Fin 4, currentUpperEighteenGains ⟨14 + j.val, by omega⟩) +
        ∑ i, finalFourGains i := by
  rw [P4AOriginalFull87SavedGain.original_saved_gain_q96]
  norm_num [currentUpperEighteenGains, finalFourGains, Fin.sum_univ_succ]

/-- The nineteen paid nominal slots leave precisely the original early
three slots, before replacing them by their actual signed arithmetic gain. -/
theorem nineteen_slots_dictionary :
    (∑ i, currentUpperEighteenPositive i) - paidSixthSlots -
        (savedGain : ℝ) - upperFallbackSlots = quotedAll22Raw + lowerEarlySlots := by
  rw [savedGain_eq_final_eight_slots]
  norm_num [paidSixthSlots, P4AOriginalOrderedLaterPaid.original,
    upperFallbackSlots, lowerEarlySlots, quotedAll22Raw, currentUpperEighteenRaw,
    currentUpperEighteenPositive, currentUpperEighteenGains, finalFourGains,
    Fin.sum_univ_succ]

/-- A single late-cutoff ceiling and cofinal m/r/n/e/q schedule control
the actual final raw coefficient. The positive cutoff omega is fixed
before the target threshold, and the original early defect remains unsigned. -/
theorem exists_final_raw_upper_with_early_defect
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ h : ℝ, 0 < h ∧ ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E → ∀ qMin : ℕ,
      ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ a omega : ℝ, 0 < omega → omega < thirdPrefixRho →
        omega ≤ a → omega ≤ h → a ≤ 1 / 800 →
      ∀ᶠ N : ℕ in atTop, Even N → 2 ≤ N ∧
        normalize N (rawRoot (finalPolicy m r n e q a omega N) N) <
          quotedAll22Raw + lowerEarlyDefect n e q a omega N + eta := by
  have hthird : 0 < eta / 3 := by positivity
  obtain ⟨nS, hSixth⟩ :=
    P4AOriginalFiniteAll22PaidSixth.exists_common_final_raw_upper
      (eta / 3) eMax hthird heMax
  obtain ⟨h, hh, m0, hFallback⟩ :=
    P4AOriginalFiniteFallbackJointGain.gains (eta / 3) hthird
  obtain ⟨r0, hEighth⟩ :=
    P4AOriginalR17Full87SavedEndpoint.original_ordinary_saved (eta / 3) hthird
  refine ⟨h, hh, m0, ?_⟩
  intro m hm
  obtain ⟨EB, hEB, hB⟩ := hFallback m hm
  refine ⟨r0, ?_⟩
  intro r hr
  obtain ⟨n8, h8n⟩ := hEighth r hr
  refine ⟨max nS n8, ?_⟩
  intro n hn
  obtain ⟨ES, hES, hESmax, hS⟩ := hSixth n ((le_max_left _ _).trans hn)
  obtain ⟨E8, hE8, h8⟩ := h8n n ((le_max_right _ _).trans hn)
  let E : ℝ := min ES (min EB E8)
  refine ⟨E, lt_min hES (lt_min hEB hE8), (min_le_left _ _).trans hESmax, ?_⟩
  intro e he heE qMin
  have heRat : 0 < e := by exact_mod_cast he
  have heS : (e : ℝ) < ES := heE.trans_le (min_le_left _ _)
  have heB : (e : ℝ) < EB :=
    heE.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he8 : (e : ℝ) < E8 :=
    heE.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨qB, _hqB, hBq⟩ := hB e he heB
  obtain ⟨q8, _hq8, h8q⟩ := h8 e heRat he8
  obtain ⟨q0, hq0, hqMin, hSq⟩ := hS e he heS (max qMin (max qB q8))
  have hqMin' : qMin ≤ q0 := (le_max_left _ _).trans hqMin
  have hqB0 : qB ≤ q0 := (le_max_left _ _).trans ((le_max_right _ _).trans hqMin)
  have hq80 : q8 ≤ q0 := (le_max_right _ _).trans ((le_max_right _ _).trans hqMin)
  refine ⟨q0, hq0, hqMin', ?_⟩
  intro q hq a omega hw hwR hwa hwh ha
  have ha100 : a ≤ 1 / 100 := ha.trans (by norm_num)
  obtain ⟨N8, _hN8, h8N⟩ := h8q q (hq80.trans hq) a ha100
  filter_upwards [hSq q hq a omega hw hwR hwa ha,
    hBq q (hqB0.trans hq) a omega ha hwa hwh (width r) n,
    eventually_ge_atTop N8] with N hSN hBN hN8
  intro hEven
  obtain ⟨hN2, hRaw⟩ := hSN hEven
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hmu : (N : ℝ) ^ VariableEnvelope.mu ≤ cutoff N :=
    Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num [VariableEnvelope.mu])
  have hz : cutoff N ≤ (N : ℝ) := by
    simpa only [cutoff, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr.le
        (show (19 / 96 : ℝ) ≤ 1 by norm_num)
  have hEight : (savedGain : ℝ) - eta / 3 < lowerEighth r n e q a omega N := by
    rw [P4AOriginalFull87UpperDispatch.lowerEighth_eq_paid_source]
    exact h8N N hN8 hEven omega hwa N (cutoff N) hmu hz
  have hBack : upperFallbackSlots - eta / 3 < upperFallback m r n e q a omega N :=
    hBN hEven
  refine ⟨hN2, ?_⟩
  have hTotal := hRaw m r
  have hDictionary := nineteen_slots_dictionary
  unfold lowerEarlyDefect at *
  linarith only [hTotal, hEight, hBack, hDictionary]

end
end ImbalancedChen.P4AOriginalFiniteAll22Nineteen
