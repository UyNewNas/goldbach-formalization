import ImbalancedChen.P4AOriginalFiniteAll22PhysicalLedger
import ImbalancedChen.P4AOriginalLaterSixthHighDispatch
import ImbalancedChen.P4AOriginalElevenOrderedPayment
import ImbalancedChen.P4AOrderedThirdPositiveRoot

/-!
SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.

Consume the existing saved, eleven and later-sixth payments on the final
finite All22 dispatcher. No source integral, floor or arithmetic mean is
proved again. The resolution, buffer and coarse mesh are common, and the
target threshold is taken only after the late physical cutoff is fixed.
The three early slots, the eighth increment and both upper fallback slots
remain literal signed differences. No sign is asserted for their defects.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22PaidSixth

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFiniteAll22RawLedger
  (lowerEarly lowerSaved lowerEleven lowerLater lowerEighth upperFallback finalPolicy)
open P4AOriginalFiniteAll22PhysicalLedger (scalar upper)

/-- Literal original slots 3, 6 and 7 through 13, each used once. -/
def paidSixthSlots : ℝ :=
  currentUpperEighteenGains 3 + currentUpperEighteenGains 6 +
    P4AOriginalOrderedLaterPaid.original

theorem lowerSaved_eq_paid_source
    (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    lowerSaved n e q a omega N =
      normalize N (P4AOriginalOrderedSavedGain.gain n e q a omega N) := by
  have hU : ∀ h, fresh (data e q a) omega N true h = true := by
    intro h
    rw [← P4AOriginalFiniteFallbackOccurrence.empty_eq
      (P4AFallbackCanonicalBanks.bank 0) (data e q a) omega N]
    exact P4AOriginalFiniteFallbackOccurrence.positive _ _ _ _ _
  exact P4AOriginalLaterSixthHighDispatch.dispatch_saved n (data e q a) omega N _ hU

theorem lowerLater_eq_paid_source
    (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    lowerLater n e q a omega N =
      P4AOriginalOrderedLaterPaid.total n (data e q a) omega N := by
  have hU : ∀ h, fresh (data e q a) omega N true h = true := by
    intro h
    rw [← P4AOriginalFiniteFallbackOccurrence.empty_eq
      (P4AFallbackCanonicalBanks.bank 0) (data e q a) omega N]
    exact P4AOriginalFiniteFallbackOccurrence.positive _ _ _ _ _
  exact P4AOriginalLaterSixthHighDispatch.dispatch_later n (data e q a) omega N _ hU

/-- Read the existing exact telescope on the literal final raw coefficient. -/
theorem normalized_final_eq_scalar
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    normalize N (rawRoot (finalPolicy m r n e q a omega N) N) =
      scalar m r n e q a omega N := by
  rw [P4AOriginalFiniteAll22RawLedger.exact_all22_telescope]
  rfl

theorem eleven_floor_eq_literal_slot :
    P4AOriginalElevenOrderedPayment.originalFloor = currentUpperEighteenGains 6 := by
  norm_num [P4AOriginalElevenOrderedPayment.originalFloor, currentUpperEighteenGains]

/-- The actual fresh root and all nine sixth slots share one schedule.
The q threshold may exceed any earlier requirement. It precedes a and
omega; N may depend on these fixed choices. No early payment is an input. -/
theorem exists_common_root_and_paid_sixth
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E → ∀ qMin : ℕ,
      ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ a omega : ℝ, 0 < omega → omega < thirdPrefixRho →
        omega ≤ a → a ≤ 1 / 800 →
      ∀ᶠ N : ℕ in atTop, Even N →
        2 ≤ N ∧
        normalize N (rawRoot (fresh (data e q a) omega N) N) <
          (∑ i, currentUpperEighteenPositive i) + eta / 4 ∧
        currentUpperEighteenGains 3 - eta / 4 < lowerSaved n e q a omega N ∧
        currentUpperEighteenGains 6 - eta / 4 < lowerEleven n e q a omega N ∧
        P4AOriginalOrderedLaterPaid.original - eta / 4 < lowerLater n e q a omega N := by
  have hquarter : 0 < eta / 4 := by positivity
  obtain ⟨ER, hER, hRoot⟩ := P4AOrderedThirdPositiveRoot.original_four_positive
    (eta / 4) hquarter
  obtain ⟨nS, hSaved⟩ := P4AOriginalOrderedSavedGain.exists_original_G4
    (eta / 4) hquarter
  obtain ⟨nG, hEleven⟩ := P4AOriginalElevenOrderedPayment.exists_original_G7_ordered_payment
    (eta / 4) hquarter
  obtain ⟨nL, hLater⟩ := P4AOriginalOrderedLaterPaid.exists_original_later_payment
    (eta / 4) hquarter
  refine ⟨max nS (max nG nL), ?_⟩
  intro n hn
  have hnS : nS ≤ n := (le_max_left _ _).trans hn
  have hnG : nG ≤ n := (le_max_left nG nL).trans ((le_max_right _ _).trans hn)
  have hnL : nL ≤ n := (le_max_right nG nL).trans ((le_max_right _ _).trans hn)
  obtain ⟨EG, hEG, hG⟩ := hEleven n hnG
  obtain ⟨EL, hEL, hL⟩ := hLater n hnL
  let E : ℝ := min eMax (min ER (min (1 / 64000) (min EG EL)))
  have hE : 0 < E := by
    dsimp only [E]
    exact lt_min heMax (lt_min hER (lt_min (by norm_num) (lt_min hEG hEL)))
  refine ⟨E, hE, min_le_left _ _, ?_⟩
  intro e he heE qMin
  have heRat : 0 < e := by exact_mod_cast he
  have heR : (e : ℝ) < ER :=
    heE.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heS : (e : ℝ) < 1 / 64000 :=
    heE.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have heG : (e : ℝ) < EG :=
    heE.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have heL : (e : ℝ) < EL :=
    heE.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨qR, hqR, hR⟩ := hRoot e he heR
  obtain ⟨qS, _hqS, hS⟩ := hSaved n hnS e he heS
  obtain ⟨qG, _hqG, hGq⟩ := hG e heRat heG
  obtain ⟨qL, _hqL, hLq⟩ := hL e heRat heL
  let q0 : ℕ := max qMin (max qR (max qS (max qG qL)))
  have hRq0 : qR ≤ q0 := (le_max_left _ _).trans (le_max_right _ _)
  have hSq0 : qS ≤ q0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hGq0 : qG ≤ q0 :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hLq0 : qL ≤ q0 :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨q0, hqR.trans_le hRq0, le_max_left _ _, ?_⟩
  intro q hq a omega homega homegaR hwa ha
  have hqR' := hRq0.trans hq
  have hqS' := hSq0.trans hq
  have hqG' := hGq0.trans hq
  have hqL' := hLq0.trans hq
  have ha100 : a ≤ 1 / 100 := ha.trans (by norm_num)
  obtain ⟨NG, _hNG, hGN⟩ := hGq q hqG' a omega ha100 hwa
  filter_upwards [hR q hqR' a omega homega homegaR,
    hS q hqS' a ha, hLq q hqL' a omega ha100 hwa,
    eventually_ge_atTop NG, eventually_ge_atTop (2 : ℕ)]
    with N hRN hSN hLN hNG hN
  intro hEven
  refine ⟨hN, hRN hEven, ?_, ?_, ?_⟩
  · rw [lowerSaved_eq_paid_source]
    exact hSN hEven omega hwa
  · rw [P4AOriginalFiniteAll22RawLedger.lowerEleven_eq_paid_source]
    simpa only [eleven_floor_eq_literal_slot] using hGN N hNG hEven
  · rw [lowerLater_eq_paid_source]
    exact hLN hEven

/-- Insert only the proved nine-slot payment into the actual final ledger.
The other thirteen slots remain their full signed arithmetic quantities.
The final fallback bank m and eighth trim r may be chosen after N here. -/
theorem exists_common_final_raw_upper
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E → ∀ qMin : ℕ,
      ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ a omega : ℝ, 0 < omega → omega < thirdPrefixRho →
        omega ≤ a → a ≤ 1 / 800 →
      ∀ᶠ N : ℕ in atTop, Even N → 2 ≤ N ∧ ∀ m r : ℕ,
        normalize N (rawRoot (finalPolicy m r n e q a omega N) N) <
          (∑ i, currentUpperEighteenPositive i) - paidSixthSlots -
            lowerEarly n e q a omega N - lowerEighth r n e q a omega N -
              upperFallback m r n e q a omega N + eta := by
  obtain ⟨n0, hN⟩ := exists_common_root_and_paid_sixth eta eMax heta heMax
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨E, hE, heMax', hEall⟩ := hN n hn
  refine ⟨E, hE, heMax', ?_⟩
  intro e he heE qMin
  obtain ⟨q0, hq0, hqMin, hQ⟩ := hEall e he heE qMin
  refine ⟨q0, hq0, hqMin, ?_⟩
  intro q hq a omega hw hwR hwa ha
  filter_upwards [hQ q hq a omega hw hwR hwa ha] with N hPaid
  intro hEven
  obtain ⟨hN2, hRoot, hSaved, hEleven, hLater⟩ := hPaid hEven
  refine ⟨hN2, ?_⟩
  intro m r
  rw [normalized_final_eq_scalar]
  unfold scalar paidSixthSlots
  linarith only [hRoot, hSaved, hEleven, hLater]

/-- The same partially paid scalar in the final coefficient's physical
upper expression. Its favorable correction and its one compiler expense
are retained literally; this does not assert a physical density or PP bound. -/
theorem physical_upper_lt_of_scalar
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega u_c B : ℝ)
    {N : ℕ} (hN : 2 ≤ N) (hscalar : scalar m r n e q a omega N < B) :
    upper m r n e q a omega u_c N <
      (B + u_c) * (singularSeries N / Real.log (N : ℝ)) -
        p4aActualPresieveCorrection
          (P4AOriginalFiniteFallbackPolicy.F
            (P4AFallbackCanonicalBanks.bank m) (P4AOriginalFull87HistoryCore.width r)
              n (data e q a) omega N)
          N N ((N : ℝ) ^ omega) (cutoff N) := by
  have h := mul_lt_mul_of_pos_right hscalar (densityScale_pos hN)
  unfold upper
  linarith only [h]

end
end ImbalancedChen.P4AOriginalFiniteAll22PaidSixth
