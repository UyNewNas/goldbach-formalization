import ImbalancedChen.P4AOriginalFiniteAll22Nineteen
import ImbalancedChen.P4AOriginalEarlyFinitePayment

/-!
Static public extraction of the existing FineCofinalCoefficient hRawClean
argument. UNCOMPILED; no kernel or publication status is asserted.

The two published suppliers choose one cofinal q for the same actual
finalPolicy, whose data is P4AOriginalNewFifthUnion.data. The early-payment
threshold is uniform in omega ≤ a. The final threshold below may depend
on omega, as in the nineteen-slot supplier. No beta/k compiler selection
is needed for this raw estimate.
-/
namespace ImbalancedChen.P1OriginalFinalPolicyRawBound

noncomputable section
open Filter Topology
open scoped Classical
open P4AOriginalFull87RawChronology (rawRoot)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFiniteAll22RawLedger (finalPolicy)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P4AAll22OriginalKLedger20261024zSourceOnly (quotedAll22Raw)

/-- The actual final raw coefficient, with all original slots paid at
one cofinal mesh. The cutoff and mesh restrictions retain the original
supplier order; the eventual target threshold is chosen after omega. -/
theorem exists_cofinal_final_raw_upper
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ h : ℝ, 0 < h ∧
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r →
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧
    ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E →
    ∀ a : ℝ, 0 < a → a ≤ 1 / 800 → ∀ qMin mMin : ℕ,
    ∃ q : ℕ, qMin ≤ q ∧ 0 < q ∧ 256 ∣ q ∧ mMin ≤ refinedMesh q ∧
    ∀ omega : ℝ, 0 < omega → omega < thirdPrefixRho →
      omega ≤ a → omega ≤ h →
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      normalize N (rawRoot (finalPolicy m r n e q a omega N) N) <
        quotedAll22Raw + eta := by
  have hhalf : 0 < eta / 2 := half_pos heta
  obtain ⟨h, hh, m0, hM⟩ :=
    P4AOriginalFiniteAll22Nineteen.exists_final_raw_upper_with_early_defect
      (eta / 2) eMax hhalf heMax
  obtain ⟨nE, hEarly⟩ :=
    P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect (eta / 2) hhalf
  refine ⟨h, hh, m0, ?_⟩
  intro m hm
  obtain ⟨r0, hR⟩ := hM m hm
  refine ⟨r0, ?_⟩
  intro r hr
  obtain ⟨nC, hC⟩ := hR r hr
  refine ⟨max nC nE, ?_⟩
  intro n hn
  obtain ⟨EC, hEC, hECmax, hCE⟩ := hC n ((le_max_left _ _).trans hn)
  obtain ⟨EE, hEE, hEEall⟩ := hEarly n ((le_max_right _ _).trans hn)
  refine ⟨min EC EE, lt_min hEC hEE, (min_le_left _ _).trans hECmax, ?_⟩
  intro e he heE a ha haSmall qMin mMin
  have heRat : 0 < e := by exact_mod_cast he
  obtain ⟨q0, hq0, hqMin, hQ⟩ :=
    hCE e he (heE.trans_le (min_le_left _ _)) qMin
  obtain ⟨q, hq, hqpos, hqdiv, hmesh, NE, hNE, hEN⟩ :=
    hEEall e heRat (heE.trans_le (min_le_right _ _)) a ha haSmall q0 mMin
  refine ⟨q, hqMin.trans hq, hqpos, hqdiv, hmesh, ?_⟩
  intro omega homega homegaR hwa hwh
  obtain ⟨NR, hRN⟩ := eventually_atTop.mp
    (hQ q hq a omega homega homegaR hwa hwh haSmall)
  refine ⟨max NR NE, hNE.trans (le_max_right _ _), ?_⟩
  intro N hN hEven
  have hNR' : NR ≤ N := (le_max_left _ _).trans hN
  have hNE' : NE ≤ N := (le_max_right _ _).trans hN
  obtain ⟨_hNRaw, hRaw⟩ := hRN N hNR' hEven
  have hDefect := hEN omega hwa N hNE' hEven
  linarith only [hRaw, hDefect]

end
end ImbalancedChen.P1OriginalFinalPolicyRawBound
