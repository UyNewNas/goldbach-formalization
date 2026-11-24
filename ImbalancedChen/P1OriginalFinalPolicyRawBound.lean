import ImbalancedChen.P4AOriginalFiniteAll22Nineteen
import ImbalancedChen.P4AOriginalEarlyFinitePayment

/-!
RECONSTRUCTED SOURCE CANDIDATE / NOT YET COMPILED OR KERNEL ACCEPTED.

The prior P1 output candidate is named in the published continuation records,
but its source body is not present in the pinned repository. This file is a new
minimal extraction of the already-written `hRawClean` composition in
`P4AOriginalFiniteAll22FineCofinalCoefficient`.

It reuses the nineteen-slot raw estimate and the actual early-defect payment.
It does not reprove the twenty-two primitive terms, assume a target density,
or assert a distribution estimate. The policy is literally the existing
`P4AOriginalFiniteAll22RawLedger.finalPolicy`.
-/

set_option autoImplicit false

namespace ImbalancedChen.P1OriginalFinalPolicyRawBound

noncomputable section
open Filter Topology
open scoped Classical
open P4AOriginalFull87RawChronology (rawRoot)
open P4AOriginalFiniteAll22RawLedger (finalPolicy)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P5OriginalCommonPositivePresieve (normalize)
open P4AAll22OriginalKLedger20261024zSourceOnly (quotedAll22Raw)

/-- The complete original twenty-two-slot raw upper bound on the literal
finite fallback policy. One common q satisfies the nineteen-slot threshold,
the original early-payment divisibility, and the requested refined mesh.
The positive cutoff ceiling is chosen first; q is chosen before omega, and
the eventual target threshold may depend on omega. -/
theorem exists_cofinal_final_raw_upper
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ h : ℝ, 0 < h ∧
    ∃ m0 : ℕ, ∀ m ≥ m0,
    ∃ r0 : ℕ, ∀ r ≥ r0,
    ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧
    ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E →
    ∀ a : ℝ, 0 < a → a ≤ 1 / 800 →
    ∀ qMin mMin : ℕ,
    ∃ q : ℕ, qMin ≤ q ∧ 0 < q ∧ 256 ∣ q ∧ mMin ≤ refinedMesh q ∧
    ∀ omega : ℝ, 0 < omega → omega < thirdPrefixRho →
      omega ≤ a → omega ≤ h →
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
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
  obtain ⟨q0, _hq0, hqMin, hQ⟩ :=
    hCE e he (heE.trans_le (min_le_left _ _)) qMin
  obtain ⟨q, hq, hqpos, hqdiv, hmesh, NE, hNE, hEN⟩ :=
    hEEall e heRat (heE.trans_le (min_le_right _ _)) a ha haSmall q0 mMin
  refine ⟨q, hqMin.trans hq, hqpos, hqdiv, hmesh, ?_⟩
  intro omega homega homegaR hwa hwh
  obtain ⟨NR, hRN⟩ := eventually_atTop.mp
    (hQ q hq a omega homega homegaR hwa hwh haSmall)
  refine ⟨max NR NE, hNE.trans (le_max_right _ _), ?_⟩
  intro N hN hEven
  have hNR : NR ≤ N := (le_max_left _ _).trans hN
  have hNE' : NE ≤ N := (le_max_right _ _).trans hN
  obtain ⟨_hNRaw, hRaw⟩ := hRN N hNR hEven
  have hDefect := hEN omega hwa N hNE' hEven
  linarith only [hRaw, hDefect]

end
end ImbalancedChen.P1OriginalFinalPolicyRawBound
