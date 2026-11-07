import ImbalancedChen.P4BArbitraryWidthUpperPairProfile
import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches
import ImbalancedChen.P5IndependentTestPrimeChartUniformCutoff

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The rough-prime correction in the actual arbitrary-width upper source is
eventually exactly zero.  Its source prime floor is derived from the literal
smoothPhysicalPairOuterRamp, and its chart cutoff is the original pre-HB
cutoff.  One threshold precedes all legal widths, original chart labels,
prime words, trim exponents, finite modulus carriers and signed coefficients.

The fixed maximum rank K is chosen before that threshold, with 2 <= K.
No Family containing artificial absent ranks, support estimate on rho,
distribution bound, density bound or source decomposition licence is used.
-/
namespace ImbalancedChen.P4BActualUpperRoughPrimeReserveZero

noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness P4BArbitraryWidthUpperPairProfile
open P5Z.LicensedOriginalIntegerProfile
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.ActualLabelledPrimeSmoothCharts
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.IndependentTestPrimeChartUniformCutoff
open Part3.AllKLambdaChartCorrection Part3.OriginalProperPowerActualChart

/-- The original independent prime word has the actual ramp's power
floor.  The cap N is the independent test-prime cap, not the coefficient's
enumeration cap or the modulus residual. -/
theorem actual_prime_word_floor
    {b kappa nu r width : ℝ} {N : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    {ps : List ℕ} (hps : ps ∈ primeTuples N 2)
    (hW : listExtension (licence hb hnu hr hw hgap N) ps ≠ 0) :
    ∀ p ∈ ps, (N : ℝ) ^ (nu * r) < (p : ℝ) ∧ (p : ℝ) ≤ N := by
  have hlen := (primeTuples_spec N 2 hps).1
  have hprofile : profile b kappa width N
      (fun i => (wordVector 2 ps i : ℝ)) ≠ 0 := by
    change integerExtension (licence hb hnu hr hw hgap N) (wordVector 2 ps) ≠ 0
    rw [← listExtension_ofFn, ofFn_wordVector hlen]
    exact hW
  have hs := nonzero_data hb hnu hr hw hgap hprofile
  intro p hp
  have hp' : p ∈ List.ofFn (wordVector 2 ps) := by
    simpa only [ofFn_wordVector hlen] using hp
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp'
  have hfloor : (N : ℝ) ^ (nu * r) < (p : ℝ) := by
    simpa only [hi] using hs.2.2.1 i
  have hcap : p ≤ N := ((primeTuples_spec N 2 hps).2 p hp).2.2
  exact ⟨hfloor, by exact_mod_cast hcap⟩

/-- The nonzero ORIGINAL chart supplies its own smooth psi windows and
actual prime floor.  These are conclusions of source membership, not
fields added to a proposed PP certificate. -/
theorem actual_original_chart_windows
    {b kappa nu r width : ℝ} {N : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (kappa0 : ℝ) {js ps : List ℕ}
    (hjs : js ∈ chartBank N 2) (hps : ps ∈ primeTuples N 2)
    (hactive : originalChart (licence hb hnu hr hw hgap N)
      N kappa0 js ps ≠ 0) :
    js.length = 2 ∧
      List.Forall₂
        (fun j p => psi P5Z.ActualEtaPsiOccurrenceBudget.chi ((p : ℝ) / R j) ≠ 0 ∧
          R j / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * R j) js ps ∧
      ∀ p ∈ ps, (N : ℝ) ^ (nu * r) ≤ (p : ℝ) ∧ (p : ℝ) ≤ N := by
  simp only [originalChart, chartTerm, trimmedWeight] at hactive
  have htuple := (mul_ne_zero_iff.mp hactive).1
  have hWc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hactive).2).2
  have hW : listExtension (licence hb hnu hr hw hgap N) ps ≠ 0 := by
    intro hz
    exact hWc (by simp only [hz, Complex.ofReal_zero])
  have hfloor := actual_prime_word_floor hb hnu hr hw hgap hps hW
  refine ⟨(words_spec _ _ _ hjs).1, ?_, ?_⟩
  · exact profile_nonzero_support P5Z.ActualEtaPsiOccurrenceBudget.chi
      (fun t ht => actual_chi_one ht) (fun t ht => actual_chi_zero ht) js ps htuple
  · intro p hp
    exact ⟨(hfloor p hp).1.le, (hfloor p hp).2⟩

/-- The real rough correction vanishes on every original chart, uniformly
over every signed Q/rho and every legal physical width.  No estimate of
the number or total mass of charts is needed for this exact zero. -/
theorem exists_actual_upper_roughPrimeReserve_zero
    (K : ℕ) (hK : 2 ≤ K) {b kappa nu r : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ (width : ℝ) (hw : 0 < width)
        (hgap : 2 * width ≤ baseline b kappa - nu * r)
        (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ)
        (js : List ℕ), js ∈ chartBank N 2 →
        roughPrimeReserve (licence hb hnu hr hw hgap N)
          K N N kappa0 Q rho js = 0 := by
  obtain ⟨N0, hcutoff⟩ :=
    independent_test_chart_cutoff_eventual K (nu * r) (mul_pos hnu hr)
  refine ⟨N0, ?_⟩
  intro N hN width hw hgap kappa0 Q rho js hjs
  unfold roughPrimeReserve
  apply Finset.sum_eq_zero
  intro ps hps
  by_cases hchart : originalChart (licence hb hnu hr hw hgap N)
      N kappa0 js ps = 0
  · simp only [hchart, zero_mul]
  · obtain ⟨hlen, hwin, hsource⟩ :=
      actual_original_chart_windows hb hnu hr hw hgap kappa0 hjs hps hchart
    have hz : beforeHBCutoff K js < (N : ℝ) ^ (nu * r) :=
      hcutoff N hN 2 (by omega) hK P5Z.ActualEtaPsiOccurrenceBudget.chi
        js ps hlen hwin hsource
    have hprime : primeOnly ps :=
      fun p hp => ((primeTuples_spec N 2 hps).2 p hp).1
    have hrough : ∀ p ∈ ps, beforeHBCutoff K js < (p : ℝ) :=
      fun p hp => hz.trans_le (hsource p hp).1
    rw [roughWord_one_on_prime_word _ hprime hrough]
    simp only [sub_self, mul_zero, zero_mul]

/-- The entire original signed chart sum is exactly zero at one common
threshold.  This is already uniform in the final physical coefficient;
the conclusion does not require positivity or an absolute rho bound. -/
theorem eventually_actual_upper_roughPrimeReserve_sum_zero
    (K : ℕ) (hK : 2 ≤ K) {b kappa nu r : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ (width : ℝ) (hw : 0 < width)
      (hgap : 2 * width ≤ baseline b kappa - nu * r)
      (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ),
      (∑ js ∈ chartBank N 2,
        roughPrimeReserve (licence hb hnu hr hw hgap N)
          K N N kappa0 Q rho js) = 0 := by
  obtain ⟨N0, hz⟩ := exists_actual_upper_roughPrimeReserve_zero K hK hb hnu hr
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  intro width hw hgap kappa0 Q rho
  exact Finset.sum_eq_zero (fun js hjs => hz N hN width hw hgap kappa0 Q rho js hjs)

end
end ImbalancedChen.P4BActualUpperRoughPrimeReserveZero
