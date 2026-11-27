import ImbalancedChen.P3OriginalU5JointRectangleDensity
import ImbalancedChen.P3OriginalU5JointClassicalPayment
import ImbalancedChen.P5zElevenErrorTransport
import ImbalancedChen.UniformPrimeTail
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem

/-! The correction for the exact coprime prime mean and the centre is paid
on the occupied complete moduli of the joint signed coefficient. The real
rectangle gives an original U5 count lower bound with its exact signed
high-modulus primitive remainder. -/

namespace ImbalancedChen.P3OriginalU5JointCountReserve

noncomputable section
open Filter
open scoped Classical BigOperators
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)
open P2GammaU5PlateauGeometry (rectangle rectangle_subset_pairSupport)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairSourceReceiver (PairRange)
open P3OriginalU5CoarseRootV (meshStep)
open P3OriginalU5JointBetaAttachment (rho)
open P3OriginalU5JointClassicalPayment (correction correctionKernel count_account density
  exists_joint_classical_payment highPrimitive lowPrimitive moduliOn physical_data_on physical_pushforward
  physicalRho physicalRho_at_original)
open P5CausalPrimeCorrectionPayment (atomCost atomCost_nonneg atomCost_le_log)
open P5OriginalU5CausalFinite (attachment_gates cutoff pairSupport smallCutoff)
open P5OriginalU5PlateauPrimeBV (fullModulus)

/-- Each active full modulus has one original row, and its two prime
correction terms cost at most twice the binary logarithm of the target. -/
theorem abs_joint_correction_le (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    (m : ℕ) {N : ℕ} (hN : 1 ≤ N) {epsilon : ℝ} (hw : smallCutoff N epsilon ≤ cutoff N)
    (tau : ℝ) {T : Finset (ℕ × ℕ)} (hT : T ⊆ pairSupport N)
    (hcap : ∀ t ∈ T, ∀ k : ℕ, rho R bank b m N epsilon tau t k ≠ 0 →
      (fullModulus t k : ℝ) < (N : ℝ) ^ (599/1000 : ℝ)) :
    |correction R bank b m N epsilon tau T| ≤
      (2 / Real.log 2) * (N : ℝ) ^ (599/1000 : ℝ) * Real.log (N : ℝ) := by
  let X := (N : ℝ) ^ (599/1000 : ℝ)
  let A := 2 * (Real.log (N : ℝ) / Real.log 2)
  let w := physicalRho R bank b m N epsilon tau
  let S := moduliOn T N epsilon
  let active := S.filter (fun q => w q ≠ 0)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : 0 ≤ X := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hXN : X ≤ (N : ℝ) := by
    simpa only [X, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (599/1000 : ℝ) ≤ 1)
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (div_nonneg (Real.log_nonneg hNr) (Real.log_nonneg (by norm_num)))
  have hbound (q : ℕ) (hq : q ∈ S) (hn : w q ≠ 0) : (q : ℝ) < X := by
    obtain ⟨⟨t,k⟩, htag, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ht, hk⟩ := Finset.mem_sigma.mp htag
    have heq := physicalRho_at_original R bank b m hw tau (hT ht) hk
    exact hcap t ht k (fun hz => hn (heq.trans hz))
  have hsub : active ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro q hq
    obtain ⟨hm, hn⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(physical_data_on R bank b m hw tau hT hm).1,
      (Nat.le_floor_iff hX).mpr (hbound q hm hn).le⟩
  have hcard : (active.card : ℝ) ≤ X := by
    have h := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le hX)
  rw [correction, ← physical_pushforward R bank b m hw tau hT]
  change |∑ q ∈ S, w q * correctionKernel N q| ≤ _
  calc
    _ ≤ ∑ q ∈ S, |w q * correctionKernel N q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ S, if w q ≠ 0 then A else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hn : w q = 0
      · simp [hn]
      · rw [if_pos hn, abs_mul]
        have hqN : q ≤ N := by exact_mod_cast (hbound q hq hn).le.trans hXN
        have hd := physical_data_on R bank b m hw tau hT hq
        have hpos : 0 ≤ correctionKernel N q := by
          simpa only [atomCost, one_mul, correctionKernel] using atomCost_nonneg N 1 q
        have hk : correctionKernel N q ≤ A := by
          simpa only [atomCost, one_mul, correctionKernel, A] using
            atomCost_le_log hN (b := 1) (by decide) hd.1 (by simpa only [one_mul] using hqN)
        rw [abs_of_nonneg hpos]
        exact (mul_le_mul_of_nonneg_right hd.2.2 hpos).trans ((one_mul _).le.trans hk)
    _ = (active.card : ℝ) * A := by
      rw [← Finset.sum_filter]
      simp only [active, Finset.sum_const, nsmul_eq_mul]
    _ ≤ X * A := mul_le_mul_of_nonneg_right hcard hA
    _ = _ := by dsimp only [X, A]; ring

/-- The absolute cost is negligible uniformly in every later marked
subset and joint coefficient whose actual nonzero support meets its cap. -/
theorem eventually_joint_correction_payment (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
      (b : ℚ) (m : ℕ) (epsilon tau : ℝ), smallCutoff N epsilon ≤ cutoff N →
      ∀ T : Finset (ℕ × ℕ), T ⊆ pairSupport N →
        (∀ t ∈ T, ∀ k : ℕ, rho R bank b m N epsilon tau t k ≠ 0 →
          (fullModulus t k : ℝ) < (N : ℝ) ^ (599/1000 : ℝ)) →
        |correction R bank b m N epsilon tau T| ≤ eta * singularNormalization N := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_powerLog_le_singularNormalization (2 / Real.log 2) (599/1000) 1 (by norm_num) eta heta]
    with N hN hp
  intro R mesh bank b m epsilon tau hw T hT hcap
  exact (abs_joint_correction_le R bank b m hN hw tau hT hcap).trans (by simpa only [pow_one] using hp)

private theorem eventually_primePrefix_lower :
    ∀ᶠ N : ℕ in atTop, (1/2 : ℝ) * ((N : ℝ) / Real.log (N : ℝ)) ≤ ((chenPrimePrefix N).card : ℝ) := by
  obtain ⟨X, _, hX⟩ := exists_primeCounting_real_relative_error_threshold_of_real_pnt
    (by simpa using AnalyticNumberTheory.PrimeDistribution.primeCounting_asymptotic_real)
    (1/2) (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop X)] with N hN
  have he := (abs_le.mp (hX (N : ℝ) hN).2).1
  rw [Nat.floor_natCast] at he
  have hp : chenPrimePrefix N = N.primesLE := Finset.ext (fun _ => mem_chenPrimePrefix.trans Nat.mem_primesLE.symm)
  rw [hp, Nat.primesLE_card_eq_primeCounting]
  linarith only [he]

/-- The actual U5 count dominates a positive singular normalization plus
the literal signed high-modulus discrepancy of the same rectangular rho.
The BV cutoff is fixed before the receiver, the positive constant before
the meshes, and each bank is fixed before its width and target threshold. -/
theorem exists_joint_rectangle_count_reserve :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : PairRange, ∃ c : ℝ, 0 < c ∧
      ∀ epsilonMax : ℝ, 0 < epsilonMax →
        ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧ epsilon < 1/272 ∧
          ∀ m : ℕ, meshStep R m ≤ 1/32000 → ∀ {mesh : ℕ} (bank : CandidateBank mesh),
            ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
              ∀ tau : ℝ, 0 < tau → tau ≤ tau0 → ∀ N ≥ N0, Even N →
                c * singularNormalization N +
                  highPrimitive R bank (1/1000) m N epsilon tau (rectangle N) (panModulusCutoff N B) ≤
                    currentChenUpsilon5 N ∧
                |lowPrimitive R bank (1/1000) m N epsilon tau (rectangle N) (panModulusCutoff N B)| +
                  |correction R bank (1/1000) m N epsilon tau (rectangle N)| ≤ c * singularNormalization N ∧
                ∀ (t : ℕ × ℕ) (k : ℕ), rho R bank (1/1000) m N epsilon tau t k ≠ 0 →
                  (fullModulus t k : ℝ) < (N : ℝ) ^ (599/1000 : ℝ) := by
  obtain ⟨B, hB, C, _, hBV⟩ := exists_joint_classical_payment 3
  refine ⟨B, hB, ?_⟩
  intro R
  obtain ⟨c, hc, hdensity⟩ := P3OriginalU5JointRectangleDensity.exists_joint_rectangle_positive_density R
  have heta : 0 < c/8 := by positivity
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp ((hBV.and (eventually_joint_correction_payment (c/8) heta)).and
    ((p5z_eventually_logCube_le_singularNormalization C (c/8) heta).and eventually_primePrefix_lower))
  refine ⟨c/4, by positivity, ?_⟩
  intro epsilonMax hmax
  obtain ⟨epsilon, he, he8, heMax, he272, hres⟩ := hdensity epsilonMax hmax
  refine ⟨epsilon, he, he8, heMax, he272, ?_⟩
  intro m hm mesh bank
  obtain ⟨tau0, htau0, Nd, hNd, hr⟩ := hres m hm bank
  refine ⟨tau0, htau0, max Nd Ne, hNd.trans (le_max_left _ _), ?_⟩
  intro tau htau ht N hN hEven
  have hdN := (le_max_left Nd Ne).trans hN
  have hN2 := hNd.trans hdN
  obtain ⟨hden, hcap⟩ := hr tau htau ht N hdN hEven
  obtain ⟨⟨hlow, hcorr⟩, hbvPaid, hpi⟩ := hNe N ((le_max_right _ _).trans hN)
  have hT := rectangle_subset_pairSupport hN2
  have hw := (attachment_gates hN2 he he8).2.2
  have hlowPaid := (hlow R bank (1/1000) m epsilon tau he he8 (rectangle N) hT).trans hbvPaid
  have hcPaid := hcorr R bank (1/1000) m epsilon tau hw (rectangle N) hT (fun t _ => hcap t)
  let D := density R bank (1/1000) m N epsilon tau (rectangle N)
  let g := c * singularSeries N / Real.log (N : ℝ)
  have hg : 0 ≤ g := div_nonneg (mul_nonneg hc.le (singularSeries_pos N).le)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  have hD : g ≤ D := hden
  have hmain : (c/2) * singularNormalization N ≤ ((chenPrimePrefix N).card : ℝ) * D := by
    calc
      _ = ((1/2 : ℝ) * ((N : ℝ) / Real.log (N : ℝ))) * g := by
        dsimp only [singularNormalization, g]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ _ := mul_le_mul hpi hD hg (Nat.cast_nonneg _)
  have hcount := count_account R bank (1/1000) m hN2 he he8 tau hT (panModulusCutoff N B)
  change ((chenPrimePrefix N).card : ℝ) * D + _ - _ ≤ currentChenUpsilon5 N at hcount
  refine ⟨?_, ?_, hcap⟩
  · have hl := (abs_le.mp hlowPaid).1
    have hca := (le_abs_self _).trans hcPaid
    linarith only [hmain, hcount, hl, hca]
  · linarith only [hlowPaid, hcPaid]

end
end ImbalancedChen.P3OriginalU5JointCountReserve
