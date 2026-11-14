import ImbalancedChen.P1OriginalSingletonMiddleTensor
import ImbalancedChen.P5IndependentTestPrimeChartUniformCutoff

/-!
SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.

The original singleton chart uses the real narrow profile, prime cap 2*N,
and the unchanged pre-HB cutoff. Its rough-prime correction is eventually
exactly zero, uniformly in the collar order, chart, complete modulus set
and signed coefficient. The cutoff supplier is applied at the independent
prime cap 2*N; the moving residue and physical target remain N.

No estimate for medium, two-long, proper powers, the historical middle
differences, or the whole singleton discrepancy is asserted here.
-/
namespace ImbalancedChen.P1OriginalSingletonRoughPrimeReserveZero
noncomputable section
open Classical Filter
open scoped BigOperators
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P5Z.LicensedOriginalIntegerProfile
open P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.ActualLabelledPrimeSmoothCharts
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.IndependentTestPrimeChartUniformCutoff
open Part3.AllKLambdaChartCorrection Part3.OriginalProperPowerActualChart
open P1OriginalSingletonMiddleTensor (singletonAtlas)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free)

/-- The actual profile, without any added arithmetic filter, supplies its
strict target-power floor on the original singleton word. -/
theorem actual_singleton_prime_word_floor
    (kappa : ℝ) (B N : ℕ) (hN : 2 ≤ N) {ps : List ℕ}
    (hps : ps ∈ primeTuples (2*N) 1)
    (hW : listExtension (actualLicence kappa B N) ps ≠ 0) :
    ∀ p ∈ ps, (N : ℝ)^(1-kappa) < (p : ℝ) ∧ (p : ℝ) ≤ (2*N : ℕ) := by
  have hlen := (primeTuples_spec (2*N) 1 hps).1
  have hprofile : P5Z.ActualSingletonLogCollarFamily.profile (1-kappa)
      (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N
      (fun i => (wordVector 1 ps i : ℝ)) ≠ 0 := by
    change integerExtension (actualLicence kappa B N) (wordVector 1 ps) ≠ 0
    rw [←listExtension_ofFn, ofFn_wordVector hlen]
    exact hW
  have hd := P5Z.ActualSingletonLogCollarFamily.logWidth_bounds B hN
  have hs := P5Z.ActualSingletonLogCollarFamily.profile_support_short
    (1-kappa) hd.1 hd.2 hprofile
  intro p hp
  have hp' : p ∈ List.ofFn (wordVector 1 ps) := by
    simpa only [ofFn_wordVector hlen] using hp
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp'
  have hi0 : i = 0 := Subsingleton.elim _ _
  have hlo : (N : ℝ)^(1-kappa) < (p : ℝ) := by
    simpa only [←hi, hi0] using hs.2.1
  have hcap : p ≤ 2*N := ((primeTuples_spec (2*N) 1 hps).2 p hp).2.2
  exact ⟨hlo, by exact_mod_cast hcap⟩

/-- Changing only the ambient cap in the cutoff supplier: this is a
consequence of 2*N <= N^2, not a change of target or smoothing profile. -/
theorem doubled_cap_floor (kappa : ℝ) (hk : kappa < 1)
    (N : ℕ) (hN : 2 ≤ N) :
    ((2*N : ℕ) : ℝ)^((1-kappa)/2) ≤ (N : ℝ)^(1-kappa) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 ≤ (1-kappa)/2 := by linarith
  have hsq : ((2*N : ℕ) : ℝ) ≤ (N : ℝ)^2 := by
    have hp : 0 ≤ (N : ℝ)*((N : ℝ)-2) :=
      mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hNr)
    push_cast
    nlinarith only [hp]
  calc
    ((2*N : ℕ) : ℝ)^((1-kappa)/2) ≤ ((N : ℝ)^2)^((1-kappa)/2) :=
      Real.rpow_le_rpow (by positivity) hsq ha
    _ = (N : ℝ)^(1-kappa) := by
      rw [←Real.rpow_natCast (N : ℝ) 2, ←Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      ring

/-- A nonzero original chart provides its own psi windows and the true
source floor at cap 2*N. The source word is still evaluated at target N. -/
theorem actual_singleton_chart_windows
    (kappa : ℝ) (hk : kappa < 1) (B N : ℕ) (hN : 2 ≤ N)
    (kappa0 : ℝ) {js ps : List ℕ}
    (hjs : js ∈ chartBank (2*N) 1) (hps : ps ∈ primeTuples (2*N) 1)
    (hactive : originalChart (actualLicence kappa B N) N kappa0 js ps ≠ 0) :
    js.length = 1 ∧
      List.Forall₂
        (fun j p => psi P5Z.ActualEtaPsiOccurrenceBudget.chi ((p : ℝ)/R j) ≠ 0 ∧
          R j/2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*R j) js ps ∧
      ∀ p ∈ ps, ((2*N : ℕ) : ℝ)^((1-kappa)/2) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ (2*N : ℕ) := by
  simp only [originalChart, chartTerm, trimmedWeight] at hactive
  have htuple := (mul_ne_zero_iff.mp hactive).1
  have hWc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hactive).2).2
  have hW : listExtension (actualLicence kappa B N) ps ≠ 0 := by
    intro hz
    exact hWc (by simp only [hz, Complex.ofReal_zero])
  have hfloor := actual_singleton_prime_word_floor kappa B N hN hps hW
  refine ⟨(words_spec _ _ _ hjs).1, ?_, ?_⟩
  · exact profile_nonzero_support P5Z.ActualEtaPsiOccurrenceBudget.chi
      (fun t ht => actual_chi_one ht) (fun t ht => actual_chi_zero ht) js ps htuple
  · intro p hp
    exact ⟨(doubled_cap_floor kappa hk N hN).trans (hfloor p hp).1.le, (hfloor p hp).2⟩

/-- One threshold is selected before every original chart, collar order,
complete-modulus carrier and signed coefficient. Every correction term
vanishes on its actual prime word; no absolute-value rho is substituted. -/
theorem exists_original_singleton_roughPrimeReserve_zero
    (K : ℕ) (hK : 1 ≤ K) (kappa : ℝ) (hk : kappa < 1) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ (B : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ)
        (js : List ℕ), js ∈ chartBank (2*N) 1 →
        roughPrimeReserve (actualLicence kappa B N) K (2*N) N kappa0 Q rho js = 0 := by
  have ha : 0 < (1-kappa)/2 := by linarith
  obtain ⟨M0, hcutoff⟩ := independent_test_chart_cutoff_eventual K ((1-kappa)/2) ha
  refine ⟨max 2 M0, le_max_left _ _, ?_⟩
  intro N hN B kappa0 Q rho js hjs
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hMN : M0 ≤ N := (le_max_right _ _).trans hN
  have hM : M0 ≤ 2*N := by omega
  unfold roughPrimeReserve
  apply Finset.sum_eq_zero
  intro ps hps
  by_cases hchart : originalChart (actualLicence kappa B N) N kappa0 js ps = 0
  · simp only [hchart, zero_mul]
  · obtain ⟨hlen, hwin, hsource⟩ :=
      actual_singleton_chart_windows kappa hk B N hN2 kappa0 hjs hps hchart
    have hz : beforeHBCutoff K js < ((2*N : ℕ) : ℝ)^((1-kappa)/2) :=
      hcutoff (2*N) hM 1 (by decide) hK P5Z.ActualEtaPsiOccurrenceBudget.chi
        js ps hlen hwin hsource
    have hprime : primeOnly ps := fun p hp => ((primeTuples_spec (2*N) 1 hps).2 p hp).1
    have hrough : ∀ p ∈ ps, beforeHBCutoff K js < (p : ℝ) :=
      fun p hp => hz.trans_le (hsource p hp).1
    rw [roughWord_one_on_prime_word _ hprime hrough]
    simp only [sub_self, mul_zero, zero_mul]

theorem eventually_original_singleton_roughPrimeReserve_sum_zero
    (K : ℕ) (hK : 1 ≤ K) (kappa : ℝ) (hk : kappa < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ),
      (∑ js ∈ chartBank (2*N) 1,
        roughPrimeReserve (actualLicence kappa B N) K (2*N) N kappa0 Q rho js) = 0 := by
  obtain ⟨N0, _, hz⟩ := exists_original_singleton_roughPrimeReserve_zero K hK kappa hk
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro B kappa0 Q rho
  exact Finset.sum_eq_zero (fun js hjs => hz N hN B kappa0 Q rho js hjs)

/-- Read the already defined final-bank singletonAtlas itself. The
physical parameter record and free complete-modulus coefficient are the
original objects. Only the proved-zero rough-prime correction disappears. -/
theorem eventually_original_singletonAtlas_roughPrime_paid
    (K : ℕ) (hK : 1 ≤ K) (kappa : ℝ) (hk : kappa < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ P : Params, P.N = N → ∀ kappa0 zeta : ℝ,
      singletonAtlas P kappa K kappa0 zeta =
        let L := actualLicence kappa 6 P.N
        let S := products P
        let c := fun d => (free P d : ℂ)
        trimReserve L (2*P.N) P.N kappa0 S c +
          ∑ js ∈ chartBank (2*P.N) 1,
            (mediumAtlas L K (2*P.N) P.N kappa0
                (originalMediumLow zeta js) (originalMediumHigh zeta js) S c js +
              noMediumAtlas L K (2*P.N) P.N kappa0
                (originalMediumLow zeta js) (originalMediumHigh zeta js) S c js -
              properPowerReserve L K (2*P.N) P.N kappa0 S c js) := by
  obtain ⟨N0, _, hz⟩ := exists_original_singleton_roughPrimeReserve_zero K hK kappa hk
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro P hPN kappa0 zeta
  subst N
  unfold singletonAtlas
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [hz P.N hN 6 kappa0 (products P) (fun d => (free P d : ℂ)) js hjs, add_zero]

end
end ImbalancedChen.P1OriginalSingletonRoughPrimeReserveZero
