import ImbalancedChen.P5OriginalSharpPrimeSynthesis
import ImbalancedChen.Part3PolynomialResidueDivisorBound

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
The source is the ORIGINAL independent singleton prime testword, not a
marked physical prefix or a residual rough divisor. Its actual lowerTrim
is paid after the complete signed modulus sum, retaining the exact
coprime mean. The zero difference N-p is excluded BEFORE using divisors.
No smooth PP conclusion, adopted CapPlan identity or all-rank cover is an
input or conclusion of this local source-restoration theorem.
-/
namespace ImbalancedChen.P5OriginalSingletonLowerTrimPaid
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalPrimeEndpoint P5OriginalSharpPrime
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem primePrefix_card_le (Y : ℕ) : (chenPrimePrefix Y).card ≤ Y := by
  have hsub : chenPrimePrefix Y ⊆ Finset.Icc 1 Y := by
    intro p hp
    have hd := mem_chenPrimePrefix.mp hp
    exact Finset.mem_Icc.mpr ⟨hd.2.pos, hd.1⟩
  simpa using Finset.card_le_card hsub

-- The single divisor constant is chosen before N, every source, every
-- modulus set and every signed weight. It is DERIVED from the existing
-- elementary subpower divisor theorem, not an assumed reserve budget.
theorem exists_prefix_primitive_budget {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Y M : ℕ) (S Q : Finset ℕ)
      (rho delta : ℕ → ℝ),
      Y < N → S ⊆ Finset.Icc 1 Y → Q ⊆ Finset.Icc 1 M →
      (∀ q ∈ Q, |rho q| ≤ 1) → (∀ p ∈ S, |delta p| ≤ 1) →
      |∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy S delta N q| ≤
        (Y : ℝ) * (C * (N : ℝ) ^ eps +
          4 * (1 + Real.log (max 1 (M : ℝ)))) := by
  obtain ⟨C, hC, htau⟩ :=
    Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
      (k := 2) (by norm_num) heps
  refine ⟨C, hC, ?_⟩
  intro N Y M S Q rho delta hYN hS hQ hrho hdelta
  have hcard : (S.card : ℝ) ≤ Y := by
    exact_mod_cast (show S.card ≤ Y by simpa using Finset.card_le_card hS)
  have ht (p : ℕ) (hp : p ∈ S) :
      ((distance N p).divisors.card : ℝ) ≤ C * (N : ℝ) ^ eps := by
    have hpY := (Finset.mem_Icc.mp (hS hp)).2
    have hpN : p < N := hpY.trans_lt hYN
    have hdist : distance N p = N - p := if_pos hpN.le
    have hpos : 0 < distance N p := by rw [hdist]; omega
    have hle : distance N p ≤ N := by rw [hdist]; omega
    have hsmall : ((distance N p).divisors.card : ℝ) ≤
        C * (distance N p : ℝ) ^ eps := by
      simpa only [fouvryTau_two] using htau (distance N p) hpos
    exact hsmall.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) heps.le) hC.le)
  have hAP : |∑ q ∈ Q, rho q * finiteCongruenceMass S delta N q| ≤
      (Y : ℝ) * (C * (N : ℝ) ^ eps) := by
    have heq : (∑ q ∈ Q, rho q * finiteCongruenceMass S delta N q) =
        ∑ p ∈ S, delta p * ∑ q ∈ Q with Nat.ModEq q p N, rho q := by
      simp only [finiteCongruenceMass, Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      by_cases h : Nat.ModEq q p N <;> simp [h, mul_comm]
    rw [heq]
    calc
      _ ≤ ∑ p ∈ S, |delta p * ∑ q ∈ Q with Nat.ModEq q p N, rho q| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, C * (N : ℝ) ^ eps := by
        apply Finset.sum_le_sum
        intro p hp
        have hpN : p < N := (Finset.mem_Icc.mp (hS hp)).2.trans_lt hYN
        rw [abs_mul]
        calc
          _ ≤ 1 * ∑ q ∈ Q with Nat.ModEq q p N, |rho q| :=
            mul_le_mul (hdelta p hp) (Finset.abs_sum_le_sum_abs _ _)
              (abs_nonneg _) zero_le_one
          _ ≤ ((distance N p).divisors.card : ℝ) := by
            rw [one_mul]
            exact sum_abs_rho_congruence_le_divisors Q rho N p hpN.ne hrho
          _ ≤ _ := ht p hp
      _ = (S.card : ℝ) * (C * (N : ℝ) ^ eps) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hrec : (∑ q ∈ Q, |rho q| / (Nat.totient q : ℝ)) ≤
      4 * (1 + Real.log (max 1 (M : ℝ))) := by
    refine le_trans ?_ (sum_reciprocal_totient_subset_le_log Q M hQ)
    apply Finset.sum_le_sum
    intro q hq
    exact div_le_div_of_nonneg_right (hrho q hq) (Nat.cast_nonneg _)
  have hmean : |∑ q ∈ Q, rho q *
      (finiteCoprimeMass S delta q / (Nat.totient q : ℝ))| ≤
      (Y : ℝ) * (4 * (1 + Real.log (max 1 (M : ℝ)))) := by
    refine (abs_signed_coprime_mean_le S Q rho delta hdelta).trans ?_
    exact mul_le_mul hcard hrec
      (Finset.sum_nonneg (fun q hq => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
      (Nat.cast_nonneg _)
  have heq : (∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy S delta N q) =
      (∑ q ∈ Q, rho q * finiteCongruenceMass S delta N q) -
        ∑ q ∈ Q, rho q * (finiteCoprimeMass S delta q / (Nat.totient q : ℝ)) := by
    simp only [finitePrimitiveDiscrepancy, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add hAP hmean).trans_eq (by ring))

theorem lowerTrim_singleton_eq_prefix (P N Y : ℕ) (hYP : Y ≤ P)
    (Q : Finset ℕ) (rho smooth : ℕ → ℝ) :
    Part3.primeProductSignedError 1 P N Q rho
      (P5S1SingletonPP.singletonWeight P (lowerTrim N Y smooth)) =
      ∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy
        (chenPrimePrefix Y) (lowerTrim N Y smooth) N q := by
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq]
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (fun x : ℝ => rho q * x)
  apply finitePrimitiveDiscrepancy_eq_of_subset
  · intro p hp
    have hd := mem_chenPrimePrefix.mp hp
    exact mem_chenPrimePrefix.mpr ⟨hd.1.trans hYP, hd.2⟩
  · intro p hp hn
    have hpY : Y < p := by
      by_contra h
      exact hn (mem_chenPrimePrefix.mpr
        ⟨Nat.le_of_not_gt h, (mem_chenPrimePrefix.mp hp).2⟩)
    exact lowerTrim_eq_zero_of_lt N Y p smooth hpY

theorem exists_actual_lowerTrim_budget {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (retainEven : List ℕ → Bool)
      (N cap P Y M : ℕ) (w z L : ℝ) (Q : Finset ℕ) (smooth : ℕ → ℝ),
      Y < N → N ≤ P → Q ⊆ Finset.Icc 1 M →
      (∀ p ∈ chenPrimePrefix P, 0 ≤ smooth p ∧ smooth p ≤ 1) →
      |Part3.primeProductSignedError 1 P N Q
        (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight P (lowerTrim N Y smooth))| ≤
        (Y : ℝ) * (C * (N : ℝ) ^ eps +
          4 * (1 + Real.log (max 1 (M : ℝ)))) := by
  obtain ⟨C, hC, hb⟩ := exists_prefix_primitive_budget heps
  refine ⟨C, hC, ?_⟩
  intro retainEven N cap P Y M w z L Q smooth hYN hNP hQ hsmooth
  have hYP : Y ≤ P := hYN.le.trans hNP
  rw [lowerTrim_singleton_eq_prefix P N Y hYP]
  apply hb N Y M (chenPrimePrefix Y) Q _ _ hYN
  · intro p hp
    have hd := mem_chenPrimePrefix.mp hp
    exact Finset.mem_Icc.mpr ⟨hd.2.pos, hd.1⟩
  · exact hQ
  · intro q hq
    exact actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q
  · intro p hp
    have hd := mem_chenPrimePrefix.mp hp
    have hpP := mem_chenPrimePrefix.mpr ⟨hd.1.trans hYP, hd.2⟩
    have hr := lowerTrim_range_of_le N Y p smooth hYN.le (hsmooth p hpP)
    simpa only [abs_of_nonneg hr.1] using hr.2

-- This strict inequality is required before using tau(N-p). In
-- particular no tau(0) or divisor estimate is used at p=N.
theorem eventually_originalLowerCut_lt (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappa1 : kappa < 1) :
    ∀ᶠ N : ℕ in atTop, originalLowerCut kappa N < N ∧
      (originalLowerCut kappa N : ℝ) ≤ 3 * (N : ℝ) ^ (1-kappa) := by
  filter_upwards [eventually_powerLog_le_logAccuracy 3 (1-kappa) 0 0
    (by linarith) (1/2) (by norm_num), eventually_ge_atTop (1 : ℕ)] with N hsmall hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : 1 ≤ (N : ℝ) ^ (1-kappa) :=
    Real.one_le_rpow hNr (by linarith)
  have hceil : (originalLowerCut kappa N : ℝ) ≤
      2 * (N : ℝ) ^ (1-kappa) + 1 := by
    exact (Nat.ceil_lt_add_one (by positivity :
      0 ≤ 2 * (N : ℝ) ^ (1-kappa))).le
  have hY : (originalLowerCut kappa N : ℝ) ≤ 3 * (N : ℝ) ^ (1-kappa) := by
    linarith
  have hhalf : 3 * (N : ℝ) ^ (1-kappa) ≤ (1/2) * (N : ℝ) := by
    simpa only [pow_zero, mul_one, div_one] using hsmall
  refine ⟨?_, hY⟩
  have hlt : (originalLowerCut kappa N : ℝ) < N := by linarith
  exact_mod_cast hlt

-- The actual original lowerTrim now has arbitrary logarithmic accuracy.
-- One threshold precedes the causal plan, all finite moduli and smooth
-- test values. Smooth PP itself has not been assumed or established.
theorem eventually_actual_lowerTrim_logAccuracy (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (A : ℕ)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool)
      (cap P M : ℕ) (w z L : ℝ) (Q : Finset ℕ) (smooth : ℕ → ℝ),
      N ≤ P → M ≤ N → Q ⊆ Finset.Icc 1 M →
      (∀ p ∈ chenPrimePrefix P, 0 ≤ smooth p ∧ smooth p ≤ 1) →
      |Part3.primeProductSignedError 1 P N Q
        (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight P
          (lowerTrim N (originalLowerCut kappa N) smooth))| ≤
        eta * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨C, hC, hb⟩ := exists_actual_lowerTrim_budget
    (show 0 < kappa/2 by positivity)
  filter_upwards [eventually_originalLowerCut_lt kappa hkappa hkappa1,
    eventually_powerLog_le_logAccuracy (3*C) (1-kappa/2) 0 A
      (by linarith) (eta/3) (by positivity),
    eventually_powerLog_le_logAccuracy 12 (1-kappa) 0 A
      (by linarith) (eta/3) (by positivity),
    eventually_powerLog_le_logAccuracy 12 (1-kappa) 1 A
      (by linarith) (eta/3) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with N hcut hAP hM0 hM1 hN
  intro retainEven cap P M w z L Q smooth hNP hMN hQ hsmooth
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hlogM : Real.log (max 1 (M : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hNr (by exact_mod_cast hMN))
  have hbracket : C * (N : ℝ) ^ (kappa/2) +
      4 * (1 + Real.log (max 1 (M : ℝ))) ≤
      C * (N : ℝ) ^ (kappa/2) + 4 * (1 + Real.log (N : ℝ)) := by
    linarith
  have hbracket0 : 0 ≤ C * (N : ℝ) ^ (kappa/2) +
      4 * (1 + Real.log (max 1 (M : ℝ))) := by
    have hl := Real.log_nonneg (le_max_left (1 : ℝ) (M : ℝ))
    positivity
  have hbound := hb retainEven N cap P (originalLowerCut kappa N) M
    w z L Q smooth hcut.1 hNP hQ hsmooth
  calc
    _ ≤ (3 * (N : ℝ) ^ (1-kappa)) *
        (C * (N : ℝ) ^ (kappa/2) + 4 * (1 + Real.log (N : ℝ))) :=
      hbound.trans (mul_le_mul hcut.2 hbracket hbracket0 (by positivity))
    _ = 3*C*(N : ℝ)^(1-kappa/2) + 12*(N : ℝ)^(1-kappa) +
        12*(N : ℝ)^(1-kappa)*Real.log (N : ℝ) := by
      have hprod : (N : ℝ)^(1-kappa) * (N : ℝ)^(kappa/2) =
          (N : ℝ)^(1-kappa/2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      calc
        _ = 3*C*((N : ℝ)^(1-kappa) * (N : ℝ)^(kappa/2)) +
            12*(N : ℝ)^(1-kappa) +
            12*(N : ℝ)^(1-kappa)*Real.log (N : ℝ) := by ring
        _ = _ := by rw [hprod]
    _ ≤ eta * (N : ℝ) / Real.log (N : ℝ)^A := by
      simp only [pow_zero, pow_one, mul_one] at hAP hM0 hM1
      linarith

-- On the original inclusive prime source, the actual low patch is the
-- original unit test. The real smooth caller and its literal lowerTrim
-- are not defined to be the same object on both sides of a binding.
theorem original_singleton_eq_smooth_add_lowerTrim (N Y : ℕ)
    (Q : Finset ℕ) (rho smooth : ℕ → ℝ)
    (hmiddle : ∀ p ∈ chenPrimePrefix N, Y < p → smooth p = 1) :
    Part3.primeProductSignedError 1 N N Q rho
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) =
      Part3.primeProductSignedError 1 N N Q rho
        (P5S1SingletonPP.singletonWeight N smooth) +
      Part3.primeProductSignedError 1 N N Q rho
        (P5S1SingletonPP.singletonWeight N (lowerTrim N Y smooth)) := by
  have hpatch : Part3.primeProductSignedError 1 N N Q rho
      (P5S1SingletonPP.singletonWeight N (patched N Y smooth)) =
      Part3.primeProductSignedError 1 N N Q rho
        (P5S1SingletonPP.singletonWeight N (fun _ => 1)) := by
    rw [P5S1SingletonPP.primeProductSignedError_singleton_eq,
      P5S1SingletonPP.primeProductSignedError_singleton_eq]
    apply Finset.sum_congr rfl
    intro q hq
    apply congrArg (fun x : ℝ => rho q * x)
    apply finitePrimitiveDiscrepancy_congr
    intro p hp
    by_cases hlow : p ≤ Y
    · simp only [patched, if_pos hlow, sharp,
        if_pos (mem_chenPrimePrefix.mp hp).1]
    · simp only [patched, if_neg hlow,
        hmiddle p hp (Nat.lt_of_not_ge hlow)]
  rw [← hpatch]
  exact patched_PP_eq_smooth_add_lowerTrim N N Y Q rho smooth

theorem eventually_original_singleton_smoothing_paid (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (A : ℕ)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool)
      (cap M : ℕ) (w z L : ℝ) (Q : Finset ℕ) (smooth : ℕ → ℝ),
      M ≤ N → Q ⊆ Finset.Icc 1 M →
      (∀ p ∈ chenPrimePrefix N, 0 ≤ smooth p ∧ smooth p ≤ 1) →
      (∀ p ∈ chenPrimePrefix N, originalLowerCut kappa N < p → smooth p = 1) →
      |Part3.primeProductSignedError 1 N N Q
          (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
        Part3.primeProductSignedError 1 N N Q
          (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight N smooth)| ≤
        eta * (N : ℝ) / Real.log (N : ℝ)^A := by
  filter_upwards [eventually_actual_lowerTrim_logAccuracy
    kappa hkappa hkappa1 A eta heta] with N hN
  intro retainEven cap M w z L Q smooth hMN hQ hrange hmiddle
  have hid := original_singleton_eq_smooth_add_lowerTrim N
    (originalLowerCut kappa N) Q
    (actualLowerSmallRoughRho retainEven N cap w z L) smooth hmiddle
  have hbound := hN retainEven cap N M w z L Q smooth le_rfl hMN hQ hrange
  rw [hid, add_sub_cancel_left]
  exact hbound

end
end ImbalancedChen.P5OriginalSingletonLowerTrimPaid
