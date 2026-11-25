import ImbalancedChen.P1OriginalSingletonSmoothLicence
import ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy
import ImbalancedChen.P5OriginalSingletonLowerTrimPaid

/-!
The literal lower trim in the original singleton Atlas.

The discarded weight is (1 - eta) times the original smoothNatural,
with independent lower-wall parameters. It is identified with the same
signed singleton discrepancy before restricting its prime carrier.
The original exact coprime mean and the same Q/rho remain in that identity.

Only the existing prefix primitive budget and sublinear power-log payment
are used. The original lower cut is strictly below N before the divisor
budget is applied, so no zero difference is charged to a divisor bound.
The eventual threshold precedes kap, B, Q and rho.
-/

namespace ImbalancedChen.P1OriginalSingletonAtlasTrim

noncomputable section

open Classical Filter
open scoped BigOperators
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_bounds eta_one)
open P5Z.LicensedOriginalIntegerProfile (listExtension listExtension_ofFn)
open P5Z.IndependentPrimeSourceWordDictionary
  (sourceWord sourceWord_product wordKernel original_prime_discrepancy_words)
open P5Z.ActualLabelledPrimeSmoothCharts (primeTuples)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (trimReserve)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence smoothNatural smooth_range)
open P5OriginalSharpPrime (originalLowerCut)
open P5OriginalSingletonLowerTrimPaid
  (exists_prefix_primitive_budget eventually_originalLowerCut_lt)

/-- The original discarded weight, including its separate complete-product eta. -/
def trimNaturalWeight (kap kap0 : ℝ) (B N p : ℕ) : ℝ :=
  (1 - eta ((p : ℝ) / (N : ℝ) ^ (1 - kap0))) * smoothNatural kap B N p

private theorem trimNaturalWeight_bounds (kap kap0 : ℝ) (B N p : ℕ) :
    0 ≤ trimNaturalWeight kap kap0 B N p ∧ trimNaturalWeight kap kap0 B N p ≤ 1 := by
  have hE := eta_bounds ((p : ℝ) / (N : ℝ) ^ (1 - kap0))
  have hW := smooth_range kap B N p
  have hcut0 : 0 ≤ 1 - eta ((p : ℝ) / (N : ℝ) ^ (1 - kap0)) := sub_nonneg.mpr hE.2
  have hcut1 : 1 - eta ((p : ℝ) / (N : ℝ) ^ (1 - kap0)) ≤ 1 := by linarith
  refine ⟨mul_nonneg hcut0 hW.1, ?_⟩
  exact (mul_le_mul hcut1 hW.2 hW.1 zero_le_one).trans_eq (by norm_num)

private theorem trimNaturalWeight_zero_above_cut (kap kap0 : ℝ) (B N p : ℕ)
    (hN : 0 < N) (hp : originalLowerCut kap0 N < p) :
    trimNaturalWeight kap kap0 B N p = 0 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpower : 0 < (N : ℝ) ^ (1 - kap0) := Real.rpow_pos_of_pos hNr _
  have hceil : 2 * (N : ℝ) ^ (1 - kap0) ≤ (originalLowerCut kap0 N : ℝ) :=
    Nat.le_ceil _
  have hlo : 2 * (N : ℝ) ^ (1 - kap0) ≤ (p : ℝ) :=
    hceil.trans (by exact_mod_cast hp.le)
  have hE : eta ((p : ℝ) / (N : ℝ) ^ (1 - kap0)) = 1 :=
    eta_one ((le_div_iff₀ hpower).mpr hlo)
  simp only [trimNaturalWeight, hE, sub_self, zero_mul]

/-- The original reserve is exactly a real singleton signed discrepancy.
The ambient licence is evaluated at its literal integer input. -/
theorem original_singleton_trimReserve_eq_signedError
    (kap kap0 : ℝ) (B N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    trimReserve (actualLicence kap B N) (2 * N) N kap0 Q (fun q => (rho q : ℂ)) =
      (Part3.primeProductSignedError 1 (2 * N) N Q rho
        (P5S1SingletonPP.singletonWeight (2 * N) (trimNaturalWeight kap kap0 B N)) : ℂ) := by
  let W : List ℕ → ℝ := fun ps =>
    (1 - eta ((ps.prod : ℝ) / (N : ℝ) ^ (1 - kap0))) *
      listExtension (actualLicence kap B N) ps
  have hW : (fun u : Fin 1 → Fin (2 * N + 1) => W (sourceWord u)) =
      P5S1SingletonPP.singletonWeight (2 * N) (trimNaturalWeight kap kap0 B N) := by
    funext u
    have hL : listExtension (actualLicence kap B N) (sourceWord u) =
        smoothNatural kap B N (u 0).val := by
      rw [sourceWord, listExtension_ofFn]
      rfl
    dsimp only [W]
    rw [sourceWord_product, P5S1SingletonPP.labelledProduct_singleton, hL]
    rfl
  have hdict := original_prime_discrepancy_words 1 (2 * N) N Q rho W
  rw [hW] at hdict
  change _ = ∑ ps ∈ primeTuples (2 * N) 1,
    (W ps : ℂ) * wordKernel Q (fun q => (rho q : ℂ)) N ps at hdict
  simpa only [trimReserve, W, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one] using hdict.symm

/-- The zero extension removes only source primes above the original lower cut.
Both the congruence count and exact coprime mean keep the same finite carrier. -/
theorem original_singleton_trimReserve_eq_prefix
    (kap kap0 : ℝ) (B N : ℕ) (hN : 0 < N)
    (hcut : originalLowerCut kap0 N ≤ 2 * N) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    trimReserve (actualLicence kap B N) (2 * N) N kap0 Q (fun q => (rho q : ℂ)) =
      ((∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy
        (chenPrimePrefix (originalLowerCut kap0 N))
        (trimNaturalWeight kap kap0 B N) N q : ℝ) : ℂ) := by
  rw [original_singleton_trimReserve_eq_signedError,
    P5S1SingletonPP.primeProductSignedError_singleton_eq]
  apply congrArg (fun x : ℝ => (x : ℂ))
  apply Finset.sum_congr rfl
  intro q _
  apply congrArg (fun x : ℝ => rho q * x)
  apply finitePrimitiveDiscrepancy_eq_of_subset
  · intro p hp
    obtain ⟨hpY, hprime⟩ := mem_chenPrimePrefix.mp hp
    exact mem_chenPrimePrefix.mpr ⟨hpY.trans hcut, hprime⟩
  · intro p hp hn
    have hpY : originalLowerCut kap0 N < p := by
      by_contra h
      exact hn (mem_chenPrimePrefix.mpr
        ⟨Nat.le_of_not_gt h, (mem_chenPrimePrefix.mp hp).2⟩)
    exact trimNaturalWeight_zero_above_cut kap kap0 B N p hN hpY

/-- The manuscript's discarded singleton products are paid uniformly in the
original smooth profile and in every bounded signed coefficient on Q ⊆ [1,N]. -/
theorem eventually_original_singleton_atlas_trim_singularNormalization
    (kap0 tol : ℝ) (hkap0 : 0 < kap0) (hkap01 : kap0 < 1) (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ) (B : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q, |rho q| ≤ 1) →
      ‖trimReserve (actualLicence kap B N) (2 * N) N kap0 Q
          (fun q => (rho q : ℂ))‖ ≤ tol * singularNormalization N := by
  obtain ⟨C, hC, H⟩ := exists_prefix_primitive_budget (show 0 < kap0 / 2 by positivity)
  filter_upwards [eventually_originalLowerCut_lt kap0 hkap0 hkap01,
    eventually_powerLog_le_singularNormalization (3 * C) (1 - kap0 / 2) 0
      (by linarith) (tol / 3) (by positivity),
    eventually_powerLog_le_singularNormalization 12 (1 - kap0) 0
      (by linarith) (tol / 3) (by positivity),
    eventually_powerLog_le_singularNormalization 12 (1 - kap0) 1
      (by linarith) (tol / 3) (by positivity),
    eventually_ge_atTop (2 : ℕ)] with N hcut h1 h2 h3 hN
  intro kap B Q rho hQ hrho
  have hNpos : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog := Real.log_nonneg hN1
  have hbound := H N (originalLowerCut kap0 N) N
    (chenPrimePrefix (originalLowerCut kap0 N)) Q rho (trimNaturalWeight kap kap0 B N)
    hcut.1
    (fun p hp => Finset.mem_Icc.mpr
      ⟨(mem_chenPrimePrefix.mp hp).2.pos, (mem_chenPrimePrefix.mp hp).1⟩)
    hQ hrho (fun p _ => by
      obtain ⟨ha, hb⟩ := trimNaturalWeight_bounds kap kap0 B N p
      simpa only [abs_of_nonneg ha] using hb)
  rw [max_eq_right hN1] at hbound
  rw [original_singleton_trimReserve_eq_prefix kap kap0 B N hNpos (by omega),
    Complex.norm_real, Real.norm_eq_abs]
  have hpower : (N : ℝ) ^ (1 - kap0) * (N : ℝ) ^ (kap0 / 2) =
      (N : ℝ) ^ (1 - kap0 / 2) := by
    rw [← Real.rpow_add hNr]
    congr 1
    ring
  calc
    _ ≤ (3 * (N : ℝ) ^ (1 - kap0)) *
        (C * (N : ℝ) ^ (kap0 / 2) + 4 * (1 + Real.log (N : ℝ))) :=
      hbound.trans (mul_le_mul_of_nonneg_right hcut.2 (by positivity))
    _ = 3 * C * (N : ℝ) ^ (1 - kap0 / 2) + 12 * (N : ℝ) ^ (1 - kap0) +
        12 * (N : ℝ) ^ (1 - kap0) * Real.log (N : ℝ) := by
      calc
        _ = 3 * C * ((N : ℝ) ^ (1 - kap0) * (N : ℝ) ^ (kap0 / 2)) +
            12 * (N : ℝ) ^ (1 - kap0) +
            12 * (N : ℝ) ^ (1 - kap0) * Real.log (N : ℝ) := by ring
        _ = _ := by rw [hpower]
    _ ≤ tol * singularNormalization N := by
      simp only [pow_zero, pow_one, mul_one] at h1 h2 h3
      linarith only [h1, h2, h3]

end
end ImbalancedChen.P1OriginalSingletonAtlasTrim
