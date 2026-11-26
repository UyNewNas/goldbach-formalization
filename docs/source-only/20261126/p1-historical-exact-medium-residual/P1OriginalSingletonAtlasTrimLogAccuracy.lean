import ImbalancedChen.P1OriginalSingletonAtlasTrim

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original Atlas trim already has a public exact prefix dictionary and
a public generic prefix budget. This file strengthens its exported rate
to arbitrary logarithmic accuracy, using those suppliers and the existing
power-log payment. It does not repeat their divisor, zero-difference,
source reindexing or asymptotic proofs. Both smoothing parameters and the
same finite Q/rho kernel remain unchanged.
-/

namespace ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_bounds)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (trimReserve)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence smoothNatural smooth_range)
open P5OriginalSharpPrime (originalLowerCut)
open P5OriginalSingletonLowerTrimPaid
  (exists_prefix_primitive_budget eventually_originalLowerCut_lt)
open P1OriginalSingletonAtlasTrim
  (trimNaturalWeight original_singleton_trimReserve_eq_prefix)

/-- A stronger output rate for the original discarded weight. The fixed
threshold precedes the actual profile, collar order and signed Q/rho.
There is no trim-error or smooth-PP estimate among the hypotheses. -/
theorem eventually_original_singleton_atlas_trim_logAccuracy
    (kap0 : ℝ) (hkap0 : 0 < kap0) (hkap01 : kap0 < 1)
    (A : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ) (B : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q, |rho q| ≤ 1) →
      ‖trimReserve (actualLicence kap B N) (2*N) N kap0 Q
          (fun q => (rho q : ℂ))‖ ≤ eps*(N : ℝ)/(Real.log (N : ℝ))^A := by
  obtain ⟨C, hC, hprefix⟩ :=
    exists_prefix_primitive_budget (show 0 < kap0/2 by positivity)
  filter_upwards [eventually_originalLowerCut_lt kap0 hkap0 hkap01,
    eventually_powerLog_le_logAccuracy (3*C) (1-kap0/2) 0 A
      (by linarith) (eps/3) (by positivity),
    eventually_powerLog_le_logAccuracy 12 (1-kap0) 0 A
      (by linarith) (eps/3) (by positivity),
    eventually_powerLog_le_logAccuracy 12 (1-kap0) 1 A
      (by linarith) (eps/3) (by positivity),
    eventually_ge_atTop (2 : ℕ)] with N hcut h1 h2 h3 hN
  intro kap B Q rho hQ hrho
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hbound := hprefix N (originalLowerCut kap0 N) N
    (chenPrimePrefix (originalLowerCut kap0 N)) Q rho (trimNaturalWeight kap kap0 B N)
    hcut.1
    (fun p hp => Finset.mem_Icc.mpr
      ⟨(mem_chenPrimePrefix.mp hp).2.pos, (mem_chenPrimePrefix.mp hp).1⟩)
    hQ hrho (fun p _ => by
      have hE := eta_bounds ((p : ℝ)/(N : ℝ)^(1-kap0))
      have hW := smooth_range kap B N p
      have hEabs : |1-eta ((p : ℝ)/(N : ℝ)^(1-kap0))| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hE.2)]
        linarith only [hE.1]
      have hWabs : |smoothNatural kap B N p| ≤ 1 := by
        rw [abs_of_nonneg hW.1]
        exact hW.2
      simpa only [trimNaturalWeight, abs_mul, mul_one] using
        mul_le_mul hEabs hWabs (abs_nonneg _) zero_le_one)
  rw [max_eq_right hN1] at hbound
  rw [original_singleton_trimReserve_eq_prefix kap kap0 B N hNpos (by omega),
    Complex.norm_real, Real.norm_eq_abs]
  have hpower : (N : ℝ)^(1-kap0)*(N : ℝ)^(kap0/2) =
      (N : ℝ)^(1-kap0/2) := by
    rw [←Real.rpow_add hNr]
    congr 1
    ring
  calc
    _ ≤ (3*(N : ℝ)^(1-kap0))*
        (C*(N : ℝ)^(kap0/2)+4*(1+Real.log (N : ℝ))) :=
      hbound.trans (mul_le_mul_of_nonneg_right hcut.2 (by positivity))
    _ = 3*C*(N : ℝ)^(1-kap0/2)+12*(N : ℝ)^(1-kap0)+
        12*(N : ℝ)^(1-kap0)*Real.log (N : ℝ) := by
      calc
        _ = 3*C*((N : ℝ)^(1-kap0)*(N : ℝ)^(kap0/2))+
            12*(N : ℝ)^(1-kap0)+12*(N : ℝ)^(1-kap0)*Real.log (N : ℝ) := by ring
        _ = _ := by rw [hpower]
    _ ≤ _ := by
      simp only [pow_zero, pow_one, mul_one] at h1 h2 h3
      linarith only [h1, h2, h3]

end
end ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy
