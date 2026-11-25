import ImbalancedChen.P1OriginalSingletonPointwiseData
import ImbalancedChen.Part3ProperPowerChartSum
import ImbalancedChen.SingularSeries

/-!
The manuscript's proper-power deletion for the original smoothed
singleton, with its full prime cap `2 * N` and the same signed `Q, rho`.

The arithmetic estimate is the already proved Part3 chart-sum theorem.
Only its original-singleton instance is proved here. In particular, the
threshold precedes the collar order, modulus set and signed coefficient.
The exact coprime von Mangoldt mean stays inside the signed error.

This comparison does not assert a bound on the remaining von Mangoldt
error or on the old chart-weighted Atlas reserve.
-/

namespace ImbalancedChen.P1OriginalSingletonProperPower

noncomputable section

open Classical Finset Filter
open scoped Topology BigOperators
open Part3 P5CanonicalTentNarrowSingletonTransfer

/-- The exact von Mangoldt comparison term on the full singleton range. -/
def vonMangoldtRemaining (kap : ℝ) (collarOrder N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) : ℂ :=
  finiteProductSignedError (Icc 1 (2 * N)) Q N (fun q => (rho q : ℂ))
    (labelledVonMangoldtProductMass 1 (2 * N)
      (fullSmoothWeight kap collarOrder N))

private theorem fullSmoothWeight_abs_le_one (kap : ℝ) (collarOrder N : ℕ)
    (t : Fin 1 → Fin (2 * N + 1)) :
    |fullSmoothWeight kap collarOrder N t| ≤ 1 := by
  rw [fullSmoothWeight_eq_actual_profile]
  obtain ⟨h0, h1⟩ := P5Z.ActualSingletonLogCollarFamily.profile_bounds
    (1 - kap) (P5Z.ActualSingletonLogCollarFamily.logWidth collarOrder N) N
    (fun i => ((t i).val : ℝ))
  rwa [abs_of_nonneg h0]

private theorem fullSmoothWeight_effective_geometry
    (kap : ℝ) (collarOrder : ℕ) {N : ℕ} (hN : 2 ≤ N)
    (t : Fin 1 → Fin (2 * N + 1))
    (ht : fullSmoothWeight kap collarOrder N t * labelledVonMangoldtWeight t ≠ 0) :
    (∀ i, (N : ℝ) ^ (1 - kap) ≤ ((t i).val : ℝ)) ∧
      (labelledProduct t : ℝ) ≤ 2 * (N : ℝ) := by
  have hW : fullSmoothWeight kap collarOrder N t ≠ 0 :=
    (mul_ne_zero_iff.mp ht).1
  have hlo : (N : ℝ) ^ (1 - kap) < ((t 0).val : ℝ) := by
    by_contra h
    apply hW
    rw [fullSmoothWeight_eq_actual_profile]
    exact P5Z.ActualSingletonLogCollarFamily.profile_zero_below
      (1 - kap) (P5Z.ActualSingletonLogCollarFamily.logWidth collarOrder N) hN
      (fun i => ((t i).val : ℝ)) (le_of_not_gt h)
  constructor
  · intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa only [hi] using hlo.le
  · rw [P5S1SingletonPP.labelledProduct_singleton]
    exact_mod_cast Nat.le_of_lt_succ (t 0).isLt

/-- Every logarithmic accuracy for the original full smoothed singleton.
No desired signed-error estimate is an assumption. -/
theorem eventually_original_singleton_prime_sub_vonMangoldt_logAccuracy
    (kap : ℝ) (hkap : kap < 1) (A eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (collarOrder : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ),
        (∀ q ∈ Q, 0 < q ∧ (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) →
        (∀ q ∈ Q, |rho q| ≤ 1) →
        ‖(primeProductSignedError 1 (2 * N) N Q rho
            (fullSmoothWeight kap collarOrder N) : ℂ) -
          vonMangoldtRemaining kap collarOrder N Q rho‖ ≤
          eps * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  have h := ProperPowerChartSum.eventually_primeProductSignedError_sub_vonMangoldt_logAccuracy
    1 0 0 (M := 1) (C := 2) (c := 1) (K := 1) (Cρ := 1)
    (a := 1 - kap) (θ := 599 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) A eps heps
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with N hmain hN
  intro collarOrder Q rho hQ hrho
  unfold vonMangoldtRemaining
  apply hmain (2 * N) (Icc 1 (2 * N)) Q rho
    (fullSmoothWeight kap collarOrder N) P5Z.ActualEtaPsiOccurrenceBudget.chi
  · intro b hb
    refine mem_Icc.mpr ⟨(mem_Icc.mp hb).1, (mem_Icc.mp hb).2.trans ?_⟩
    exact_mod_cast Nat.le_ceil ((2 : ℝ) * (N : ℝ))
  · intro t ht _
    rw [P5S1SingletonPP.labelledProduct_singleton]
    have hp : Nat.Prime (t 0).val := (mem_filter.mp ht).2 0
    exact mem_Icc.mpr ⟨by have := hp.pos; omega, Nat.le_of_lt_succ (t 0).isLt⟩
  · intro q hq
    exact ⟨(hQ q hq).1, by simpa only [one_mul] using (hQ q hq).2.le⟩
  · intro q hq
    simpa only [pow_zero, mul_one] using hrho q hq
  · intro s hs
    exact P5Z.ActualSingletonPrimeTestFamily.chi_one hs
  · intro s hs
    exact P5Z.ActualSingletonPrimeTestFamily.chi_zero hs
  · intro s
    exact P5Z.ActualSingletonPrimeTestFamily.chi_bounds s
  · intro t
    simpa only [pow_zero, mul_one] using fullSmoothWeight_abs_le_one kap collarOrder N t
  · intro t ht
    simpa only [one_mul] using fullSmoothWeight_effective_geometry kap collarOrder hN t ht

/-- The comparison fits any fixed positive share of the manuscript's
actual singular normalization, uniformly in the original `Q, rho`. -/
theorem eventually_original_singleton_prime_sub_vonMangoldt_singularNormalization
    (kap : ℝ) (hkap : kap < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (collarOrder : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ),
        (∀ q ∈ Q, 0 < q ∧ (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) →
        (∀ q ∈ Q, |rho q| ≤ 1) →
        ‖(primeProductSignedError 1 (2 * N) N Q rho
            (fullSmoothWeight kap collarOrder N) : ℂ) -
          vonMangoldtRemaining kap collarOrder N Q rho‖ ≤
          eta * singularNormalization N := by
  filter_upwards [eventually_original_singleton_prime_sub_vonMangoldt_logAccuracy
    kap hkap 2 (eta * twinPrimeConstant) (mul_pos heta twinPrimeConstant_pos)] with N hN
  intro collarOrder Q rho hQ hrho
  have herr := hN collarOrder Q rho hQ hrho
  have hnorm := mul_le_mul_of_nonneg_left (singularNormalization_lower N) heta.le
  calc
    _ ≤ (eta * twinPrimeConstant) * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := herr
    _ = eta * (twinPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := by
      rw [Real.rpow_two]
      ring
    _ ≤ eta * singularNormalization N := hnorm

end
end ImbalancedChen.P1OriginalSingletonProperPower
