import ImbalancedChen.P1OriginalSharpFiniteReceiver

/-! The older full87 sharp receiver stopped at the fixed power 9/20.
Use the complete modulus cutoff of the pinned maximal prime BV theorem.
The endpoint is inclusive and the centre here is the literal total pi(N).
The BV exponent is chosen once, before the physical coefficient or tolerance. -/
namespace ImbalancedChen.P1Full87SharpClassicalCut
noncomputable section
open Filter
open scoped Classical BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open MathlibNt.SieveTheory.LiuWeight
open P4AOriginalFull87EighthPrimeMeanLedger (primeMass densityTest)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError)
open P1OriginalSharpFiniteReceiver (cut)

private theorem sharp_as_two_prime_errors (N d : ℕ) :
    sharpPrimeError N d = part3PrimeAPError N N d -
      part3PrimeAPError N 1 1 * (1 / (d.totient : ℝ)) := by
  have hunit : part3PrimeAPError N 1 1 = primeMass N - trueLogarithmicIntegral N := by
    simp [part3PrimeAPError, chenPrimeAPCount, primeMass, Nat.ModEq]
  rw [sharpPrimeError, hunit, part3PrimeAPError, densityTest]
  ring

/-- A single full physical BV cutoff pays all bounded signed prime weights
on any subcarrier. For the original application one may read the difference
of the two physical policies directly, since that difference is one-bounded. -/
theorem exists_pan_sharp_payment :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, cut N ≤ panModulusCutoff N B ∧
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
        S ⊆ Finset.Icc 1 (panModulusCutoff N B) →
        (∀ d ∈ S, d.Coprime N) → ∀ c : ℕ → ℝ, (∀ d ∈ S, |c d| ≤ 1) →
        |∑ d ∈ S, c d * sharpPrimeError N d| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    part3_sum_abs_primeAPError_log_saving ((4 : ℕ) : ℝ) (by positivity)
  have hcut : ∀ᶠ N : ℕ in atTop, cut N ≤ panModulusCutoff N B := by
    simpa only [cut, liuSourceDEpsilon, show (1/2 - 1/20 : ℝ) = 9/20 by norm_num] using
      (eventually_liuSourceDEpsilon_le_panModulusCutoff (1/20 : ℝ) B (by norm_num) hB)
  refine ⟨B, hB, 9*C, by positivity, ?_⟩
  filter_upwards [hBV, hcut, eventually_one_le_nat_log, eventually_ge_atTop (2 : ℕ)]
    with N hprime hcutN hlog hN
  refine ⟨hcutN, ?_⟩
  intro S hSN hSD hcop c hc
  let D := panModulusCutoff N B
  let X := C * (N : ℝ) / Real.log (N : ℝ) ^ 4
  have hD : 1 ≤ D :=
    (P4BPositiveUpperPrimeBV.belowHalfCap_le_target (X := N) (by omega)).1.trans hcutN
  have hunitSet : ({1} : Finset ℕ) ⊆ Finset.Icc 1 D :=
    Finset.singleton_subset_iff.mpr (Finset.mem_Icc.mpr ⟨le_rfl, hD⟩)
  have hp : |part3PrimeAPError N 1 1| ≤ X := by
    simpa only [X, Finset.sum_singleton, Real.rpow_natCast] using
      (hprime D le_rfl {1} hunitSet N le_rfl (fun _ => 1)
        (fun _ _ => Nat.coprime_one_left _))
  have hs : (∑ d ∈ S, |part3PrimeAPError N N d|) ≤ X := by
    simpa only [X, Real.rpow_natCast] using
      (hprime D le_rfl S hSD N le_rfl (fun _ => N) (fun d hd => (hcop d hd).symm))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hrec : (∑ d ∈ S, 1 / (d.totient : ℝ)) ≤ 8 * Real.log (N : ℝ) := by
    have hh := sum_reciprocal_totient_subset_le_log S N hSN
    rw [max_eq_right hN1] at hh
    linarith only [hh, hlog]
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hcost := mul_le_mul hp hrec
    (Finset.sum_nonneg (fun d _ => by positivity)) hX
  calc
    _ ≤ ∑ d ∈ S, |c d * sharpPrimeError N d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ S, (|part3PrimeAPError N N d| +
          |part3PrimeAPError N 1 1| * (1 / (d.totient : ℝ))) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      refine (mul_le_of_le_one_left (abs_nonneg _) (hc d hd)).trans ?_
      rw [sharp_as_two_prime_errors]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 / (d.totient : ℝ) by positivity)]
    _ ≤ X + X * (8 * Real.log (N : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      exact add_le_add hs hcost
    _ ≤ (9 * Real.log (N : ℝ)) * X := by
      nlinarith only [mul_nonneg hX (sub_nonneg.mpr hlog)]
    _ = _ := by dsimp only [X]; field_simp [hlogpos.ne'] <;> ring

end
end ImbalancedChen.P1Full87SharpClassicalCut
