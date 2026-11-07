import ImbalancedChen.P4AOriginalFull87ExceptionDivisorFibres
import ImbalancedChen.ActualSmallRoughAttachment
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: remove the last *unproved coefficient-size premise* from the
elementary prime-exception invoices.  The literal sign-attached, full-beta
small/rough coefficient is already proved one-bounded in
ActualSmallRoughAttachment.  Apply THAT theorem to the same original
sixth/eighth physical families; do not replace rho by a different sieve
coefficient.

For a nonprime centre the zero-gap p=N is excluded arithmetically.
The centre invoice then has the honest divisor-count upper bound
sum_{p prime, p|N} tau(N-p); the modulus invoice has an honest
unit-coefficient totient-fibre upper bound. Neither estimate is claimed
to be o(H_N), and neither reserve is paid.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualRhoDivisorTau
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87ExceptionDivisorFibres
open P4AOriginalFull87EighthPrimeMeanLedger
open P4AOriginalFull87LicensedSixthPolicy

/-- Original coefficient control, not an assumed bound on an arbitrary
signed beta.  The zero-gap p=N is deliberately excluded: tau(0) cannot
majorize that correction, and it occurs for prime centres. -/
theorem centre_invoice_le_actual_divisor_count
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hN : ¬ Nat.Prime N) :
    centreDivisorInvoice P N cap w z L ≤
      ∑ p ∈ centrePrimeFactors N, (((N - p).divisors.card : ℕ) : ℝ) := by
  classical
  unfold centreDivisorInvoice
  apply Finset.sum_le_sum
  intro p hp
  let S : Finset ℕ :=
    (actualSmallRoughModuli (P false) N cap w z).filter
      (fun d => d ∣ N - p)
  have hgap : N - p ≠ 0 :=
    Nat.ne_of_gt (centre_factor_gap_pos N p hN hp)
  have hsub : S ⊆ (N - p).divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hgap⟩
  change (∑ d ∈ S, |actualSmallRoughRho (P false) N cap w z L d|) ≤
    (((N - p).divisors.card : ℕ) : ℝ)
  calc
    (∑ d ∈ S, |actualSmallRoughRho (P false) N cap w z L d|) ≤
        ∑ d ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d _
          exact actualSmallRoughRho_abs_le_one (P false) N cap w z L d
    _ = (S.card : ℝ) := by simp
    _ ≤ (((N - p).divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub

/-- The same bound applies to both ACTUAL policies, independently of
their different signed coefficients and potentially different support. -/
theorem original_two_centre_invoices_le_tau
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (hN : ¬ Nat.Prime N) :
    centreDivisorInvoice (sixthPolicy n e q om (N : ℝ)) N cap w z L +
      centreDivisorInvoice (policy delta n e q om (N : ℝ)) N cap w z L ≤
        2 * ∑ p ∈ centrePrimeFactors N,
          (((N - p).divisors.card : ℕ) : ℝ) := by
  have h6 := centre_invoice_le_actual_divisor_count
    (sixthPolicy n e q om (N : ℝ)) N cap w z L hN
  have h8 := centre_invoice_le_actual_divisor_count
    (policy delta n e q om (N : ℝ)) N cap w z L hN
  linarith

/-- Remove |rho| only after invoking the literal one-bound. The original
complete modulus and the true p|d incidence remain; totient is not
replaced by a rough-factor or unrelated mean. -/
def unitModulusDivisorInvoice (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : ℝ :=
  ∑ p ∈ chenPrimePrefix N,
    ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
      (fun d => p ∣ d), (Nat.totient d : ℝ)⁻¹

theorem modulus_invoice_le_unit_rho
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    modulusDivisorInvoice P N cap w z L ≤
      unitModulusDivisorInvoice P N cap w z := by
  classical
  unfold modulusDivisorInvoice unitModulusDivisorInvoice
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro d _
  have hc := actualSmallRoughRho_abs_le_one (P false) N cap w z L d
  have hnonneg : 0 ≤ (Nat.totient d : ℝ)⁻¹ := by positivity
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_right hc hnonneg

/-- There is NO modulus-prime overlap with a prime divisor of the centre.
This uses the actual support's proved coprimality, not an imposed mask. -/
theorem actual_full_modulus_excludes_centre_prime
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {d p : ℕ}
    (hd : d ∈ actualSmallRoughModuli (P false) N cap w z)
    (hp : Nat.Prime p) (hpN : p ∣ N) :
    ¬ p ∣ d := by
  have hc : Nat.Coprime d N :=
    actualSmallRoughModuli_coprime_target (P false) N cap w z hd
  exact hp.coprime_iff_not_dvd.mp (hc.of_dvd_right hpN).symm

/-- Complete original receiver-density discrepancy with both genuine
one-bounded prime-exception invoices.  The primitive discrepancy and
modulus unit fibres are NOT discharged by this finite inequality. -/
theorem receiver_density_error_unit_tau_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (hN : ¬ Nat.Prime N) :
    |gain delta n e q om N cap w z L (receiverTest N) -
        primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      absoluteGainBudget delta n e q om N cap w z L (primitiveError N) +
      unitModulusDivisorInvoice (sixthPolicy n e q om (N : ℝ)) N cap w z +
      unitModulusDivisorInvoice (policy delta n e q om (N : ℝ)) N cap w z +
      2 * ∑ p ∈ centrePrimeFactors N,
        (((N - p).divisors.card : ℕ) : ℝ) := by
  have hb := receiver_density_error_divisor_fibre_bound
    delta n e q om N cap w z L
  have hm6 := modulus_invoice_le_unit_rho
    (sixthPolicy n e q om (N : ℝ)) N cap w z L
  have hm8 := modulus_invoice_le_unit_rho
    (policy delta n e q om (N : ℝ)) N cap w z L
  have hc := original_two_centre_invoices_le_tau
    delta n e q om N cap w z L hN
  linarith

end
end ImbalancedChen.P4AOriginalFull87ActualRhoDivisorTau
