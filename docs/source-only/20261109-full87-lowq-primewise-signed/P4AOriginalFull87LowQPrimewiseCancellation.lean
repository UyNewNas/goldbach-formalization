import ImbalancedChen.P4AOriginalFull87LowQLocalPrimeFibres
import ImbalancedChen.P4AOriginalFull87PPCutoffLowQInvoice
import ImbalancedChen.CurvedRegionDiscrepancy
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The earlier per-q local prime-fibre envelope still took absolute values
BEFORE summing the actual signed physical coefficient across low moduli.
Here the original primitive discrepancy is expanded against the SAME
prime in the SAME chenPrimePrefix, the signed original RAW/LICENSED
complete-q coefficients are summed first, and the absolute value is
paid only once per prime. This preserves any genuine low-q cancellation.
The new charge is an alternative to, NOT an addition to, the old
per-q B(d)*C_W(d) invoice. No PP input or asymptotic gain is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87LowQPrimewiseCancellation
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87PhysicalQAggregateInvoice
  (pairActualPhysicalModuli pairActualHighQModuli)
open P4AOriginalFull87PPCutoffLowQInvoice
  (pairActualLowQModuli actual_raw_licensed_primitive_discrepancy_high_low)

/-- The literal one-prime contribution to the ORIGINAL coprime-normalized
AP discrepancy at full modulus d, including d=1. This is a formula,
not a postulated error bound or a surrogate sieve coefficient. -/
def actualPrimeContrast (N p d : ℕ) : ℝ :=
  (if Nat.ModEq d p N then (1 : ℝ) else 0) -
    (if Nat.Coprime p d then (1 : ℝ) / (Nat.totient d : ℝ) else 0)

private theorem primitive_eq_prime_contrast
    (T : Finset ℕ) (W : ℕ → ℝ) (N d : ℕ) :
    finitePrimitiveDiscrepancy T W N d =
      ∑ p ∈ T, W p * actualPrimeContrast N p d := by
  rw [finitePrimitiveDiscrepancy_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  unfold actualPrimeContrast
  by_cases hAP : Nat.ModEq d p N
  · by_cases hC : Nat.Coprime p d
    · simp [hAP, hC]
      ring
    · simp [hAP, hC]
  · by_cases hC : Nat.Coprime p d
    · simp [hAP, hC]
      ring
    · simp [hAP, hC]

/-- Finite Fubini identity: the signed FULL-q coefficient is retained
inside every original prime's combined low-modulus kernel. -/
private theorem finite_q_prime_exchange
    (T Q : Finset ℕ) (W A : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Q, A d * finitePrimitiveDiscrepancy T W N d) =
      ∑ p ∈ T, W p *
        (∑ d ∈ Q, A d * actualPrimeContrast N p d) := by
  calc
    (∑ d ∈ Q, A d * finitePrimitiveDiscrepancy T W N d) =
        ∑ d ∈ Q, ∑ p ∈ T,
          W p * (A d * actualPrimeContrast N p d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [primitive_eq_prime_contrast, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = ∑ p ∈ T, ∑ d ∈ Q,
          W p * (A d * actualPrimeContrast N p d) := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ T, W p *
          (∑ d ∈ Q, A d * actualPrimeContrast N p d) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

private theorem finite_q_prime_abs_envelope
    (T Q : Finset ℕ) (W A : ℕ → ℝ) (N : ℕ) :
    |∑ d ∈ Q, A d * finitePrimitiveDiscrepancy T W N d| ≤
      ∑ p ∈ T, |W p| *
        |∑ d ∈ Q, A d * actualPrimeContrast N p d| := by
  rw [finite_q_prime_exchange]
  calc
    |∑ p ∈ T, W p *
        (∑ d ∈ Q, A d * actualPrimeContrast N p d)| ≤
      ∑ p ∈ T, |W p *
        (∑ d ∈ Q, A d * actualPrimeContrast N p d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ T, |W p| *
        |∑ d ∈ Q, A d * actualPrimeContrast N p d| := by
      simp only [abs_mul]

/-- Exact signed low-q rearrangement for the TWO ORIGINAL dynamic policies.
The q=X boundary remains LOW; all physical Rosser beta factors and
occurrence multiplicities are already in supportedPhysicalRho. -/
theorem actual_raw_licensed_lowq_primitive_primewise_exact
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    (∑ d ∈ pairActualLowQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) =
    ∑ p ∈ chenPrimePrefix (N + D), W p *
      (∑ d ∈ pairActualLowQModuli R S N cap w z X,
        (supportedPhysicalRho R N cap w z L d -
          supportedPhysicalRho S N cap w z L d) *
          actualPrimeContrast N p d) := by
  dsimp only
  exact finite_q_prime_exchange
    (chenPrimePrefix (N + D))
    (pairActualLowQModuli
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      N cap w z X)
    W
    (fun d =>
      supportedPhysicalRho
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L d -
      supportedPhysicalRho
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        N cap w z L d)
    N

/-- The full signed PP discrepancy may be passed to STRICT d>X with
one per-prime low-q kernel. No moduluswise absolute value is imposed
until all original low-q coefficients at this SAME prime have canceled.
The kernel is explicit, not an added hypothesis or booked saving. -/
theorem actual_highq_primitive_le_full_plus_primewise_lowq
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    |∑ d ∈ pairActualHighQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| ≤
    |∑ d ∈ pairActualPhysicalModuli R S N cap w z,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| +
    ∑ p ∈ chenPrimePrefix (N + D), |W p| *
      |∑ d ∈ pairActualLowQModuli R S N cap w z X,
        (supportedPhysicalRho R N cap w z L d -
          supportedPhysicalRho S N cap w z L d) *
          actualPrimeContrast N p d| := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let T := chenPrimePrefix (N + D)
  let M := pairActualPhysicalModuli R S N cap w z
  let H := pairActualHighQModuli R S N cap w z X
  let Q := pairActualLowQModuli R S N cap w z X
  let A : ℕ → ℝ := fun d =>
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d
  let E : ℕ → ℝ := fun d => finitePrimitiveDiscrepancy T W N d
  have hsplit : (∑ d ∈ M, A d * E d) =
      (∑ d ∈ H, A d * E d) + (∑ d ∈ Q, A d * E d) := by
    exact actual_raw_licensed_primitive_discrepancy_high_low
      delta n e q om N D cap w z L W X
  have hlow : |∑ d ∈ Q, A d * E d| ≤
      ∑ p ∈ T, |W p| *
        |∑ d ∈ Q, A d * actualPrimeContrast N p d| := by
    exact finite_q_prime_abs_envelope T Q W A N
  have hdiff : (∑ d ∈ H, A d * E d) =
      (∑ d ∈ M, A d * E d) - (∑ d ∈ Q, A d * E d) := by
    linarith
  change |∑ d ∈ H, A d * E d| ≤
    |∑ d ∈ M, A d * E d| +
      ∑ p ∈ T, |W p| *
        |∑ d ∈ Q, A d * actualPrimeContrast N p d|
  calc
    |∑ d ∈ H, A d * E d| =
        |(∑ d ∈ M, A d * E d) - (∑ d ∈ Q, A d * E d)| := by
      rw [hdiff]
    _ ≤ |∑ d ∈ M, A d * E d| +
        |∑ d ∈ Q, A d * E d| := abs_sub_le _ _
    _ ≤ |∑ d ∈ M, A d * E d| +
        ∑ p ∈ T, |W p| *
          |∑ d ∈ Q, A d * actualPrimeContrast N p d| :=
      add_le_add_left hlow _

end
end ImbalancedChen.P4AOriginalFull87LowQPrimewiseCancellation
