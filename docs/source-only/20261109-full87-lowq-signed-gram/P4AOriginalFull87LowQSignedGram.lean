import ImbalancedChen.P4AOriginalFull87LowQPrimewiseCancellation
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Exact second-moment (Gram) accounting for the ORIGINAL RAW/LICENSED
low complete-q primitive kernel. The preceding primewise packet stopped
after one absolute value at each original prime. Here its same signed
kernel is squared BEFORE expanding the pair of complete moduli. The
diagonal AND cross-modulus terms, including negative correlations,
remain explicit. The Gram quadratic form is nonnegative without any
claimed diagonal dominance, asymptotic gain, or new PP permission.

This is only a finite algebraic identity on the original signed physical
rho, the original chenPrimePrefix, and the original strict high/low
partition (d = X belongs to LOW). It does not assert a bound relative to
H_N, certify saved87 geometry, or double-charge an earlier invoice.
-/

namespace ImbalancedChen.P4AOriginalFull87LowQSignedGram
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87PPCutoffLowQInvoice (pairActualLowQModuli)
open P4AOriginalFull87LowQPrimewiseCancellation (actualPrimeContrast)

/-- Finite Gram identity with ALL ordered cross-modulus pairs present.
No positivity or independence is required of A or of K. -/
private theorem finite_signed_gram_identity
    (T Q : Finset ℕ) (A : ℕ → ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ p ∈ T, (∑ d ∈ Q, A d * K p d) ^ 2) =
      ∑ d ∈ Q, ∑ e ∈ Q,
        A d * A e * (∑ p ∈ T, K p d * K p e) := by
  calc
    (∑ p ∈ T, (∑ d ∈ Q, A d * K p d) ^ 2) =
        ∑ p ∈ T, (∑ d ∈ Q, A d * K p d) *
          (∑ e ∈ Q, A e * K p e) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = ∑ p ∈ T, ∑ d ∈ Q, ∑ e ∈ Q,
          A d * A e * (K p d * K p e) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = ∑ d ∈ Q, ∑ e ∈ Q, ∑ p ∈ T,
          A d * A e * (K p d * K p e) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Q, ∑ e ∈ Q,
          A d * A e * (∑ p ∈ T, K p d * K p e) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]

/-- Genuine low-q second moment of the SAME physical coefficient pair.
It is a positive-semidefinite Gram form, not a declaration that the
off-diagonal correlations are negligible or that its magnitude is
small compared with H_N. There is no model-supplied covariance field. -/
theorem actual_raw_licensed_lowq_prime_gram_exact_and_nonneg
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let Q := pairActualLowQModuli R S N cap w z X
    let A : ℕ → ℝ := fun d =>
      supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d
    (∑ p ∈ chenPrimePrefix (N + D),
        (∑ d ∈ Q, A d * actualPrimeContrast N p d) ^ 2) =
      ∑ d ∈ Q, ∑ f ∈ Q, A d * A f *
        (∑ p ∈ chenPrimePrefix (N + D),
          actualPrimeContrast N p d * actualPrimeContrast N p f) ∧
    0 ≤ ∑ d ∈ Q, ∑ f ∈ Q, A d * A f *
      (∑ p ∈ chenPrimePrefix (N + D),
        actualPrimeContrast N p d * actualPrimeContrast N p f) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let Q := pairActualLowQModuli R S N cap w z X
  let A : ℕ → ℝ := fun d =>
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d
  let T := chenPrimePrefix (N + D)
  let K : ℕ → ℕ → ℝ := actualPrimeContrast N
  have hGram := finite_signed_gram_identity T Q A K
  change (∑ p ∈ T, (∑ d ∈ Q, A d * K p d) ^ 2) =
      ∑ d ∈ Q, ∑ f ∈ Q,
        A d * A f * (∑ p ∈ T, K p d * K p f) ∧
    0 ≤ ∑ d ∈ Q, ∑ f ∈ Q,
      A d * A f * (∑ p ∈ T, K p d * K p f)
  constructor
  · exact hGram
  · rw [← hGram]
    exact Finset.sum_nonneg (fun p hp =>
      sq_nonneg (∑ d ∈ Q, A d * K p d))

end
end ImbalancedChen.P4AOriginalFull87LowQSignedGram
