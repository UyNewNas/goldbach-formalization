import ImbalancedChen.P4AOriginalFull87LowQPrimewiseCancellation
import ImbalancedChen.P4AOriginalFull87LowQSignedGram
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The preceding ORIGINAL RAW/LICENSED finite Gram identity is UNWEIGHTED,
whereas its primitive discrepancy invoice uses the genuine (possibly
signed) Gevrey prime weight W. This packet does not infer an estimate for
that signed prime sum from the unweighted Gram without a weight bound.
Instead it proves a WEIGHTED finite Gram and the exact finite Cauchy
invoice with |W|, using the same complete-q physical rho, original prime
prefix and strict q > X cut (q = X is LOW).

No original saved87 witness, analytic PP bound, numerical saving, or
relative-to-H_N estimate follows from this elementary finite identity.
-/

namespace ImbalancedChen.P4AOriginalFull87LowQWeightedGramInvoice
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87PPCutoffLowQInvoice (pairActualLowQModuli)
open P4AOriginalFull87LowQPrimewiseCancellation
  (actualPrimeContrast actual_raw_licensed_lowq_primitive_primewise_exact)

private theorem finite_product_sums (T : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ p ∈ T, f p) * (∑ q ∈ T, g q) =
      ∑ p ∈ T, ∑ q ∈ T, f p * g q := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]

/-- Finite nonnegative pairwise-variance identity. It proves the weighted
Cauchy inequality without assuming the actual prime weight is positive:
its application uses lambda(p)=|W(p)|, never W(p). -/
private theorem finite_weighted_variance_identity
    (T : Finset ℕ) (lam u : ℕ → ℝ) :
    (∑ p ∈ T, ∑ q ∈ T, lam p * lam q * (u p - u q)^2) =
      2 * ((∑ p ∈ T, lam p) *
        (∑ p ∈ T, lam p * (u p)^2) -
        (∑ p ∈ T, lam p * u p)^2) := by
  calc
    (∑ p ∈ T, ∑ q ∈ T, lam p * lam q * (u p - u q)^2) =
        ∑ p ∈ T, ∑ q ∈ T,
          ((lam p * (u p)^2) * lam q +
            lam p * (lam q * (u q)^2) -
            2 * ((lam p * u p) * (lam q * u q))) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = (∑ p ∈ T, ∑ q ∈ T, (lam p * (u p)^2) * lam q) +
        (∑ p ∈ T, ∑ q ∈ T, lam p * (lam q * (u q)^2)) -
        2 * (∑ p ∈ T, ∑ q ∈ T, (lam p * u p) * (lam q * u q)) := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      ring
    _ = 2 * ((∑ p ∈ T, lam p) *
        (∑ p ∈ T, lam p * (u p)^2) -
        (∑ p ∈ T, lam p * u p)^2) := by
      rw [← finite_product_sums T (fun p => lam p * (u p)^2) lam,
        ← finite_product_sums T lam (fun p => lam p * (u p)^2),
        ← finite_product_sums T (fun p => lam p * u p) (fun p => lam p * u p)]
      ring

private theorem finite_weighted_cauchy
    (T : Finset ℕ) (lam u : ℕ → ℝ)
    (hlam : ∀ p ∈ T, 0 ≤ lam p) :
    (∑ p ∈ T, lam p * u p)^2 ≤
      (∑ p ∈ T, lam p) * (∑ p ∈ T, lam p * (u p)^2) := by
  have hpos :
      0 ≤ ∑ p ∈ T, ∑ q ∈ T,
        lam p * lam q * (u p - u q)^2 := by
    apply Finset.sum_nonneg
    intro p hp
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (mul_nonneg (hlam p hp) (hlam q hq)) (sq_nonneg _)
  rw [finite_weighted_variance_identity] at hpos
  nlinarith

private theorem finite_weighted_signed_gram
    (T Q : Finset ℕ) (lam A : ℕ → ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ p ∈ T, lam p * (∑ d ∈ Q, A d * K p d)^2) =
      ∑ d ∈ Q, ∑ f ∈ Q, A d * A f *
        (∑ p ∈ T, lam p * (K p d * K p f)) := by
  calc
    (∑ p ∈ T, lam p * (∑ d ∈ Q, A d * K p d)^2) =
        ∑ p ∈ T, ∑ d ∈ Q, ∑ f ∈ Q,
          A d * A f * (lam p * (K p d * K p f)) := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        lam p * (∑ d ∈ Q, A d * K p d)^2 =
            (∑ d ∈ Q, A d * K p d) *
              (∑ f ∈ Q, lam p * (A f * K p f)) := by
          rw [← Finset.mul_sum]
          ring
        _ = ∑ d ∈ Q, ∑ f ∈ Q,
            A d * A f * (lam p * (K p d * K p f)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro f hf
          ring
    _ = ∑ d ∈ Q, ∑ f ∈ Q, ∑ p ∈ T,
        A d * A f * (lam p * (K p d * K p f)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Q, ∑ f ∈ Q, A d * A f *
          (∑ p ∈ T, lam p * (K p d * K p f)) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.mul_sum]

/-- The ORIGINAL physical low-q invoice with the ACTUAL signed weight W.
The full weighted Gram retains EVERY ordered pair of complete moduli,
including potentially negative off-diagonal terms. The second conjunct
is an unconditional finite Cauchy PAYMENT in terms of its true |W|-weighted
second moment, not a declaration that this moment is small.

This fixes the precise mismatch between the predecessor's unweighted
Gram and the actual (possibly signed) prime weights in the PP invoice.
No new supplier, covariance assumption or artificially licensed coefficient. -/
theorem actual_raw_licensed_lowq_weighted_gram_and_cauchy
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let T := chenPrimePrefix (N + D)
    let Q := pairActualLowQModuli R S N cap w z X
    let A : ℕ → ℝ := fun d =>
      supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d
    let k : ℕ → ℝ := fun p =>
      ∑ d ∈ Q, A d * actualPrimeContrast N p d
    (∑ p ∈ T, |W p| * (k p)^2) =
      ∑ d ∈ Q, ∑ f ∈ Q, A d * A f *
        (∑ p ∈ T, |W p| *
          (actualPrimeContrast N p d * actualPrimeContrast N p f)) ∧
    (∑ d ∈ Q, A d * finitePrimitiveDiscrepancy T W N d)^2 ≤
      (∑ p ∈ T, |W p|) *
        (∑ d ∈ Q, ∑ f ∈ Q, A d * A f *
          (∑ p ∈ T, |W p| *
            (actualPrimeContrast N p d * actualPrimeContrast N p f))) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let T := chenPrimePrefix (N + D)
  let Q := pairActualLowQModuli R S N cap w z X
  let A : ℕ → ℝ := fun d =>
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d
  let K : ℕ → ℕ → ℝ := actualPrimeContrast N
  let k : ℕ → ℝ := fun p => ∑ d ∈ Q, A d * K p d
  let B : ℝ := ∑ d ∈ Q, ∑ f ∈ Q, A d * A f *
      (∑ p ∈ T, |W p| * (K p d * K p f))
  have hGram : (∑ p ∈ T, |W p| * (k p)^2) = B :=
    finite_weighted_signed_gram T Q (fun p => |W p|) A K
  have hCauchySigned : (∑ p ∈ T, W p * k p)^2 ≤
      (∑ p ∈ T, |W p|) * B := by
    have hSigned :
        (∑ p ∈ T, W p * k p)^2 ≤
          (∑ p ∈ T, |W p| * |k p|)^2 := by
      have hAbs :
          |∑ p ∈ T, W p * k p| ≤ ∑ p ∈ T, |W p * k p| :=
        Finset.abs_sum_le_sum_abs _ _
      have hAbsEq :
          (∑ p ∈ T, |W p * k p|) =
            ∑ p ∈ T, |W p| * |k p| := by
        simp only [abs_mul]
      rw [hAbsEq] at hAbs
      have hPos : 0 ≤ ∑ p ∈ T, |W p| * |k p| :=
        Finset.sum_nonneg (fun p hp => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hdiff := mul_nonneg (sub_nonneg.mpr hAbs)
        (add_nonneg hPos (abs_nonneg (∑ p ∈ T, W p * k p)))
      nlinarith [sq_abs (∑ p ∈ T, W p * k p)]
    have hAbsCauchy : (∑ p ∈ T, |W p| * |k p|)^2 ≤
        (∑ p ∈ T, |W p|) * B := by
      have h := finite_weighted_cauchy T (fun p => |W p|)
        (fun p => |k p|) (fun p hp => abs_nonneg _)
      have hEq : (∑ p ∈ T, |W p| * (|k p|)^2) = B := by
        simpa only [sq_abs] using hGram
      rw [hEq] at h
      exact h
    exact hSigned.trans hAbsCauchy
  have hPrime := actual_raw_licensed_lowq_primitive_primewise_exact
    delta n e q om N D cap w z L W X
  change (∑ d ∈ Q, A d * finitePrimitiveDiscrepancy T W N d) =
    ∑ p ∈ T, W p * k p at hPrime
  change (∑ p ∈ T, |W p| * (k p)^2) = B ∧
    (∑ d ∈ Q, A d * finitePrimitiveDiscrepancy T W N d)^2 ≤
      (∑ p ∈ T, |W p|) * B
  constructor
  · exact hGram
  · rw [hPrime]
    exact hCauchySigned

end
end ImbalancedChen.P4AOriginalFull87LowQWeightedGramInvoice
