import ImbalancedChen.P4AOriginalFull87PairedCoprimePP
import ImbalancedChen.ActualSmallRoughAttachment
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The manuscript's signed singleton PP statement is for the ORIGINAL COMPLETE
rho_N, not automatically for rho_N restricted to q > X. The latter
restriction is imposed after both real policies and their original
sign-sensitive small/rough coefficients have been constructed. To isolate
the STRICT integer high-q part one must retain a low-q complement; no
unproved cancellation or second sieve bound is introduced.

This packet provides an exact original-pair partition, verifies the
arithmetic q>0 / squarefree / target-coprime prerequisites on BOTH actual
supports, and pays the low-q complement in an explicit absolute invoice.
It does NOT claim that an arbitrary X is the legal manuscript PP cutoff,
that a chosen W is licensed Gevrey, or that the remaining invoice is o(H_N).
-/

namespace ImbalancedChen.P4AOriginalFull87PPCutoffLowQInvoice
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87PhysicalQAggregateInvoice
  (pairActualPhysicalModuli pairActualHighQModuli)
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87SharpCentreCarrier
  (actualSharpCarrierLiteral centreSharpSigned)
open P4AOriginalFull87WeightedSharpSmooth
  (weightedLowerBoundary weightedUpperBoundary)
open P4AOriginalFull87PairedCoprimePP
  (actual_raw_licensed_true_sharp_coprime_PP_same_full_q)

/-- The complement of the ORIGINAL complete-modulus high-q labels. In
particular the equality case d=X is LOW, because the physical cutoff is
strict X<d. Both sides of the comparison use the SAME partition. -/
def pairActualLowQModuli (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (X : ℕ) : Finset ℕ :=
  (pairActualPhysicalModuli R S N cap w z).filter (fun d => d ≤ X)

/-- There is no analytic modulus zero hidden in the RAW/LICENSED supports.
Both real original physical policies have squarefree, positive moduli
coprime to the TARGET N; no condition on X or W is needed for this. -/
theorem actual_raw_licensed_full_q_arithmetic_support
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    ∀ d ∈ pairActualPhysicalModuli R S N cap w z,
      0 < d ∧ Squarefree d ∧ d.Coprime N := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  intro d hd
  change d ∈ (actualSmallRoughModuli (R false) N cap w z ∪
    actualSmallRoughModuli (S false) N cap w z) at hd
  rcases Finset.mem_union.mp hd with hR | hS
  · have hs := actualSmallRoughModuli_squarefree (R false) N cap w z hR
    exact ⟨Nat.pos_of_ne_zero hs.ne_zero, hs,
      actualSmallRoughModuli_coprime_target (R false) N cap w z hR⟩
  · have hs := actualSmallRoughModuli_squarefree (S false) N cap w z hS
    exact ⟨Nat.pos_of_ne_zero hs.ne_zero, hs,
      actualSmallRoughModuli_coprime_target (S false) N cap w z hS⟩

/-- Actual RAW and LICENSED prime discrepancy, grouped only AFTER their
complete rho coefficients are formed, splits at the precise integer X.
Every occurrence and beta sign stays INSIDE supportedPhysicalRho.
The equality d=X belongs to the complement, not the high-q term. -/
theorem actual_raw_licensed_primitive_discrepancy_high_low
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    (∑ d ∈ pairActualPhysicalModuli R S N cap w z,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) =
    (∑ d ∈ pairActualHighQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) +
    (∑ d ∈ pairActualLowQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let M := pairActualPhysicalModuli R S N cap w z
  let G : ℕ → ℝ := fun d =>
    (supportedPhysicalRho R N cap w z L d -
     supportedPhysicalRho S N cap w z L d) *
      finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  change (∑ d ∈ M, G d) =
    (∑ d ∈ M.filter (fun d => X < d), G d) +
    (∑ d ∈ M.filter (fun d => d ≤ X), G d)
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : X < d
  · have hnot : ¬ d ≤ X := Nat.not_le.mpr hd
    simp [hd, hnot]
  · have hle : d ≤ X := Nat.le_of_not_gt hd
    simp [hd, hle]

/-- Sharp actual Chen receiver recentered at the *genuine* q-coprime
mean = strictly high-q primitive discrepancy PLUS the still-unpaid
low-q primitive discrepancy PLUS the original two endpoints and
centre deletion. A full-rho PP estimate alone does not erase low-q. -/
theorem actual_raw_licensed_true_sharp_PP_high_low_exact
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ)
    (hN : ¬ Nat.Prime N)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    (actualSharpCarrierLiteral R N cap w z L -
      actualSharpCarrierLiteral S N cap w z L) -
      (∑ d ∈ pairActualPhysicalModuli R S N cap w z,
        (supportedPhysicalRho R N cap w z L d -
         supportedPhysicalRho S N cap w z L d) *
        (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
          (Nat.totient d : ℝ))) =
    (∑ d ∈ pairActualHighQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) +
    (∑ d ∈ pairActualLowQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) +
    ((weightedLowerBoundary R N D cap w z L W -
       weightedLowerBoundary S N D cap w z L W) -
     (weightedUpperBoundary R N D cap w z L W -
       weightedUpperBoundary S N D cap w z L W)) -
    (centreSharpSigned R N cap w z L -
      centreSharpSigned S N cap w z L) := by
  have hFull := actual_raw_licensed_true_sharp_coprime_PP_same_full_q
    delta n e q om N D cap w z L W hN hInterior
  have hSplit := actual_raw_licensed_primitive_discrepancy_high_low
    delta n e q om N D cap w z L W X
  dsimp only at hFull hSplit ⊢
  rw [hFull, hSplit]
  ring

/-- Exact finite charge needed to pass from a *licensed full-rho*
primitive PP bound to the strict high-q part. The remaining low-q
charge is an ORIGINAL same-q signed coefficient, not the difference of
two unrelated sieve estimates. It is not assumed small here. -/
theorem actual_raw_licensed_highq_primitive_abs_le_full_plus_low
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
    (∑ d ∈ pairActualLowQModuli R S N cap w z X,
      |supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d| *
        |finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d|) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let G : ℕ → ℝ := fun d =>
    (supportedPhysicalRho R N cap w z L d -
     supportedPhysicalRho S N cap w z L d) *
      finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  let high := ∑ d ∈ pairActualHighQModuli R S N cap w z X, G d
  let low := ∑ d ∈ pairActualLowQModuli R S N cap w z X, G d
  let full := ∑ d ∈ pairActualPhysicalModuli R S N cap w z, G d
  have hSplit : full = high + low := by
    exact actual_raw_licensed_primitive_discrepancy_high_low
      delta n e q om N D cap w z L W X
  have hlow :
      |low| ≤ ∑ d ∈ pairActualLowQModuli R S N cap w z X,
        |supportedPhysicalRho R N cap w z L d -
          supportedPhysicalRho S N cap w z L d| *
          |finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| := by
    calc
      |low| ≤ ∑ d ∈ pairActualLowQModuli R S N cap w z X, |G d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d _
        simp only [G, abs_mul]
  have hhigh : |high| ≤ |full| + |low| := by
    have heq : high = full - low := by linarith
    rw [heq]
    exact abs_sub_le _ _
  change |high| ≤ |full| +
    (∑ d ∈ pairActualLowQModuli R S N cap w z X,
      |supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d| *
        |finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d|)
  exact hhigh.trans (add_le_add_left hlow _)

end
end ImbalancedChen.P4AOriginalFull87PPCutoffLowQInvoice
