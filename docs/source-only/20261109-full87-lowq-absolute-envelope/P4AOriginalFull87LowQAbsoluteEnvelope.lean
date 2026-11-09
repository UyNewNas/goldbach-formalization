import ImbalancedChen.P4AOriginalFull87PPCutoffLowQInvoice
import ImbalancedChen.CoprimeRecentering
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The prior packet retained the exact low-q complement in the signed
RAW/LICENSED singleton PP discrepancy.  This packet supplies an entirely
FINITE envelope for that literal complement, without requesting another
external distribution theorem or inventing a filtered admissible family.

The original complete small-Rosser x rough physical coefficients are
one-bounded for EACH real policy.  The actual prime prefix and ANY signed
weight W give a universal primitive-discrepancy envelope via the existing
finite reduced-residue recentering theorem.  Their combination bounds the
low-q complement by the exact original coefficient variation, and then by
the cardinality of its ACTUAL low-q support.  Neither bound is asserted to
be small relative to H_N.  In particular, this is not a licence to
discard low q or to replace the manuscript's signed PP input.
-/

namespace ImbalancedChen.P4AOriginalFull87LowQAbsoluteEnvelope
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87PPCutoffLowQInvoice
  (pairActualLowQModuli actual_raw_licensed_full_q_arithmetic_support)
open P4AOriginalFull87PhysicalQAggregateInvoice (pairActualPhysicalModuli)
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)

/-- The literal modulus-congruence mass is controlled by the absolute
mass on its own ORIGINAL finite prime source. No sign condition is used. -/
private theorem abs_finite_congruence_le_source_abs
    (S : Finset ℕ) (W : ℕ → ℝ) (a d : ℕ) :
    |finiteCongruenceMass S W a d| ≤ ∑ p ∈ S, |W p| := by
  classical
  calc
    |finiteCongruenceMass S W a d| =
        |∑ p ∈ S.filter (fun p => Nat.ModEq d p a), W p| := rfl
    _ ≤ ∑ p ∈ S.filter (fun p => Nat.ModEq d p a), |W p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, |W p| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => abs_nonneg (W p))

/-- Elementary bound on the genuine primitive discrepancy of the
same original prime prefix and the same signed weight. Positive q and
target-coprimality are supplied by the REAL physical modulus support. -/
private theorem actual_primitive_abs_le_two_source_abs
    (N D d : ℕ) (W : ℕ → ℝ)
    (hd : 0 < d) (hcop : d.Coprime N) :
    |finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| ≤
      2 * (∑ p ∈ chenPrimePrefix (N + D), |W p|) := by
  apply abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform_primitive
    (chenPrimePrefix (N + D)) W 0
    (∑ p ∈ chenPrimePrefix (N + D), |W p|)
    N d hd hcop.symm
  intro b _ _
  simpa only [sub_zero] using
    abs_finite_congruence_le_source_abs
      (chenPrimePrefix (N + D)) W b d

/-- The original, signed full-modulus coefficient remains one-bounded
even on the union of two DIFFERENT real policies' support sets. -/
private theorem supported_physical_rho_abs_le_one
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (d : ℕ) :
    |supportedPhysicalRho P N cap w z L d| ≤ 1 := by
  unfold supportedPhysicalRho
  split_ifs with h
  · exact actualSmallRoughRho_abs_le_one (P false) N cap w z L d
  · norm_num

/-- NEW FINITE invoice. The original low-q primitive discrepancy cost
is bounded by twice the absolute prime-source mass times the actual
signed coefficient variation. This does not assume that the q-filtered
coefficient is licensed by the manuscript's full-rho PP theorem.
The true q=X boundary remains LOW. -/
theorem actual_raw_licensed_lowq_primitive_le_coefficient_variation
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let Q := pairActualLowQModuli R S N cap w z X
    let T := ∑ p ∈ chenPrimePrefix (N + D), |W p|
    |∑ d ∈ Q,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| ≤
      (2 * T) *
        (∑ d ∈ Q,
          |supportedPhysicalRho R N cap w z L d -
           supportedPhysicalRho S N cap w z L d|) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let Q := pairActualLowQModuli R S N cap w z X
  let T : ℝ := ∑ p ∈ chenPrimePrefix (N + D), |W p|
  let A : ℕ → ℝ := fun d =>
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d
  let E : ℕ → ℝ := fun d =>
    finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  have hE (d : ℕ) (hd : d ∈ Q) : |E d| ≤ 2 * T := by
    have hfull : d ∈ pairActualPhysicalModuli R S N cap w z :=
      (Finset.mem_filter.mp hd).1
    have hvalid : 0 < d ∧ Squarefree d ∧ d.Coprime N :=
      (actual_raw_licensed_full_q_arithmetic_support
        delta n e q om N cap w z) d hfull
    exact actual_primitive_abs_le_two_source_abs
      N D d W hvalid.1 hvalid.2.2
  change |∑ d ∈ Q, A d * E d| ≤
    (2 * T) * (∑ d ∈ Q, |A d|)
  calc
    |∑ d ∈ Q, A d * E d| ≤
        ∑ d ∈ Q, |A d * E d| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Q, |A d| * |E d| := by simp only [abs_mul]
    _ ≤ ∑ d ∈ Q, |A d| * (2 * T) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hE d hd) (abs_nonneg (A d))
    _ = (2 * T) * (∑ d ∈ Q, |A d|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring

/-- Completely explicit fallback envelope: at most four times the
cardinality of the ORIGINAL LOW complete-modulus support times the
absolute mass of the ORIGINAL prime prefix. No distribution hypothesis,
extra postulate, or independent upper/lower sieve bound enters this estimate.
It is deliberately NOT claimed to be o(H_N). -/
theorem actual_raw_licensed_lowq_primitive_le_support_card
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let Q := pairActualLowQModuli R S N cap w z X
    let T := ∑ p ∈ chenPrimePrefix (N + D), |W p|
    |∑ d ∈ Q,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| ≤
      4 * (Q.card : ℝ) * T := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let Q := pairActualLowQModuli R S N cap w z X
  let T : ℝ := ∑ p ∈ chenPrimePrefix (N + D), |W p|
  let A : ℕ → ℝ := fun d =>
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d
  let E : ℕ → ℝ := fun d =>
    finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  have hT : 0 ≤ T := Finset.sum_nonneg
    (fun p _ => abs_nonneg (W p))
  have hA (d : ℕ) : |A d| ≤ 2 := by
    change |supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d| ≤ 2
    calc
      _ ≤ |supportedPhysicalRho R N cap w z L d| +
          |supportedPhysicalRho S N cap w z L d| := abs_sub_le _ _
      _ ≤ 1 + 1 := add_le_add
          (supported_physical_rho_abs_le_one R N cap w z L d)
          (supported_physical_rho_abs_le_one S N cap w z L d)
      _ = 2 := by norm_num
  have hsum : (∑ d ∈ Q, |A d|) ≤ 2 * (Q.card : ℝ) := by
    calc
      _ ≤ ∑ _d ∈ Q, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        exact hA d
      _ = 2 * (Q.card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hbase :=
    actual_raw_licensed_lowq_primitive_le_coefficient_variation
      delta n e q om N D cap w z L W X
  dsimp only at hbase
  change |∑ d ∈ Q, A d * E d| ≤
    (2 * T) * (∑ d ∈ Q, |A d|) at hbase
  change |∑ d ∈ Q, A d * E d| ≤ 4 * (Q.card : ℝ) * T
  calc
    |∑ d ∈ Q, A d * E d| ≤
        (2 * T) * (∑ d ∈ Q, |A d|) := hbase
    _ ≤ (2 * T) * (2 * (Q.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (by norm_num) hT)
    _ = 4 * (Q.card : ℝ) * T := by ring

end
end ImbalancedChen.P4AOriginalFull87LowQAbsoluteEnvelope
