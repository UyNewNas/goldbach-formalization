import ImbalancedChen.P4AOriginalFull87LowQRealLedgerEnvelope
import ImbalancedChen.CoprimeRecentering
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous original low-q RAW/LICENSED discrepancy invoice used the
unrestricted prime absolute mass 2*T_W at EVERY complete modulus. This
packet keeps the *actual* prime residue and coprime fibres at each q,
and pays their local mass against the real first-disagreement / 87-Cell
producer books. This is one ALTERNATIVE to the previous global 2*T_W
invoice, not a second reserve payment.

q=1 is exactly free: the original primitive discrepancy vanishes there.
All q are original physical moduli from the two actual policies. The
signed source coefficients, Rosser beta, original eighth-level owners,
first stopped disagreements, and repeated occurrences are unchanged.
No geometric witness, Gevrey input, PP estimate or H_N saving is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87LowQLocalPrimeFibres
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87PhysicalQAggregateInvoice
  (pairActualPhysicalModuli pairActualHighQModuli)
open P4AOriginalFull87PPCutoffLowQInvoice
  (pairActualLowQModuli actual_raw_licensed_full_q_arithmetic_support
   actual_raw_licensed_primitive_discrepancy_high_low)
open P4AOriginalFull87SameQCellLedger
  (actual_full_rho_q_abs_le_once_paid_real_invoices)
open P4AOriginalFull87LowQRealLedgerEnvelope
  (actualPerQFirstDisagreementLedgerCharge)

/-- A *local* literal absolute-prime charge for one original complete
physical modulus. The first mass is on p ≡ N (mod d); the second is
on the genuinely d-coprime prime source divided by the ORIGINAL φ(d).
For d=1 the primitive discrepancy is exactly zero, so the invoice is
set to zero rather than charging the prime mass twice.
This is NOT an arbitrary upper-bound field of a new policy structure. -/
def actualLocalPrimitivePrimeCharge
    (N D d : ℕ) (W : ℕ → ℝ) : ℝ :=
  if d = 1 then 0 else
    finiteCongruenceMass (chenPrimePrefix (N + D))
      (fun p => |W p|) N d +
    finiteCoprimeMass (chenPrimePrefix (N + D))
      (fun p => |W p|) d / (Nat.totient d : ℝ)

private theorem abs_congruence_le_local_prime_abs
    (S : Finset ℕ) (W : ℕ → ℝ) (a d : ℕ) :
    |finiteCongruenceMass S W a d| ≤
      finiteCongruenceMass S (fun p => |W p|) a d := by
  change |∑ p ∈ S.filter (fun p => Nat.ModEq d p a), W p| ≤
    ∑ p ∈ S.filter (fun p => Nat.ModEq d p a), |W p|
  exact Finset.abs_sum_le_sum_abs _ _

private theorem abs_coprime_le_local_prime_abs
    (S : Finset ℕ) (W : ℕ → ℝ) (d : ℕ) :
    |finiteCoprimeMass S W d| ≤
      finiteCoprimeMass S (fun p => |W p|) d := by
  change |∑ p ∈ S.filter (fun p => Nat.Coprime p d), W p| ≤
    ∑ p ∈ S.filter (fun p => Nat.Coprime p d), |W p|
  exact Finset.abs_sum_le_sum_abs _ _

/-- Both literal prime-fibre masses are nonnegative, including arbitrary
signed W. No distribution estimate enters this elementary fact. -/
private theorem actual_local_charge_nonneg
    (N D d : ℕ) (W : ℕ → ℝ) :
    0 ≤ actualLocalPrimitivePrimeCharge N D d W := by
  by_cases hd1 : d = 1
  · simp [actualLocalPrimitivePrimeCharge, hd1]
  · have hc : 0 ≤
        finiteCongruenceMass (chenPrimePrefix (N + D))
          (fun p => |W p|) N d := by
      unfold finiteCongruenceMass
      exact Finset.sum_nonneg (fun p _ => abs_nonneg (W p))
    have hp : 0 ≤
        finiteCoprimeMass (chenPrimePrefix (N + D))
          (fun p => |W p|) d := by
      unfold finiteCoprimeMass
      exact Finset.sum_nonneg (fun p _ => abs_nonneg (W p))
    have hphi : (0 : ℝ) ≤ (Nat.totient d : ℝ) := Nat.cast_nonneg _
    simp only [actualLocalPrimitivePrimeCharge, if_neg hd1]
    exact add_nonneg hc (div_nonneg hp hphi)

/-- Genuine finite primitive discrepancy is pointwise controlled by the
actual selected AP absolute mass and exact coprime mean absolute mass.
The modulus-one fibre costs zero, not 2*T_W. -/
private theorem actual_primitive_le_local_prime_fibres
    (N D d : ℕ) (W : ℕ → ℝ) (hd : 0 < d) :
    |finitePrimitiveDiscrepancy
      (chenPrimePrefix (N + D)) W N d| ≤
        actualLocalPrimitivePrimeCharge N D d W := by
  by_cases hd1 : d = 1
  · subst d
    simp [actualLocalPrimitivePrimeCharge]
  · let S := chenPrimePrefix (N + D)
    have hphi : (0 : ℝ) < (Nat.totient d : ℝ) := by
      exact_mod_cast (Nat.totient_pos.mpr hd)
    have hc := abs_congruence_le_local_prime_abs S W N d
    have hp := abs_coprime_le_local_prime_abs S W d
    change |finiteCongruenceMass S W N d -
        finiteCoprimeMass S W d / (Nat.totient d : ℝ)| ≤
      (if d = 1 then 0 else
        finiteCongruenceMass S (fun p => |W p|) N d +
        finiteCoprimeMass S (fun p => |W p|) d /
          (Nat.totient d : ℝ))
    rw [if_neg hd1]
    calc
      |finiteCongruenceMass S W N d -
          finiteCoprimeMass S W d / (Nat.totient d : ℝ)| ≤
        |finiteCongruenceMass S W N d| +
          |finiteCoprimeMass S W d / (Nat.totient d : ℝ)| :=
        abs_sub_le _ _
      _ = |finiteCongruenceMass S W N d| +
            |finiteCoprimeMass S W d| / (Nat.totient d : ℝ) := by
        rw [abs_div, abs_of_pos hphi]
      _ ≤ finiteCongruenceMass S (fun p => |W p|) N d +
            finiteCoprimeMass S (fun p => |W p|) d /
              (Nat.totient d : ℝ) :=
        add_le_add hc (div_le_div_of_nonneg_right hp hphi.le)

/-- Main finite refinement: a complete-rho PP discrepancy bound transfers
to strict d>X by charging the *same* real first-disagreement and original
87-Cell occurrence invoice, now against the literal prime fibres of
each low modulus instead of an unrestricted factor 2*T_W.
The correction is not automatically o(H_N); no external PP theorem
has been applied to a filtered family. -/
theorem actual_highq_primitive_le_full_plus_real_local_prime_fibres
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    |∑ d ∈ pairActualHighQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy
          (chenPrimePrefix (N + D)) W N d| ≤
    |∑ d ∈ pairActualPhysicalModuli R S N cap w z,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy
          (chenPrimePrefix (N + D)) W N d| +
    ∑ d ∈ pairActualLowQModuli R S N cap w z X,
      actualPerQFirstDisagreementLedgerCharge
        delta n e q om N cap w z L d *
      actualLocalPrimitivePrimeCharge N D d W := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy
    e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let M := pairActualPhysicalModuli R S N cap w z
  let H := pairActualHighQModuli R S N cap w z X
  let Q := pairActualLowQModuli R S N cap w z X
  let A : ℕ → ℝ := fun d =>
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d
  let E : ℕ → ℝ := fun d =>
    finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  let B : ℕ → ℝ := fun d =>
    actualPerQFirstDisagreementLedgerCharge
      delta n e q om N cap w z L d
  let C : ℕ → ℝ := fun d =>
    actualLocalPrimitivePrimeCharge N D d W
  have hlow :
      |∑ d ∈ Q, A d * E d| ≤ ∑ d ∈ Q, B d * C d := by
    calc
      |∑ d ∈ Q, A d * E d| ≤
          ∑ d ∈ Q, |A d * E d| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Q, |A d| * |E d| := by simp only [abs_mul]
      _ ≤ ∑ d ∈ Q, B d * C d := by
        apply Finset.sum_le_sum
        intro d hd
        have hfull : d ∈ M := (Finset.mem_filter.mp hd).1
        have hvalid : 0 < d ∧ Squarefree d ∧ d.Coprime N :=
          (actual_raw_licensed_full_q_arithmetic_support
            delta n e q om N cap w z) d hfull
        have hA :=
          actual_full_rho_q_abs_le_once_paid_real_invoices
            delta n e q om N cap w z L d hvalid.1
        dsimp only at hA
        change |A d| ≤ B d at hA
        have hB : 0 ≤ B d := (abs_nonneg (A d)).trans hA
        have hC : |E d| ≤ C d :=
          actual_primitive_le_local_prime_fibres N D d W hvalid.1
        exact (mul_le_mul_of_nonneg_right hA (abs_nonneg (E d))).trans
          (mul_le_mul_of_nonneg_left hC hB)
  have hsplit : (∑ d ∈ M, A d * E d) =
      (∑ d ∈ H, A d * E d) + (∑ d ∈ Q, A d * E d) := by
    exact actual_raw_licensed_primitive_discrepancy_high_low
      delta n e q om N D cap w z L W X
  have hdiff : (∑ d ∈ H, A d * E d) =
      (∑ d ∈ M, A d * E d) - (∑ d ∈ Q, A d * E d) := by
    linarith
  change |∑ d ∈ H, A d * E d| ≤
    |∑ d ∈ M, A d * E d| + ∑ d ∈ Q, B d * C d
  calc
    |∑ d ∈ H, A d * E d| =
        |(∑ d ∈ M, A d * E d) - (∑ d ∈ Q, A d * E d)| := by
      rw [hdiff]
    _ ≤ |∑ d ∈ M, A d * E d| +
          |∑ d ∈ Q, A d * E d| := abs_sub_le _ _
    _ ≤ |∑ d ∈ M, A d * E d| +
          ∑ d ∈ Q, B d * C d := add_le_add_left hlow _

end
end ImbalancedChen.P4AOriginalFull87LowQLocalPrimeFibres
