import ImbalancedChen.P4AOriginalFull87SameQCellLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The prior P1.4 candidate compares the two ORIGINAL physical rho coefficients
at ONE complete modulus, with stopped, RAW-outside, actual 87 Cell and
LICENSED-outside invoices. Here we pass to the actual FINITE prime-product
test without inventing a new rho or a fabricated H_N payment.

The support is the union of the two ORIGINAL small-rough modulus supports.
We restrict it only AFTER the actual coefficients are constructed, by the
strict ORIGINAL full-modulus X < d highQTest. No Rosser factor, occurrence
multiplicity, sign or actual branch is modified, and there is no generic
surrogate owner/parent or independent stage-level analytic estimate.

The result is a FINITE physical same-rho charge. It does not establish the
required PP integer X, compare that charge with H_N, or prove the manuscript
prime-product AP input.
-/

namespace ImbalancedChen.P4AOriginalFull87PhysicalQAggregateInvoice
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87SameQCellLedger
  (actual_full_rho_q_abs_le_once_paid_real_invoices)
open P4AOriginalFull87FirstDisagreementTerminalL1
  (actualFirstDisagreementTerminalL1)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices
  (actualProducerThreeClassLeafBill)
open P4AOriginalFull87LicensedOutsideThreeInvoices
  (licensedOutsideHighQInvoice)

/-- UNION of the exact two original supported full-modulus populations.
This is a set of modulus LABELS only. The two rho coefficients still include
all original small Rosser factors and all signed terminal occurrences. -/
def pairActualPhysicalModuli (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  actualSmallRoughModuli (R false) N cap w z ∪
    actualSmallRoughModuli (S false) N cap w z

/-- Actual strict high-q part of that SAME pair of original supports. The
filter is on the FULL modulus d, never the rough selected product alone. -/
def pairActualHighQModuli (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (X : ℕ) : Finset ℕ :=
  (pairActualPhysicalModuli R S N cap w z).filter (fun d => X < d)

/-- One ORIGINAL physical policy can be evaluated over the common union
without changing its coefficient or introducing extra nonzero terms. -/
private theorem physical_on_original_union
    (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    physical R N cap w z L (highQTest X F) =
      ∑ d ∈ pairActualPhysicalModuli R S N cap w z,
        supportedPhysicalRho R N cap w z L d * highQTest X F d := by
  classical
  let sr := actualSmallRoughModuli (R false) N cap w z
  have hs : sr ⊆ pairActualPhysicalModuli R S N cap w z := by
    intro d hd
    simp only [pairActualPhysicalModuli, Finset.mem_union]
    exact Or.inl hd
  have hz : ∀ d ∈ pairActualPhysicalModuli R S N cap w z,
      d ∉ sr →
        supportedPhysicalRho R N cap w z L d * highQTest X F d = 0 := by
    intro d hd hdnot
    simp [supportedPhysicalRho, sr, hdnot]
  calc
    physical R N cap w z L (highQTest X F) =
        ∑ d ∈ sr, actualSmallRoughRho (R false) N cap w z L d *
          highQTest X F d := by rfl
    _ = ∑ d ∈ sr, supportedPhysicalRho R N cap w z L d *
          highQTest X F d := by
          apply Finset.sum_congr rfl
          intro d hd
          simp [supportedPhysicalRho, sr, hd]
    _ = ∑ d ∈ pairActualPhysicalModuli R S N cap w z,
          supportedPhysicalRho R N cap w z L d *
            highQTest X F d := by
          exact Finset.sum_subset hs hz

/-- The ORIGINAL RAW and LICENSED physical sums use ONE coefficient
difference, evaluated at every complete modulus from the shared support.
The cancellation occurs BEFORE taking any absolute values. -/
theorem actual_raw_licensed_physical_same_q_sum
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    physical R N cap w z L (highQTest X F) -
      physical S N cap w z L (highQTest X F) =
    ∑ d ∈ pairActualPhysicalModuli R S N cap w z,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) * highQTest X F d := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  have hR := physical_on_original_union R S N cap w z L X F
  have hS : physical S N cap w z L (highQTest X F) =
      ∑ d ∈ pairActualPhysicalModuli R S N cap w z,
        supportedPhysicalRho S N cap w z L d * highQTest X F d := by
    simpa only [pairActualPhysicalModuli, Finset.union_comm] using
      physical_on_original_union S R N cap w z L X F
  rw [hR, hS, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Strict integer high-q filtering of the true physical comparison,
AFTER the exact RAW/LICENSED coefficient difference has been formed.
No individual stopped/Cell coefficient receives the full-rho AP input. -/
theorem actual_raw_licensed_physical_strict_highq_sum
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    physical R N cap w z L (highQTest X F) -
      physical S N cap w z L (highQTest X F) =
    ∑ d ∈ pairActualHighQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) * F d := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  rw [actual_raw_licensed_physical_same_q_sum
    delta n e q om N cap w z L X F]
  unfold pairActualHighQModuli
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : X < d
  · simp [highQTest, h]
  · simp [highQTest, h]

/-- Sum the ORIGINAL pointwise invoices over the exact high-q pair support.
This is an absolute-weighted FINITE comparison, not an H_N asymptotic bound.
The five frontier categories and first-disagreement stopped term are paid
only once per complete physical modulus. -/
theorem actual_raw_licensed_physical_abs_le_highq_invoices
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    |physical R N cap w z L (highQTest X F) -
      physical S N cap w z L (highQTest X F)| ≤
    ∑ d ∈ pairActualHighQModuli R S N cap w z X,
      (actualFirstDisagreementTerminalL1 delta n e q om
        N cap w z L 0
          (P4AOriginalFull87FullRhoQBridge.qProbe d) +
        ((rawOutsideHighQInvoice delta e q om
            N cap w z L 0
              (P4AOriginalFull87FullRhoQBridge.qProbe d) +
          actualProducerThreeClassLeafBill delta n e q om
            N cap w z L 0
              (P4AOriginalFull87FullRhoQBridge.qProbe d)) +
         licensedOutsideHighQInvoice delta n e q om
           N cap w z L 0
             (P4AOriginalFull87FullRhoQBridge.qProbe d))) * |F d| := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  rw [actual_raw_licensed_physical_strict_highq_sum
    delta n e q om N cap w z L X F]
  calc
    |∑ d ∈ pairActualHighQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) * F d| ≤
      ∑ d ∈ pairActualHighQModuli R S N cap w z X,
        |(supportedPhysicalRho R N cap w z L d -
          supportedPhysicalRho S N cap w z L d) * F d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ pairActualHighQModuli R S N cap w z X,
          |supportedPhysicalRho R N cap w z L d -
            supportedPhysicalRho S N cap w z L d| * |F d| := by
          simp only [abs_mul]
    _ ≤ _ := by
          apply Finset.sum_le_sum
          intro d hd
          have hgt : X < d := (Finset.mem_filter.mp hd).2
          have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le X) hgt
          have hbound :=
            actual_full_rho_q_abs_le_once_paid_real_invoices
              delta n e q om N cap w z L d hdpos
          change
            |supportedPhysicalRho R N cap w z L d -
              supportedPhysicalRho S N cap w z L d| ≤
            actualFirstDisagreementTerminalL1 delta n e q om
              N cap w z L 0
                (P4AOriginalFull87FullRhoQBridge.qProbe d) +
            ((rawOutsideHighQInvoice delta e q om
                N cap w z L 0
                  (P4AOriginalFull87FullRhoQBridge.qProbe d) +
              actualProducerThreeClassLeafBill delta n e q om
                N cap w z L 0
                  (P4AOriginalFull87FullRhoQBridge.qProbe d)) +
             licensedOutsideHighQInvoice delta n e q om
               N cap w z L 0
                 (P4AOriginalFull87FullRhoQBridge.qProbe d)) at hbound
          exact mul_le_mul_of_nonneg_right hbound (abs_nonneg (F d))

end
end ImbalancedChen.P4AOriginalFull87PhysicalQAggregateInvoice
