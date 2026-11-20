import ImbalancedChen.P3ActualU6LowerModulusPrimeSplit
import ImbalancedChen.P3ActualEvenLowerRoughEulerToTargetLog
import Mathlib.Tactic

/-!
P3.6, frozen original manuscript
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §1 (PP), §3 (T), §4 (F).

Assemble ALL original U6 even-first-exit LOWER labelled pairs, not a
surrogate quotient rho: exact primitive mean, actual shifted signed
discrepancy and the not-yet-vanishing quotient-prime correction. Pair
multiplicities and distinct labels are kept by summing the REAL
`P5CausalRhoFactorization.pairs` once for EACH original `sixthSupport` t.
No collision between different t is silently quotiented out.

The previous one-row Mertens/active-small estimate has one constant C
chosen BEFORE N, A, the full policy, w and L. Its aggregate absolute
bound is paid with the exact sum of ORIGINAL physical prefix inverse
phi; that latter mass remains an INTERNAL obligation. Neither this
source nor its premises asserts the complete compiler rho_N identity,
a nonzero-shift PP bound, or a polylogarithmic prefix mass.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualU6LowerModulusPrimeSplit
open ImbalancedChen.P3ActualEvenLowerRoughEulerToTargetLog
open ImbalancedChen.P3ActualRawActiveLevelTotientCap

private def originalZ (N : ℕ) : ℝ :=
  P5CausalRhoQuotientBridge.cutoff N

private def originalCap (N : ℕ) : ℕ := Nat.ceil (originalZ N)

private def originalQ (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : Finset ℕ :=
  actualLowerSmallRoughModuli (policy t) N (originalCap N)
    (w t) (originalZ N)

private def originalRho (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : ℕ → ℤ :=
  actualEvenLowerIntegerRho (policy t) N (originalCap N)
    (w t) (originalZ N) (L t)

/-- The literal labelled AP expression, keeping all source pairs and
multiplicities BEFORE the quotient convolution. -/
def labelledRowAP (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : ℝ :=
  ∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N (originalCap N)
      (w t) (originalZ N),
    (actualEvenLowerPairInt (policy t) N (originalCap N)
      (w t) (originalZ N) (L t) x : ℝ) *
    (chenPrimeAPCount N N (((t.1 * t.2) * x.1) * x.2) -
      chenCentrePrimeAPCount N N (((t.1 * t.2) * x.1) * x.2))

/-- The EXACT primitive mean with the row's own prefix-prime
correction: it cannot be replaced by a common uncorrected scalar. -/
def rowPrimitiveMean (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : ℝ :=
  (((chenAdditivePrimeCarrier N).card : ℝ) -
      chenPrimeDivisorCount N (t.1 * t.2)) *
    (∑ q ∈ originalQ N policy w t,
      (originalRho N policy w L t q : ℝ) /
        (Nat.totient ((t.1 * t.2) * q) : ℝ))

/-- The signed nonzero-shift discrepancy remains a SEPARATE and
unpaid arithmetic term at each genuine complete physical modulus. -/
def rowPrimitiveDiscrepancy (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : ℝ :=
  ∑ q ∈ originalQ N policy w t,
    (originalRho N policy w L t q : ℝ) *
      finitePrimitiveDiscrepancy
        (chenAdditivePrimeCarrier N) (fun _ => 1) N ((t.1 * t.2) * q)

/-- Only the quotient-prime part; the prefix-prime part already sits
in `rowPrimitiveMean`. This is not an AP-discrepancy bound. -/
def rowQuotientPrimeCorrection (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : ℝ :=
  ∑ q ∈ originalQ N policy w t,
    (originalRho N policy w L t q : ℝ) *
      (chenPrimeDivisorCount N q /
        (Nat.totient ((t.1 * t.2) * q) : ℝ))

/-- Exact all-row original prefix mass, NOT assumed polylogarithmic. -/
def originalU6PrefixMass (N : ℕ) : ℝ :=
  ∑ t ∈ sixthSupport N, (Nat.totient (t.1 * t.2) : ℝ)⁻¹

/-- All the genuine original labelled U6 LOWER rows, with NO merging
of distinct source labels, obey one exact finite primitive ledger. -/
theorem all_original_U6_lower_labelled_recenter
    (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : ∀ t ∈ sixthSupport N,
      w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    (∑ t ∈ sixthSupport N, labelledRowAP N policy w L t) =
      (∑ t ∈ sixthSupport N, rowPrimitiveMean N policy w L t) +
      (∑ t ∈ sixthSupport N, rowPrimitiveDiscrepancy N policy w L t) -
      (∑ t ∈ sixthSupport N, rowQuotientPrimeCorrection N policy w L t) := by
  calc
    _ = ∑ t ∈ sixthSupport N,
          (rowPrimitiveMean N policy w L t +
           rowPrimitiveDiscrepancy N policy w L t -
           rowQuotientPrimeCorrection N policy w L t) := by
          apply Finset.sum_congr rfl
          intro t ht
          simpa [labelledRowAP, rowPrimitiveMean,
            rowPrimitiveDiscrepancy, rowQuotientPrimeCorrection,
            originalQ, originalRho, originalZ, originalCap] using
            (actual_U6_lower_labelled_recenter_split
              N t ht policy w L (hwz t ht))
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The SAME universal Mertens constant works for every row of the
original U6 selector. The physical prefix reciprocal-totient mass
is displayed and NOT silently called O(log^E N). The hypothesis
`∀t, L(t)≤A` is explicit and must come from the actual level producer;
it is NOT deduced from arbitrary policy/w/L or moved to external inputs. -/
theorem exists_all_original_U6_quotient_prime_correction_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (hN : 2 ≤ N)
        (policy : (ℕ × ℕ) → List ℕ → Bool)
        (w L : (ℕ × ℕ) → ℝ),
        (∀ t ∈ sixthSupport N,
          w t ≤ P5CausalRhoQuotientBridge.cutoff N) →
        (∀ t ∈ sixthSupport N, L t ≤ (A : ℝ)) →
        |∑ t ∈ sixthSupport N,
          rowQuotientPrimeCorrection N policy w L t| ≤
          originalU6PrefixMass N *
            (logTotientCap A * (C * (1 + Real.log (N : ℝ))) *
              ((Nat.log 2 A : ℝ) + C * (1 + Real.log (N : ℝ)))) := by
  obtain ⟨C, hC, hrow⟩ :=
    exists_actual_U6_lower_quotient_correction_target_log
  refine ⟨C, hC, ?_⟩
  intro N A hN policy w L hwz hLA
  let U : ℝ := C * (1 + Real.log (N : ℝ))
  let F : ℝ := logTotientCap A * U * ((Nat.log 2 A : ℝ) + U)
  have hpoint (t : ℕ × ℕ) (ht : t ∈ sixthSupport N) :
      |rowQuotientPrimeCorrection N policy w L t| ≤
        (Nat.totient (t.1 * t.2) : ℝ)⁻¹ * F := by
    have h := hrow N A hN t ht policy w L (hwz t ht) (hLA t ht)
    simpa [rowQuotientPrimeCorrection, originalQ, originalRho,
      originalZ, originalCap, F, U] using h
  change |∑ t ∈ sixthSupport N,
      rowQuotientPrimeCorrection N policy w L t| ≤
        originalU6PrefixMass N * F
  calc
    _ ≤ ∑ t ∈ sixthSupport N,
          |rowQuotientPrimeCorrection N policy w L t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ sixthSupport N,
          (Nat.totient (t.1 * t.2) : ℝ)⁻¹ * F := by
          apply Finset.sum_le_sum
          intro t ht
          exact hpoint t ht
    _ = originalU6PrefixMass N * F := by
          simp only [originalU6PrefixMass, Finset.sum_mul]

end
end ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
