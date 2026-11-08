import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.P3ActualU8DirectUnitPayment

/-!
P3.6 / SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The genuine finite small/rough Rosser attachment, not a freely chosen
physical weight, is now inserted into the actual U8 prime-only count.
The upper majorant is PROVED upstream for all integer test arguments;
it is not supplied as an analytic or target-equivalent assumption.

The integer presieve cutoff is Nat.ceil z. This is NOT a rough
auxiliary level or the U8 quotient q=1. Its strict prime endpoint
corresponds to p<z exactly, including integral z. The original unit
quotient is paid as a raw source count, never with a second rho.

No claim is made that an arbitrary retention policy is the manuscript's
final frozen causal policy, that the real-valued coefficient has been
identified as the final integer rho_T, or that PP has log savings.
The staged P3ActualU8DirectUnitPayment import must be supplied when
source-only files are mounted into an appropriate Lean module hierarchy.
-/

namespace ImbalancedChen.P3ActualU8RawPhysicalSieve

noncomputable section
open Filter
open scoped BigOperators

/-- The actual displayed physical carrier retains squarefreeness,
coprimality to the target, and the *same* complete sieve product
used in the pointwise Rosser majorant. The rough-support cap is not
substituted for the physical modulus carrier. -/
theorem actual_u8_raw_physical_moduli_legal
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hwz : w ≤ z) :
    ∀ q ∈ actualSmallRoughModuli retainOdd N cap w z,
      Squarefree q ∧ Nat.Coprime q N ∧
        q ∣ sieveProduct N (Nat.ceil z) := by
  intro q hq
  exact ⟨actualSmallRoughModuli_squarefree retainOdd N cap w z hq,
    actualSmallRoughModuli_coprime_target retainOdd N cap w z hq,
    actualSmallRoughModuli_dvd_sieveProduct_ceil retainOdd N cap w z hwz hq⟩

/-- Non-circular physical insertion: neither a conjectural PP bound nor
a pointwise majorant is assumed. The actual Rosser/small-rough majorant
supplies the latter at the exact real cutoff Nat.ceil z. Labels, the
p₂=q repeated-prime endpoint, original rank-three PP coefficient and
the exact coprime correction remain unchanged. -/
theorem actual_u8_upper_at_raw_physical_coefficient
    (N cap : ℕ) (retainOdd : List ℕ → Bool) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ))
    (hphysicalCut : ((Nat.ceil z : ℕ) : ℝ) ≤
      (N : ℝ) ^ (1 / 5 : ℝ)) :
    currentChenUpsilon8 N ≤
      p5z_labelledMass (Finset.range N) (P5U8SharpKSource.productWeight N) *
        physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L) +
      p5z_labelledCoprimeCorrection (Finset.range N) id
        (P5U8SharpKSource.productWeight N)
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) +
      Part3.primeProductSignedError 3 N N
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L)
        (P5U8SharpKSource.physicalWeight N) +
      ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
      ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  have hmajor := actualSmallRoughRho_sieveProduct_majorant
    retainOdd N cap w z L hL hwL hwz hzcap
  exact P3ActualU8DirectUnitPayment.actual_u8_upper_via_prime_PP_no_unit_PP
    N (Nat.ceil z) (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L)
      hphysicalCut hmajor

/-- The small-prime and unit-quotient power payments are uniform over
ALL admitted finite attachment choices. In particular the eventual
target threshold is chosen BEFORE the retention policy, physical Q,
single rho, auxiliary cap, or real sieve cutoffs. Only the actual
prime-triple signed PP still needs an analytic saving. -/
theorem eventually_actual_u8_raw_physical_upper
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (cap : ℕ) (retainOdd : List ℕ → Bool) (w z L : ℝ),
        1 < L → w ≤ L → w ≤ z → z ≤ (cap : ℝ) →
        ((Nat.ceil z : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) →
        currentChenUpsilon8 N ≤
          p5z_labelledMass (Finset.range N) (P5U8SharpKSource.productWeight N) *
            physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
              (actualSmallRoughRho retainOdd N cap w z L) +
          p5z_labelledCoprimeCorrection (Finset.range N) id
            (P5U8SharpKSource.productWeight N)
            (actualSmallRoughModuli retainOdd N cap w z)
            (actualSmallRoughRho retainOdd N cap w z L) +
          Part3.primeProductSignedError 3 N N
            (actualSmallRoughModuli retainOdd N cap w z)
            (actualSmallRoughRho retainOdd N cap w z L)
            (P5U8SharpKSource.physicalWeight N) +
          ε * singularNormalization N := by
  filter_upwards
    [P3ActualU8DirectUnitPayment.eventually_actual_u8_upper_via_prime_PP_no_unit_PP ε hε]
    with N hbase cap retainOdd w z L hL hwL hwz hzcap hcut
  exact hbase (Nat.ceil z)
    (actualSmallRoughModuli retainOdd N cap w z)
    (actualSmallRoughRho retainOdd N cap w z L) hcut
    (actualSmallRoughRho_sieveProduct_majorant
      retainOdd N cap w z L hL hwL hwz hzcap)

end

end ImbalancedChen.P3ActualU8RawPhysicalSieve
