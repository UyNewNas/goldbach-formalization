import ImbalancedChen.P3ActualU8OriginalFifthPolicyPP
import ImbalancedChen.P3ActualU8UnitQuotientOffshift
import Mathlib.Tactic

/-!
P3.6: literal native-versus-common physical carrier for BOTH U8 source ranks.

This SOURCE_ONLY candidate removes a gap left by the previous full
prime-plus-unit signed response: the response was expressed on a
common enlarged carrier, while the genuine original fifth-policy
compiler uses its own smaller physical carrier.

Both original source types are transported by coefficient ZERO extension.
In particular, the quotient-one PAIRS are not silently dropped, and
their exact coprime mean is transported using the same signed real rho.
The final theorem identifies the combined native error with the
literal full-product offshift expression on the common carrier.

Neither the global final integer rho_T, arbitrary-log PP cancellation,
nor the admitted W_T smooth family is asserted.  Lean/Lake compilation
and kernel validation are pending.
-/

namespace ImbalancedChen.P3ActualU8PrimeUnitNativeCarrier

noncomputable section
open scoped BigOperators
open Classical
open P3ActualU8UnitQuotientOffshift

/-- Both original sharp-K prime triples and the *separate* quotient-one
prime pairs are invariant under the SAME zero-extension of the original
rough physical coefficient.  The original product and labelled
multiplicity of each rank, the original small Rosser sign choice and
the exact primitive coprime means are not replaced by surrogates. -/
theorem prime_unit_zero_extension
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    (Part3.primeProductSignedError 3 N N
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L))
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L))) =
    (Part3.primeProductSignedError 3 N N
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L)
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L)) := by
  rw [P3ActualU8CommonCarrierPP.actual_u8_rank3_PP_common_eq_raw
      retainOdd N cap w z L rough hcover,
    P3ActualU8CommonCarrierPP.labelled_distribution_common_eq_raw
      (currentChenUpsilon8UnitFibres N) unitPairProduct
      (fun _ => (1 : ℝ)) N retainOdd N cap w z L rough hcover]

/-- Specialization to the real, original historical fifth-capped policy.
The coefficient in the small/rough attachment is the literal INTEGER
first-exit Mobius coefficient cast to real; the attached rho itself
remains real-valued. This is not the unbuilt final causal compiler. -/
theorem original_fifth_prime_unit_zero_extension
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Fin 4 → Fin (m + 1)))
    (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
    (J5 : Finset (Fin 5 → Fin (m + 1)))
    (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ)
    (hcover : P1OriginalHistoricalPhysicalCoefficient.roughSupport
      e chi m omega J4 cap4 J5 cap5 N cap w z ⊆ rough) :
    (Part3.primeProductSignedError 3 N N
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fun d => (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
            e chi m omega J4 cap4 J5 cap5 N cap w z d : ℝ))
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L))
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fun d => (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
            e chi m omega J4 cap4 J5 cap5 N cap w z d : ℝ))
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L))) =
    (Part3.primeProductSignedError 3 N N
        (P1OriginalHistoricalPhysicalCoefficient.physicalModuli
          e chi m omega J4 cap4 J5 cap5 N cap w z)
        (P1OriginalHistoricalPhysicalCoefficient.rho
          e chi m omega J4 cap4 J5 cap5 N cap w z L)
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N
        (P1OriginalHistoricalPhysicalCoefficient.physicalModuli
          e chi m omega J4 cap4 J5 cap5 N cap w z)
        (P1OriginalHistoricalPhysicalCoefficient.rho
          e chi m omega J4 cap4 J5 cap5 N cap w z L)) := by
  let P := P1OriginalHistoricalPhysicalCoefficient.finalPolicy
    e chi m omega J4 cap4 J5 cap5 (N : ℝ)
  have hident := P3ActualU8OriginalFifthPolicyPP.original_fifth_rough_fixed_identification
    e chi m omega J4 cap4 J5 cap5 N cap w z
  dsimp only at hident
  have hcoverRaw : fixedRoughSupport (P false) N cap w z ⊆ rough := by
    rw [← hident.1]
    exact hcover
  have hbase := prime_unit_zero_extension
    (P false) N cap w z L rough hcoverRaw
  simpa only [P1OriginalHistoricalPhysicalCoefficient.physicalModuli,
    P1OriginalHistoricalPhysicalCoefficient.rho, hident.2] using hbase

/-- The native ORIGINAL fifth-policy signed U8 error, with both actual
source ranks, is precisely the common-carrier COMPLETE-PRODUCT divisor
offshift after zero extension. This makes explicit which real physical
coefficient enters the full arithmetic expression, rather than only
comparing abstract common-carrier signed responses. -/
theorem original_fifth_prime_unit_native_offshift
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Fin 4 → Fin (m + 1)))
    (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
    (J5 : Finset (Fin 5 → Fin (m + 1)))
    (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ)
    (hcover : P1OriginalHistoricalPhysicalCoefficient.roughSupport
      e chi m omega J4 cap4 J5 cap5 N cap w z ⊆ rough) :
    (Part3.primeProductSignedError 3 N N
        (P1OriginalHistoricalPhysicalCoefficient.physicalModuli
          e chi m omega J4 cap4 J5 cap5 N cap w z)
        (P1OriginalHistoricalPhysicalCoefficient.rho
          e chi m omega J4 cap4 J5 cap5 N cap w z L)
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N
        (P1OriginalHistoricalPhysicalCoefficient.physicalModuli
          e chi m omega J4 cap4 J5 cap5 N cap w z)
        (P1OriginalHistoricalPhysicalCoefficient.rho
          e chi m omega J4 cap4 J5 cap5 N cap w z L)) =
      actualU8PrimeUnitOffshift N
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fun d => (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
            e chi m omega J4 cap4 J5 cap5 N cap w z d : ℝ))
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L)) := by
  have heq := original_fifth_prime_unit_zero_extension
    e chi m omega J4 cap4 J5 cap5 N cap w z L rough hcover
  have hoff := actual_u8_prime_unit_same_rho_offshift N
    (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
    (smallRoughRho (actualSmallRosserSupport N cap w) rough
      (fun d => (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
        e chi m omega J4 cap4 J5 cap5 N cap w z d : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L))
  exact heq.symm.trans hoff

end
end ImbalancedChen.P3ActualU8PrimeUnitNativeCarrier
