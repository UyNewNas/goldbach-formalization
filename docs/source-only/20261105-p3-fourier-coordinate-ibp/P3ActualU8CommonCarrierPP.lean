import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP
import ImbalancedChen.FiniteUpperCarrierCore
import Mathlib.Tactic

/-!
P3.6 / SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Exact full-source U8 rank-three PP transport to a finite compiler COMMON
carrier containing the literal raw retained rough support.

IMPORTANT: the added carrier may contain moduli on which the raw coefficient
vanishes. It is an algebraic ZERO EXTENSION, not an identification with the
FINAL causally compiled integer rho_T; no level or coprimality property is
asserted for the additional carrier elements. Crucially the full signed PP
sum, exact coprime correction, density and the source's divisor majorant
are transported together, before taking an absolute value. The U8 source
is the actual labelled sharp-K triple family, including q=p2.
No analytic distribution assertion, HB compiler or target equivalent
hypothesis is introduced.
-/

namespace ImbalancedChen.P3ActualU8CommonCarrierPP

noncomputable section
open scoped BigOperators
open Classical

/-- All original labelled coprime means are invariant under an extension
by zero coefficients. The source labels and their multiplicities are
untouched, as is the exact totient denominator of each physical modulus. -/
theorem labelled_coprime_common_eq_raw {α : Type*}
    (S : Finset α) (f : α → ℕ) (W : α → ℝ)
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    p5z_labelledCoprimeCorrection S f W
      (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
      (smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fixedRoughCoefficient retainOdd N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L)) =
    p5z_labelledCoprimeCorrection S f W
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L) := by
  unfold p5z_labelledCoprimeCorrection
  exact sum_actualSmallRoughRho_mul_eq_on_common_carrier
    retainOdd N cap w z L rough hcover
    (fun q => (p5z_labelledCoprimeMass S f W q - p5z_labelledMass S W) /
      (Nat.totient q : ℝ))

/-- Absolute value is NOT taken termwise: this is one signed sum
over the complete physical modulus carrier, with the original
coprime mean inside each summand. -/
theorem labelled_distribution_common_eq_raw {α : Type*}
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (T : ℕ)
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    p5z_labelledDistributionError S f W T
      (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
      (smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fixedRoughCoefficient retainOdd N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L)) =
    p5z_labelledDistributionError S f W T
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L) := by
  unfold p5z_labelledDistributionError
  exact sum_actualSmallRoughRho_mul_eq_on_common_carrier
    retainOdd N cap w z L rough hcover
    (fun q => p5z_labelledCongruenceMass S f W T q -
      p5z_labelledCoprimeMass S f W q / (Nat.totient q : ℝ))

/-- Real ORIGINAL sharp-K U8 rank-three labelled PP, not an abstract
surrogate tensor. The repeated terminal-prime label is not removed. -/
theorem actual_u8_rank3_PP_common_eq_raw
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    Part3.primeProductSignedError 3 N N
      (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
      (smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fixedRoughCoefficient retainOdd N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L))
      (P5U8SharpKSource.physicalWeight N) =
    Part3.primeProductSignedError 3 N N
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L)
      (P5U8SharpKSource.physicalWeight N) := by
  calc
    _ = p5z_labelledDistributionError
        (P5U8SharpKSource.arithmeticTriples N) P5U8SharpKSource.product
        (fun _ => (1 : ℝ)) N
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L)) :=
      (P5U8SharpKSource.distribution_eq_physicalPP N _ _).symm
    _ = p5z_labelledDistributionError
        (P5U8SharpKSource.arithmeticTriples N) P5U8SharpKSource.product
        (fun _ => (1 : ℝ)) N
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) :=
      labelled_distribution_common_eq_raw _ _ _ N retainOdd N cap w z L rough hcover
    _ = _ := P5U8SharpKSource.distribution_eq_physicalPP N _ _

/-- The actual original productWeight insertion has the same value
on the common carrier, even though its DISPLAYED modulus set is larger.
The full source is summed with its original labels and signed rho. -/
theorem actual_u8_original_divisor_sum_common_eq_raw
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    (∑ m ∈ Finset.range N, P5U8SharpKSource.productWeight N m *
      physicalDivisorSum
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L)) (N - m)) =
    (∑ m ∈ Finset.range N, P5U8SharpKSource.productWeight N m *
      physicalDivisorSum
        (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) (N - m)) := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [actualSmallRoughRho_divisorSum_eq_on_common_carrier
    retainOdd N cap w z L rough hcover (N - m)]

/-- Literal raw coefficient viewed on the compiler's *union* carrier.
The inclusion required for exact zero extension is discharged by the
definition of actualUpperCommonRoughSupport. No claim about the
compiled coefficient or any new moduli's arithmetic legality follows. -/
theorem actual_u8_PP_on_union_compiler_carrier
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (compilerSupport : Finset ℕ) :
    Part3.primeProductSignedError 3 N N
      (smallRoughModuli (actualSmallRosserSupport N cap w)
        (actualUpperCommonRoughSupport retainOdd N cap w z compilerSupport))
      (smallRoughRho (actualSmallRosserSupport N cap w)
        (actualUpperCommonRoughSupport retainOdd N cap w z compilerSupport)
        (fixedRoughCoefficient retainOdd N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L))
      (P5U8SharpKSource.physicalWeight N) =
    Part3.primeProductSignedError 3 N N
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L)
      (P5U8SharpKSource.physicalWeight N) := by
  apply actual_u8_rank3_PP_common_eq_raw retainOdd N cap w z L
  change fixedRoughSupport retainOdd N cap w z ⊆
    fixedRoughSupport retainOdd N cap w z ∪ compilerSupport
  exact Finset.subset_union_left

end

end ImbalancedChen.P3ActualU8CommonCarrierPP
