import ImbalancedChen.Part3ActualCuspBasisWhittakerCoefficients
import ImbalancedChen.Part3OriginalFullModulusCuspInput

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original R20/R21 row coefficients now act on the actual existing
native cusp basis.  The first functional conjugates the common physical
m weight, so its outer conjugate restores the original weight.  The
second retains traceBeta and its composite signed index without a
conjugation.  Neither coefficient depends on the spectral height.

This file proves exact finite product algebra for actual basis Fourier
coefficients.  It does not assert an equality of this product with the
bare c sum; that equality still requires the full normalized trace.
No hTrace, spectrum field, generic rho, or replacement kernel is input.
-/

namespace ImbalancedChen.Part3.OriginalNativeCuspFunctionals20261102

noncomputable section
open Classical Finset
open scoped BigOperators MatrixGroups
open ActualFullCuspEigenbasis20261026b Gamma0ActualCuspsSourceOnly
open ActualCuspBasisWhittakerCoefficients20261102
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalSignedTraceInput20261102
open P3NativePeriod64SamplingSourceOnly (D4)

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key))
  (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
  (z : ℕ) [NeZero z] (hz : 0 < z)

/-- The exact common physical interval and phase, at infinity scaling Id. -/
def originalMFunctional (i : actualCuspBasisIndex z hz) : ℂ :=
  ∑ p ∈ commonMBlock J j,
    starRingEnd ℂ ((commonPoissonCompleted J j (ell 1)).weight p) *
      basisR z hz i (1 : SL(2, ℤ)) (p : ℤ)

/-- The exact signed primary row at the manuscript's fixed cusp-one scaling. -/
def originalNFunctional (i : actualCuspBasisIndex z hz) : ℂ :=
  ∑ n ∈ nCarrier D k z,
    traceBeta D r k upper negativeM ell z n *
      basisR z hz i cuspOneMatrix (traceIndex D k negativeM z n)

/-- Finite Fourier products from the same native basis give the two
actual linear functionals.  This introduces no spectral summation. -/
theorem original_native_row_product (i : actualCuspBasisIndex z hz) :
    (∑ n ∈ nCarrier D k z, ∑ p ∈ commonMBlock J j,
      (commonPoissonCompleted J j (ell 1)).weight p *
        traceBeta D r k upper negativeM ell z n *
        (starRingEnd ℂ (basisR z hz i (1 : SL(2, ℤ)) (p : ℤ)) *
          basisR z hz i cuspOneMatrix (traceIndex D k negativeM z n))) =
      starRingEnd ℂ (originalMFunctional J j ell z hz i) *
        originalNFunctional D r k upper negativeM ell z hz i := by
  unfold originalMFunctional originalNFunctional
  simp only [map_sum, map_mul, starRingEnd_apply, star_star]
  rw [Finset.sum_mul, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The one-quarter correction applies at every actual original p/n
index, including negative residue, primary sign and Poisson sign. -/
theorem original_native_coefficient_product
    (ha : D.block.atom.residue ≠ 0) (i : actualCuspBasisIndex z hz)
    {n p : ℕ} (hn : n ∈ nCarrier D k z) (hp : p ∈ commonMBlock J j) :
    starRingEnd ℂ (basisR z hz i (1 : SL(2, ℤ)) (p : ℤ)) *
        basisR z hz i cuspOneMatrix (traceIndex D k negativeM z n) =
      (starRingEnd ℂ (basisRhoK z hz i (1 : SL(2, ℤ)) (p : ℤ)) *
        basisRhoK z hz i cuspOneMatrix (traceIndex D k negativeM z n))/4 := by
  have hp0 : 0 < p :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) j) (mem_Ico.mp hp).1
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hnne : traceIndex D k negativeM z n ≠ 0 :=
    Int.natAbs_pos.mp (traceIndex_natAbs_pos D k negativeM z hn ha)
  exact basisR_product z hz i _ _ hpne hnne

end
end ImbalancedChen.Part3.OriginalNativeCuspFunctionals20261102
