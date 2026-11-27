import ImbalancedChen.Part3CanonicalReciprocalData
import ImbalancedChen.Part3ActualModeJointBetaPositiveCount
import ImbalancedChen.Part3FixedRhoPrimaryFiniteCore

/-!
SOURCEONLY / UNCOMPILED. A separate fixed-rho numerator prime-support split.
This is NOT the already reviewed nu0=gcd(c,|y|) modulus split.
No installed source, cache, evidence, module count or provider is changed.

Existing CanonicalReciprocalData supportedPart/coprimePart APIs are reused;
their products are not redefined. Int exact division preserves the sign.
The finite source fibres use a computed key, so coverage and uniqueness do
not follow from an overlapping divisibility test. The original physical c
and fixed signed rho stay literal in every displayed kernel call. In general
rhoPrimaryNu rho y does NOT divide c, and no c/nu modulus is introduced.

All bodies below are source proposals, not claims of elaboration success.
No cusp conversion, ABL estimate, Eq24/25 bound or main theorem is asserted.
-/

namespace ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
noncomputable section
open Classical Finset
open CanonicalReciprocalData
open ActualReciprocalSquarePoissonSourceOnly
open ActualCompletedSquarePushforwardSourceOnly
open ActualModeBetaPositiveCountSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Direct actual-source consumer; nonzero y comes from its original filter.
No arbitrary row, coprime-gate hypothesis or spectral input is supplied. -/
theorem actual_primaryFibre_gate (e : MediumAtom) (D delta g l : ℕ)
    (Z : ℝ) (negative : Bool) {nu : ℕ} {s : Source}
    (hs : s ∈ primaryFibre
      (ActualSeparatedRowPacketMatchSourceOnly.signedResidue negative e.residue)
      (actualNonzeroSource e D delta g l Z negative) nu) :
    (nu : ℤ) ∣ s.1 * difference s.2.1 s.2.2 ∧
      ((output s).2 / (nu : ℤ)).natAbs.Coprime e.residue.natAbs := by
  have hg := primaryFibre_gate
    (rho := ActualSeparatedRowPacketMatchSourceOnly.signedResidue negative e.residue)
    (U := actualNonzeroSource e D delta g l Z negative)
    (fun t ht => (mem_filter.mp ht).2) hs
  constructor
  · simpa only [output, outputY] using hg.1
  · simpa only [ActualM2FinitePoissonAdapterSourceOnly.signedResidue_natAbs] using hg.2

end
end ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
