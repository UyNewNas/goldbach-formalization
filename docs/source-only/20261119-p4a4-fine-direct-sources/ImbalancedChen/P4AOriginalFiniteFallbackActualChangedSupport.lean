import ImbalancedChen.P4AOriginalFiniteFallbackWallRate
import ImbalancedChen.P4AOriginalFiniteFallbackProjection

/-!
SOURCE_ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.

Transport the already proved full tagged changed-cell coverage from the
projected zero-cutoff policy to the actual positive-cutoff policy. This
is a pointwise support statement, not an additional wall-rate estimate or
reserve payment. The policy remains the original high/low dispatcher, and
no tag, changed cell, prime word or source occurrence is discarded.
-/
namespace ImbalancedChen.P4AOriginalFiniteFallbackActualChangedSupport
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteFallbackRange (Bounded)
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport
open P4AFull87MarkedPrimePayment P4AFull87ActualAffineDeletion P4AFull87OrdinaryAdmissionDeletion
open P2CanonicalWallFullResidualPayment
open P4AOriginalFiniteFallbackWallRate (Charts centresFor)

/-- Every changed tagged cell of the ACTUAL positive-cutoff policy is
covered by one of the original finite wall charts, on the same physical
carrier and with the same source data. -/
theorem actual_changed_seen
    (T : Bank) (hT : Bounded T) (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (D : OriginalData) (he : 0 ≤ D.e)
    (N cap : ℕ) (hN : 2 ≤ N) (omega v tau : ℝ)
    (hw : 0 < omega) (hv : omega ≤ v) (ht : 0 < tau)
    (tags : ℕ → List Bool) {x : ℕ}
    (hx : x ∈ universe N cap ((N : ℝ)^omega) ((N : ℝ)^v))
    (hc : changed (F T delta n D omega N) tags N cap
      ((N : ℝ)^omega) ((N : ℝ)^v) tau x) :
    ∃ i : Charts T delta n D,
      x ∈ covered N cap (J0 omega) omega v ((J0 omega : ℝ)*tau)
        (centresFor T delta n D N (J0 omega) i) := by
  have hcut := P4AOriginalFiniteFallbackProjection.support_cut T delta n D
    (by omega : 1 ≤ N) cap (le_of_lt hw) ((N : ℝ)^v)
  have hc0 : changed (F T delta n D 0 N) tags N cap
      ((N : ℝ)^omega) ((N : ℝ)^v) tau x := by
    simpa only [changed, outer, inner, hcut] using hc
  exact P4AOriginalFiniteFallbackWallRate.changed_seen T hT delta hd n D he
    N cap hN omega v tau hw hv ht tags hx hc0

end
end ImbalancedChen.P4AOriginalFiniteFallbackActualChangedSupport
