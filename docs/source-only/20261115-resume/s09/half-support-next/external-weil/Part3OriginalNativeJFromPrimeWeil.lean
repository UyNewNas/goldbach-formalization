import ImbalancedChen.Part3OriginalPositiveHalfSupport
import ImbalancedChen.Part3OriginalNativeJFromHalfSupport

/-! Source-only endpoint composition.  This file does not constitute a
kernel-accepted full-J result until the external closure, compatibility,
and all six adapters have passed the root-controlled acceptance run. -/
namespace ImbalancedChen.Part3.OriginalNativeJFromPrimeWeil20261115
noncomputable section
open Finset Real
open scoped BigOperators Classical
open OriginalExceptionalJNativeCompletion20261110 (pascadiJ classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)

theorem original_range {ε : ℝ} (ep : 0<ε) (A : ℝ) (ap : 0≤A) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset ℕ+) (j : ℕ) (Q X ω : ℝ),0<Q → 0<X →
    S⊆classicalLevels Q → X≤A*max (classicalMScale j) (Q^2/classicalMScale j) →
    pascadiJ S X j ω≤C*((1+Q)*(1+classicalMScale j))^ε*(Q+classicalMScale j)*classicalMScale j :=
  OriginalNativeJFromHalfSupport20261113.original_range_of_half_support
    OriginalPositiveHalfSupport20261115.positive_half_support ep A ap

end
end ImbalancedChen.Part3.OriginalNativeJFromPrimeWeil20261115
