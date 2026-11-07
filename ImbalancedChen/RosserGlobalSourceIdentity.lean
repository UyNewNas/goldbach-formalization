import ImbalancedChen.RosserOddLayerIdentity

/-!
# Global positive-residual identity for the genuine Rosser source

The pinned `goldbach` revision `09b97db5764ade1246bfb77206baa1b124760958`
already proves the all-positive-residual identity by induction in
`MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiUpperRosserBoundarySourceSuccLayer.lean`,
at line 1107. That proved theorem is private; the provider's public wrapper
only states the narrower residual interval `[3/2,4]`.

This module deliberately depends on that pinned private declaration. The local
term elaborator constructs its exact internal name and returns a reference to
the existing proof constant. It supplies no new mathematical premise. Both
public theorems and all generated helper declarations are subject to the same
declaration inventory, safety checks, and transitive-axiom audit as other leaves.
The internal name must be reviewed if the provider pin changes.
-/

namespace ImbalancedChen

open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

/-- Exact internal name at the documented provider revision. The numerical
private-name component is constructed as `Name.num`, not a string component. -/
private def pinnedRosserGlobalSourceIdentityName : Lean.Name :=
  let p := (`_private.MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserBoundarySourceSuccLayer).num 0
  (((p.str "MathlibNt").str "SieveTheory").str "LinearSieve").str "source_layer_identity_all"

local elab "pinnedRosserGlobalSourceIdentity" : term =>
  pure (Lean.mkConst pinnedRosserGlobalSourceIdentityName)

/-- The full positive-residual identity, transported from the explicitly
documented proved private constant of the fixed provider revision. -/
theorem upperRosserBoundarySourceIntegral_eq_suzukiLayer_of_pos
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    upperRosserBoundarySourceIntegral k s 1 = suzukiLayer 1 2 (2 * k + 1) s := by
  exact pinnedRosserGlobalSourceIdentity k s hs

/-- The actual odd-region Lebesgue integral is the genuine Suzuki odd layer
for every positive residual, including pair depth zero. -/
theorem rosserOddLayerIntegral_eq_suzukiLayer_of_pos
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    rosserOddLayerIntegral k s = suzukiLayer 1 2 (2 * k + 1) s := by
  rw [rosserOddLayerIntegral_eq_boundaryMass k s hs]
  exact upperRosserBoundarySourceIntegral_eq_suzukiLayer_of_pos k s hs

end ImbalancedChen
