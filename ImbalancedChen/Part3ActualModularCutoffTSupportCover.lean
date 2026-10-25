import ImbalancedChen.Part3ActualModularCutoffCompactSupport

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual compact orbit cover extends from nonzero cutoff points to the
ENTIRE topological support. The saturation is closed because it is the
continuous preimage of the genuine compact image in the actual Hausdorff
quotient. This includes cutoff-zero boundary points needed when dividing
by a normalized compact Poincare denominator. No core membership follows.
-/

namespace ImbalancedChen.Part3.ActualModularCutoffTSupportCover20261025a

noncomputable section
open Set
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0EffectiveActionKernel20261024z
open Gamma0EffectiveFiniteUnfolding20261025a Gamma0CompactTensorPoincareC2Core20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularSmoothCutoffL2Tail20261025a
open ActualModularCutoffCompactSupport20261025a

theorem quotientCutoff_tsupport_subset (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1≤Y) :
    tsupport (quotientCutoff N Y)⊆quotientTruncatedCarrier N (2*Y) := by
  letI := quotient_t2 N
  exact closure_minimal (quotientCutoff_support_subset N Y hY)
    (quotientTruncatedCarrier_isCompact N (2*Y)).isClosed

/-- The full physical topological support lies in the actual closed
saturation of the finite compact translated carrier. -/
theorem globalCutoff_tsupport_saturation (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1≤Y) :
    tsupport (globalCutoff Y)⊆orbitProjection N ⁻¹' quotientTruncatedCarrier N (2*Y) := by
  letI := quotient_t2 N
  have hclosed : IsClosed (orbitProjection N ⁻¹' quotientTruncatedCarrier N (2*Y)) :=
    (quotientTruncatedCarrier_isCompact N (2*Y)).isClosed.preimage (orbitProjection_continuous N)
  apply closure_minimal _ hclosed
  intro z hz
  apply quotientCutoff_support_subset N Y hY
  simpa only [Function.mem_support,quotientCutoff_projection] using hz

theorem globalCutoff_tsupport_compact_gamma_cover (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1≤Y) (z : UpperHalfPlane) (hz : z∈tsupport (globalCutoff Y)) :
    ∃ γ : CongruenceSubgroup.Gamma0 N,γ • z∈truncatedGammaCarrier N (2*Y) := by
  obtain ⟨w,hw,heq⟩ := globalCutoff_tsupport_saturation N Y hY hz
  have hrel : MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) UpperHalfPlane w z :=
    Quotient.exact heq
  obtain ⟨γ,hγ⟩ := (MulAction.orbitRel_apply).mp hrel
  exact ⟨γ,by rw [hγ];exact hw⟩

theorem globalCutoff_tsupport_compact_effective_cover (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1≤Y) (z : UpperHalfPlane) (hz : z∈tsupport (globalCutoff Y)) :
    ∃ q : effectiveGamma0 N,effectiveMatrixAction N q z∈truncatedGammaCarrier N (2*Y) := by
  obtain ⟨γ,hγ⟩ := globalCutoff_tsupport_compact_gamma_cover N Y hY z hz
  exact ⟨QuotientGroup.mk γ,by simpa only [effectiveMatrixAction_mk_gamma] using hγ⟩

end
end ImbalancedChen.Part3.ActualModularCutoffTSupportCover20261025a
