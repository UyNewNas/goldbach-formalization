import ImbalancedChen.Part3GammaActualClosedGradientRealization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original finite smooth EnergyCore is a genuine graph core of the
native closed gradient. Both physical values and carrier gradients are
approximated simultaneously by the SAME original core vectors. The
closure is proved from the original energy completion, rather than
assumed as a weak-gradient density or Sobolev identification premise.
-/

namespace ImbalancedChen.Part3.GammaActualClosedGradientCore20261026b
noncomputable section
open Set
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0CarrierGradientHilbertMap20261026b GammaActualClosedGradientRealization20261026b

def originalCoreGradientPairs (N : ℕ) [NeZero N] :
    Set (QuotientL2 N × CarrierGradientL2 N) :=
  Set.range (fun u : EnergyCore N => (physicalCore N u, carrierCoreGradient N u))

theorem gradientGraphEmbedding_core (N : ℕ) [NeZero N] (u : EnergyCore N) :
    gradientGraphEmbedding N (coreEmbedding N u) =
      (physicalCore N u, carrierCoreGradient N u) := by
  apply Prod.ext
  · exact physicalProjection_core N u
  · exact completedCarrierGradient_core N u

/-- The genuine original smooth graph core, including simultaneous
value/gradient approximation. Closed range supplies the reverse inclusion. -/
theorem actualClosedGradient_graph_core (N : ℕ) [NeZero N] :
    closure (originalCoreGradientPairs N) =
      ((actualClosedGradient N).graph : Set (QuotientL2 N × CarrierGradientL2 N)) := by
  rw [actualClosedGradient_graph_eq_range]
  apply Subset.antisymm
  · apply closure_minimal
    · rintro p ⟨u,rfl⟩
      exact ⟨coreEmbedding N u, gradientGraphEmbedding_core N u⟩
    · exact gradientGraphEmbedding_closed_range N
  · rintro p ⟨e,rfl⟩
    have hclosed : IsClosed {d : EnergyCompletion N |
        gradientGraphEmbedding N d ∈ closure (originalCoreGradientPairs N)} :=
      isClosed_closure.preimage (gradientGraphEmbedding N).continuous
    have hcore : Set.range (coreEmbedding N) ⊆
        {d : EnergyCompletion N |
          gradientGraphEmbedding N d ∈ closure (originalCoreGradientPairs N)} := by
      rintro d ⟨u,rfl⟩
      rw [gradientGraphEmbedding_core]
      exact subset_closure ⟨u,rfl⟩
    exact closure_minimal hcore hclosed ((coreEmbedding_denseRange N) e)

end
end ImbalancedChen.Part3.GammaActualClosedGradientCore20261026b
