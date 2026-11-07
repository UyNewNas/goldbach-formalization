import ImbalancedChen.Part3OriginalSharedResidualBoundary
import ImbalancedChen.Part3SharedFirstFactorEnergyNonzeroReduction

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 4.

The real ORIGINAL outside betaL2*gamma1L2 is preserved. Its public divisor
moment bound is applied only after the actual shared residual is bounded.
No new Cauchy or canonical phase identity is asserted. Primitive zero
covariance and U/V are NOT discarded; the next family transfer consumes
their existing proved uniform payment through EnergyNonzeroReduction.
-/

namespace ImbalancedChen.Part3.OriginalSharedWeightedBoundary20261026b
noncomputable section
open Classical OriginalSharedResidualBoundary20261026b
open scoped BigOperators

def originalOutside (d : MediumAtom) : ℝ :=
  (∑ n ∈ d.betaCarrier, ‖d.beta n‖^2) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖^2)

def originalBetaLogCost (B : ℕ) (d : MediumAtom) : ℝ :=
  (1+Real.log (2*d.V))^((2^B)^2-1)

theorem original_weighted_sharedResidual_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
        originalOutside d * ‖sharedResidual d‖ ≤
          C*d.U^2*d.Q1^2*d.physicalFactorCap^4*originalBetaLogCost B d := by
  obtain ⟨C,hC,hresidual⟩ := original_sharedResidual_boundary
  refine ⟨4*C,by positivity,fun B sigma kappa c0 d hd => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hlog : 0 ≤ 1+Real.log (2*d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2*d.V by linarith [hd.2.1])]
  have hout := d.sharedFirstFactor_outside_le hd
  have hres := hresidual B sigma kappa c0 d hd
  change originalOutside d ≤ 4*d.V*d.Q1*originalBetaLogCost B d at hout
  calc
    _ ≤ (4*d.V*d.Q1*originalBetaLogCost B d) *
        (C*d.Q1*d.U^2*d.physicalFactorCap^4/d.V) :=
      mul_le_mul hout hres (norm_nonneg _) (by unfold originalBetaLogCost; positivity)
    _ = (4*C)*d.U^2*d.Q1^2*d.physicalFactorCap^4*originalBetaLogCost B d := by
      field_simp [hV.ne']
      ring

end
end ImbalancedChen.Part3.OriginalSharedWeightedBoundary20261026b
