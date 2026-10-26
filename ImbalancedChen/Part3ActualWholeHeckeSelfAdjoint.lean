import ImbalancedChen.Part3ActualHeckeReversalL2
import ImbalancedChen.Part3ActualBoundedPhysicalHecke

-- SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-27.
-- Whole canonical Gamma0 quotient L2 selfadjointness of the original
-- physical prime Hecke operator. The arithmetic reversal pairing is
-- proved on the actual prime-level correspondence, rather than supplied
-- as a selfadjointness, spectral, or operator-identification hypothesis.

namespace ImbalancedChen.Part3.ActualWholeHeckeSelfAdjoint20261027
noncomputable section
open MeasureTheory
open Gamma0QuotientCellPushforward20261025a
open ActualHeckeForgetL220261026b ActualHeckeSecondL220261026b
open ActualBoundedPhysicalHecke20261026b
open ActualHeckeCorrespondencePairing20261026b
open ActualHeckeReversalL220261027

variable (N p : ℕ) [NeZero N] [NeZero (N*p)]
  (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

-- Both sides are the already constructed original physical operator.
-- The real inverse square-root normalization survives conjugation exactly.
theorem physicalHeckeOperator_inner_symm
    (U V : Lp ℂ 2 (carrierPushforward N)) :
    inner ℂ (physicalHeckeOperator N p hN hp hpN U) V =
      inner ℂ U (physicalHeckeOperator N p hN hp hpN V) := by
  have hscalar : star ((Real.sqrt (p : ℝ) : ℂ)⁻¹) =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ := by simp
  change inner ℂ ((Real.sqrt (p : ℝ) : ℂ)⁻¹ •
      ContinuousLinearMap.adjoint (firstPullbackCLM N p hp hpN)
        (secondPullbackCLM N p hN hp hpN U)) V =
    inner ℂ U ((Real.sqrt (p : ℝ) : ℂ)⁻¹ •
      ContinuousLinearMap.adjoint (firstPullbackCLM N p hp hpN)
        (secondPullbackCLM N p hN hp hpN V))
  rw [inner_smul_left, inner_smul_right, hscalar,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  apply congrArg (fun z : ℂ => (Real.sqrt (p : ℝ) : ℂ)⁻¹ * z)
  change inner ℂ (rawSecondPullbackLinear N p hN hp hpN U)
      (rawPullback N p hp hpN V) =
    inner ℂ (rawPullback N p hp hpN U)
      (rawSecondPullbackLinear N p hN hp hpN V)
  exact (rawPullback_inner_swap N p hp hpN hN U V).symm

-- No restriction, eigenfunction, or cusp-space premise is needed.
theorem physicalHeckeOperator_isSelfAdjoint :
    IsSelfAdjoint (physicalHeckeOperator N p hN hp hpN) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro U V
  exact physicalHeckeOperator_inner_symm N p hN hp hpN U V

theorem physicalHeckeOperator_adjoint_eq :
    ContinuousLinearMap.adjoint (physicalHeckeOperator N p hN hp hpN) =
      physicalHeckeOperator N p hN hp hpN :=
  (physicalHeckeOperator_isSelfAdjoint N p hN hp hpN).adjoint_eq

-- The native L2 vector represented by the literal physical branch trace
-- inherits the same identity through its already proved exact equality.
theorem physicalHeckeLp_inner_symm
    (U V : Lp ℂ 2 (carrierPushforward N)) :
    inner ℂ (physicalHeckeLp N p hN hp hpN U) V =
      inner ℂ U (physicalHeckeLp N p hN hp hpN V) := by
  simpa only [physicalHeckeOperator_eq_physicalHeckeLp] using
    physicalHeckeOperator_inner_symm N p hN hp hpN U V

end
end ImbalancedChen.Part3.ActualWholeHeckeSelfAdjoint20261027
