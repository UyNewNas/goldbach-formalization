import ImbalancedChen.P2OriginalI3ProjectionAttachmentDefects
import ImbalancedChen.ActualLowerNormalizedRhoError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The existing policy-uniform ACTUAL small-Rosser error theorem pays both
seed and computed-third losses at one epsilon and threshold. Since both
losses lie in the same [0,reserve], their signed difference costs only the
one reserve. Projection defects are separate and are not paid by this lemma.
-/
namespace ImbalancedChen.P2OriginalI3UniformActualAttachmentBudget
noncomputable section
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment
open P2OriginalI3ProjectionAttachmentDefects

theorem exists_same_precision_actual_I3_attachment_budget
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧
      epsilon^2 ≤ r ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ)^(nu*r) ≤ (cap : ℝ) →
      ∀ mesh : ℕ, ∀ D : ThirdStage mesh,
        let y := (N : ℝ)^(nu*epsilon^2)
        let z := (N : ℝ)^(nu*r)
        let L := (N : ℝ)^(nu*epsilon)
        let R := eta * singularSeries N / Real.log (N : ℝ)
        (0 ≤ attachmentLoss (seedRetain D N) N cap y z L ∧
          attachmentLoss (seedRetain D N) N cap y z L ≤ R) ∧
        (0 ≤ attachmentLoss (thirdRetain D N) N cap y z L ∧
          attachmentLoss (thirdRetain D N) N cap y z L ≤ R) ∧
        |attachmentLoss (seedRetain D N) N cap y z L -
          attachmentLoss (thirdRetain D N) N cap y z L| ≤ R := by
  obtain ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,N0,hN0,hbound⟩ :=
    exists_actualLowerSmallRoughRho_density_error_le_target_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,N0,hN0,?_⟩
  intro N hN hEven cap hcap mesh D
  let y := (N : ℝ)^(nu*epsilon^2)
  let z := (N : ℝ)^(nu*r)
  let L := (N : ℝ)^(nu*epsilon)
  let R := eta * singularSeries N / Real.log (N : ℝ)
  have ho : 0 ≤ attachmentLoss (seedRetain D N) N cap y z L ∧
      attachmentLoss (seedRetain D N) N cap y z L ≤ R := by
    simpa only [attachmentLoss,rawDensity,nativeDensity] using
      hbound N hN hEven cap hcap (seedRetain D N)
  have hn : 0 ≤ attachmentLoss (thirdRetain D N) N cap y z L ∧
      attachmentLoss (thirdRetain D N) N cap y z L ≤ R := by
    simpa only [attachmentLoss,rawDensity,nativeDensity] using
      hbound N hN hEven cap hcap (thirdRetain D N)
  refine ⟨ho,hn,?_⟩
  apply abs_le.mpr
  constructor <;> linarith [ho.1,ho.2,hn.1,hn.2]

end
end ImbalancedChen.P2OriginalI3UniformActualAttachmentBudget
