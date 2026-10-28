import ImbalancedChen.P2OriginalI3ActualSmallRosserAttachment
import ImbalancedChen.ActualLowerFirstExitDensityProjection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The full raw I3 coefficient belongs to the zero-lower-cutoff tree. Its
physical y-separated attachment is connected through two explicit
projection defects and two actual attachment losses, not a false equality
of the whole zero/y prime sources. These are finite exact identities.
-/
namespace ImbalancedChen.P2OriginalI3ProjectionAttachmentDefects
noncomputable section
open scoped Classical BigOperators
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment

def rawDensity (retain : List ℕ → Bool) (N cap : ℕ) (y z : ℝ) : ℝ :=
  reciprocalTotientDensity (fixedEvenRoughSupport retain N cap y z)
    (fixedEvenRoughCoefficient retain N cap y z)

def nativeDensity (retain : List ℕ → Bool) (N cap : ℕ) (y z L : ℝ) : ℝ :=
  physicalDensitySum (actualLowerSmallRoughModuli retain N cap y z)
    (actualLowerSmallRoughRho retain N cap y z L)

/-- Literal finite projection defect of the same complete policy. -/
def projectionDefect (retain : List ℕ → Bool) (N cap : ℕ) (y z : ℝ) : ℝ :=
  actualSmallEulerProduct N cap y * rawDensity retain N cap y z -
    rawDensity retain N cap 0 z

/-- Literal actual lower small-Rosser attachment loss. Its uniform bound
is supplied by ActualLowerNormalizedRhoError, not a new primitive. -/
def attachmentLoss (retain : List ℕ → Bool) (N cap : ℕ) (y z L : ℝ) : ℝ :=
  actualSmallEulerProduct N cap y * rawDensity retain N cap y z -
    nativeDensity retain N cap y z L

theorem projectionDefect_nonneg (retain : List ℕ → Bool)
    (N cap : ℕ) (y z : ℝ) (hyz : y ≤ z) :
    0 ≤ projectionDefect retain N cap y z := by
  exact sub_nonneg.mpr (fixedEvenRoughDensity_presieveProjection retain N cap y z hyz)

private theorem pad_actual_lower_density (retain : List ℕ → Bool)
    (N cap : ℕ) (y z L : ℝ) (Q : Finset ℕ)
    (hsub : actualLowerSmallRoughModuli retain N cap y z ⊆ Q) :
    nativeDensity retain N cap y z L =
      ∑ q ∈ Q, actualLowerSmallRoughRho retain N cap y z L q / (Nat.totient q : ℝ) := by
  unfold nativeDensity physicalDensitySum
  apply Finset.sum_subset hsub
  intro q hq hnot
  have hz := smallRoughRho_eq_zero_of_not_mem
    (actualSmallRosserSupport N cap y) (fixedEvenRoughSupport retain N cap y z)
    (fixedEvenRoughCoefficient retain N cap y z)
    (actualSmallRosserPlus N cap y L) (actualSmallRosserMinus N cap y L) hnot
  change actualLowerSmallRoughRho retain N cap y z L q / _ = 0
  rw [show actualLowerSmallRoughRho retain N cap y z L q = 0 from hz]
  simp

/-- The actual common physical density is exactly new minus old, without
an extra multiplicity from the two supports. -/
theorem attached_density_eq_native_difference {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (y z L : ℝ) :
    physicalDensitySum (attachedSupport D N cap y z) (attachedRho D N cap y z L) =
      nativeDensity (thirdRetain D N) N cap y z L -
        nativeDensity (seedRetain D N) N cap y z L := by
  have hn : actualLowerSmallRoughModuli (thirdRetain D N) N cap y z ⊆
      attachedSupport D N cap y z := by
    rw [attachedSupport_eq_actual_union]
    exact Finset.subset_union_left
  have ho : actualLowerSmallRoughModuli (seedRetain D N) N cap y z ⊆
      attachedSupport D N cap y z := by
    rw [attachedSupport_eq_actual_union]
    exact Finset.subset_union_right
  rw [pad_actual_lower_density _ _ _ _ _ _ _ hn,
    pad_actual_lower_density _ _ _ _ _ _ _ ho, ← Finset.sum_sub_distrib]
  unfold physicalDensitySum attachedRho
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- No subtraction of one-sided projection inequalities is performed.
Both actual projection defects and both attachment losses remain visible. -/
theorem attached_density_eq_full_I3_with_exact_defects {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ) :
    physicalDensitySum (attachedSupport D N cap y z) (attachedRho D N cap y z L) =
      (rawDensity (thirdRetain D N) N cap 0 z -
        rawDensity (seedRetain D N) N cap 0 z) +
      projectionDefect (thirdRetain D N) N cap y z -
        projectionDefect (seedRetain D N) N cap y z -
      attachmentLoss (thirdRetain D N) N cap y z L +
        attachmentLoss (seedRetain D N) N cap y z L := by
  rw [attached_density_eq_native_difference]
  unfold projectionDefect attachmentLoss
  ring

/-- The raw full I3 term is the actual same-policy rank-three tagged
frontier established from Trace, rather than an unrelated density premise. -/
theorem full_raw_I3_eq_actual_tagged_frontier {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) :
    rawDensity (thirdRetain D N) N cap 0 z -
      rawDensity (seedRetain D N) N cap 0 z =
      ((D.taggedFrontier N cap z (fun p => 1 / ((p : ℝ)-1))).map
        (D.frontierTerm N (fun p => 1 / ((p : ℝ)-1)))).sum := by
  unfold rawDensity
  rw [← evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity
      (thirdRetain D N) N cap 0 z,
    ← evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity
      (seedRetain D N) N cap 0 z]
  exact D.actual_third_sub_eq_tagged_frontier N cap z _

/-- All carrier and attachment seams remain explicit in the same equation
which will consume the still-required ordinary-plus quotient dictionary. -/
theorem attached_density_eq_actual_frontier_and_defects {mesh : ℕ}
    (D : ThirdStage mesh) (N cap : ℕ) (y z L : ℝ) :
    physicalDensitySum (attachedSupport D N cap y z) (attachedRho D N cap y z L) =
      ((D.taggedFrontier N cap z (fun p => 1 / ((p : ℝ)-1))).map
        (D.frontierTerm N (fun p => 1 / ((p : ℝ)-1)))).sum +
      projectionDefect (thirdRetain D N) N cap y z -
        projectionDefect (seedRetain D N) N cap y z -
      attachmentLoss (thirdRetain D N) N cap y z L +
        attachmentLoss (seedRetain D N) N cap y z L := by
  rw [attached_density_eq_full_I3_with_exact_defects,
    full_raw_I3_eq_actual_tagged_frontier]

end
end ImbalancedChen.P2OriginalI3ProjectionAttachmentDefects
