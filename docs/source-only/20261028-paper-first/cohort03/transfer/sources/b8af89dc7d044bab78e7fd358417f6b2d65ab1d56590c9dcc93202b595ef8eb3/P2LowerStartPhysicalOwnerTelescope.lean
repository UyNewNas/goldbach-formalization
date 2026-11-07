import ImbalancedChen.P2LowerCapPlanIntegerRetention
import ImbalancedChen.FixedEvenRoughCoefficients

/-!
# Signed finite owner telescope for the two ordinary lower starts

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT (2026-10-28).

The owner is an actual finite first-exit tree difference. At a changed
admission it charges the entire selected continuation exactly once; at a
shared admission it recurses into that common branch. The skip branch is
always retained. Thus the signed owner equals the difference of the two
genuine reciprocal-totient densities of the selected physical policies.

Three successive policy generations telescope on the same finite prime
carrier. The last theorem applies this separately at the literal L1 and L2
start cutoffs `N^(417/5000)` and `N^(19/125)`, with their original weights
three and one. It does not assert that these owner masses equal the numerical
I3/I4/I5 integrals; that physical-to-continuous approximation and the
selected finite CapPlan bindings remain distinct upstream obligations.
-/

namespace ImbalancedChen.P2LowerStartPhysicalOwnerTelescope

noncomputable section
open scoped BigOperators
open ImbalancedChen.P2LowerCapPlanIntegerRetention
open ImbalancedChen.P2PhysicalIncomingPrefixCells

/-- Exact signed charge on the first branch where two finite retention
policies differ. No absolute value or monotonicity is used. A differing
branch stops recursion there, so none of its descendants is charged twice. -/
def signedFirstDifferentOwner {α : Type*}
    (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => 0
  | p :: ps =>
      signedFirstDifferentOwner oldPolicy newPolicy h pre positive mass ps +
        if oldPolicy (!positive) (p :: pre) =
            newPolicy (!positive) (p :: pre) then
          if newPolicy (!positive) (p :: pre) = true then
            signedFirstDifferentOwner oldPolicy newPolicy h
              (p :: pre) (!positive) (mass * h p) ps
          else 0
        else
          (if newPolicy (!positive) (p :: pre) = true then
            firstExitRetainedPolynomial newPolicy h
              (p :: pre) (!positive) (mass * h p) ps else 0) -
          (if oldPolicy (!positive) (p :: pre) = true then
            firstExitRetainedPolynomial oldPolicy h
              (p :: pre) (!positive) (mass * h p) ps else 0)

/-- The recursive owner is the exact difference of the two signed trees.
The four Boolean cases distinguish common rejection, common admission and
the two orientations of a first changed admission. -/
theorem signedFirstDifferentOwner_eq_polynomial_sub {α : Type*}
    (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    signedFirstDifferentOwner oldPolicy newPolicy h pre positive mass remaining =
      firstExitRetainedPolynomial newPolicy h pre positive mass remaining -
        firstExitRetainedPolynomial oldPolicy h pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [signedFirstDifferentOwner, firstExitRetainedPolynomial]
  | cons p ps ih =>
      have hskip := ih pre positive mass
      have hselect := ih (p :: pre) (!positive) (mass * h p)
      cases ho : oldPolicy (!positive) (p :: pre) <;>
        cases hn : newPolicy (!positive) (p :: pre) <;>
        simp [signedFirstDifferentOwner, firstExitRetainedPolynomial,
          ho, hn, hskip, hselect] <;> ring

/-- Owner terms for two actual integer cap plans, on the target-deleted
prime carrier and the original weight `1/(p-1)`. The plans are evaluated on
the physical chronological word by `P2LowerCapPlanIntegerRetention.retainEven`. -/
def physicalStartOwner {depth m : ℕ}
    (oldPlan newPlan : CapPlan depth m) (a b seedCap : ℝ)
    (N cap : ℕ) (z : ℝ) : ℝ :=
  signedFirstDifferentOwner
    (evenFirstExitPolicy (retainEven oldPlan a b seedCap N))
    (evenFirstExitPolicy (retainEven newPlan a b seedCap N))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap 0 z)

/-- The owner is identified with the two actual physical raw densities,
using the established exact even-tree divisor dictionary. This is not a
numerical I3/I4/I5 coefficient declaration. -/
theorem physicalStartOwner_eq_rawDensity_sub {depth m : ℕ}
    (oldPlan newPlan : CapPlan depth m) (a b seedCap : ℝ)
    (N cap : ℕ) (z : ℝ) :
    physicalStartOwner oldPlan newPlan a b seedCap N cap z =
      reciprocalTotientDensity
        (fixedEvenRoughSupport (retainEven newPlan a b seedCap N) N cap 0 z)
        (fixedEvenRoughCoefficient (retainEven newPlan a b seedCap N) N cap 0 z) -
      reciprocalTotientDensity
        (fixedEvenRoughSupport (retainEven oldPlan a b seedCap N) N cap 0 z)
        (fixedEvenRoughCoefficient (retainEven oldPlan a b seedCap N) N cap 0 z) := by
  have h := signedFirstDifferentOwner_eq_polynomial_sub
    (evenFirstExitPolicy (retainEven oldPlan a b seedCap N))
    (evenFirstExitPolicy (retainEven newPlan a b seedCap N))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) []
    (roughPrimeUniverse N cap 0 z) true 1
  change physicalStartOwner oldPlan newPlan a b seedCap N cap z =
    evenFirstExitRetainedPolynomial (retainEven newPlan a b seedCap N)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) -
    evenFirstExitRetainedPolynomial (retainEven oldPlan a b seedCap N)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) at h
  rw [evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity,
    evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity] at h
  exact h

/-- At one physical start, the intermediate raw densities cancel. Each
summand remains a first-difference owner on the same finite carrier. -/
theorem physicalStartOwner_three_step_telescope {depth m : ℕ}
    (P0 P3 P4 P5 : CapPlan depth m) (a b seedCap : ℝ)
    (N cap : ℕ) (z : ℝ) :
    physicalStartOwner P0 P3 a b seedCap N cap z +
      physicalStartOwner P3 P4 a b seedCap N cap z +
        physicalStartOwner P4 P5 a b seedCap N cap z =
      reciprocalTotientDensity
        (fixedEvenRoughSupport (retainEven P5 a b seedCap N) N cap 0 z)
        (fixedEvenRoughCoefficient (retainEven P5 a b seedCap N) N cap 0 z) -
      reciprocalTotientDensity
        (fixedEvenRoughSupport (retainEven P0 a b seedCap N) N cap 0 z)
        (fixedEvenRoughCoefficient (retainEven P0 a b seedCap N) N cap 0 z) := by
  rw [physicalStartOwner_eq_rawDensity_sub,
    physicalStartOwner_eq_rawDensity_sub,
    physicalStartOwner_eq_rawDensity_sub]
  ring

/-- The literal three-to-one L1/L2 weighting of the two ordinary starts.
The same four successive plans are used at both cutoffs, so an I5 owner
cannot be appended from an unrelated fourth-stage policy. -/
theorem weighted_two_start_physical_owner_telescope {depth m : ℕ}
    (P0 P3 P4 P5 : CapPlan depth m) (a b seedCap : ℝ)
    (N cap : ℕ) :
    3 * (physicalStartOwner P0 P3 a b seedCap N cap
          ((N : ℝ) ^ (417 / 5000 : ℝ)) +
        physicalStartOwner P3 P4 a b seedCap N cap
          ((N : ℝ) ^ (417 / 5000 : ℝ)) +
        physicalStartOwner P4 P5 a b seedCap N cap
          ((N : ℝ) ^ (417 / 5000 : ℝ))) +
      (physicalStartOwner P0 P3 a b seedCap N cap
          ((N : ℝ) ^ (19 / 125 : ℝ)) +
        physicalStartOwner P3 P4 a b seedCap N cap
          ((N : ℝ) ^ (19 / 125 : ℝ)) +
        physicalStartOwner P4 P5 a b seedCap N cap
          ((N : ℝ) ^ (19 / 125 : ℝ))) =
      3 * (reciprocalTotientDensity
          (fixedEvenRoughSupport (retainEven P5 a b seedCap N) N cap 0
            ((N : ℝ) ^ (417 / 5000 : ℝ)))
          (fixedEvenRoughCoefficient (retainEven P5 a b seedCap N) N cap 0
            ((N : ℝ) ^ (417 / 5000 : ℝ))) -
        reciprocalTotientDensity
          (fixedEvenRoughSupport (retainEven P0 a b seedCap N) N cap 0
            ((N : ℝ) ^ (417 / 5000 : ℝ)))
          (fixedEvenRoughCoefficient (retainEven P0 a b seedCap N) N cap 0
            ((N : ℝ) ^ (417 / 5000 : ℝ)))) +
      (reciprocalTotientDensity
          (fixedEvenRoughSupport (retainEven P5 a b seedCap N) N cap 0
            ((N : ℝ) ^ (19 / 125 : ℝ)))
          (fixedEvenRoughCoefficient (retainEven P5 a b seedCap N) N cap 0
            ((N : ℝ) ^ (19 / 125 : ℝ))) -
        reciprocalTotientDensity
          (fixedEvenRoughSupport (retainEven P0 a b seedCap N) N cap 0
            ((N : ℝ) ^ (19 / 125 : ℝ)))
          (fixedEvenRoughCoefficient (retainEven P0 a b seedCap N) N cap 0
            ((N : ℝ) ^ (19 / 125 : ℝ)))) := by
  rw [physicalStartOwner_three_step_telescope,
    physicalStartOwner_three_step_telescope]

end

end ImbalancedChen.P2LowerStartPhysicalOwnerTelescope
