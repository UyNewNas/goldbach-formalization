import ImbalancedChen.P4AUpperTaggedBetaAttachment
import ImbalancedChen.P5OriginalCommonRefinedConstructor
import ImbalancedChen.P4AHistoricalPhysicalSavingsReserve

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

Concrete binding to the existing common constructor, with its unresolved
OriginalData banks and held policy8 semantics left visible. This does NOT
identify that constructor with the complete original adopted87 policy.

The historical tag records the actual old3/common3/policy4/policy5/policy6
decisions on each of the first nine canonical ancestors. It is fixed before
tau and retains each displayed historical decision in every compiled cell.
The raw policy and both coefficient functions use the same OriginalData.
No arbitrary CapPlan, raw-density bound, or error-budget field is introduced.

Quantitative original-policy wall/cap classification, smallness of the
displayed crossing mass, and support inflation below 1/1000 remain OPEN.
-/

namespace ImbalancedChen.P4ACommonPolicyTaggedCompiler

noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor

/-- Ascending primeFactorsList is the newest-first first-exit history. -/
def canonicalHistory (d : ℕ) : List ℕ := d.primeFactorsList

def stageTag (data : OriginalData) (N : ℕ) (pre : List ℕ) : List Bool :=
  [old3 data (N : ℝ) (evenListLength pre) pre,
   common3 data (N : ℝ) (evenListLength pre) pre,
   policy4 data (N : ℝ) (evenListLength pre) pre,
   policy5 data (N : ℝ) (evenListLength pre) pre,
   policy6 data (N : ℝ) (evenListLength pre) pre]

/-- Fixed coarse-history data; fine atom width/count is not an argument. -/
def historicalTag (data : OriginalData) (N : ℕ) (d : ℕ) : List Bool :=
  (List.range 9).flatMap (fun k => stageTag data N (rosserAncestor k (canonicalHistory d)))

/-- This is precisely the held constructor, not a new full87 identification. -/
def heldRetain (data : OriginalData) (N : ℕ) : List ℕ → Bool :=
  policy8 data (N : ℝ) false

def compiledCoefficient (data : OriginalData) (N cap : ℕ) (w z tau : ℝ) : ℕ → ℝ :=
  P4AUpperTaggedParityCompiler.coefficient (heldRetain data N) (historicalTag data N)
    N cap w z tau

def compiledRho (data : OriginalData) (N cap : ℕ) (w z tau L : ℝ) : ℕ → ℝ :=
  P4AUpperTaggedBetaAttachment.rho (heldRetain data N) (historicalTag data N)
    N cap w z tau L

def changedMass (data : OriginalData) (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  P4AUpperTaggedParityCompiler.changedMass (heldRetain data N) (historicalTag data N)
    N cap w z tau

def crossingMass (data : OriginalData) (N cap : ℕ) (w z tau : ℝ) : ℝ :=
  P4AUpperTaggedParityCompiler.crossingMass (heldRetain data N) (historicalTag data N)
    N cap w z tau

theorem compiledCoefficient_dominates_held_raw (data : OriginalData)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) :
    fixedRoughCoefficient (policy8 data (N : ℝ) false) N cap w z d ≤
      compiledCoefficient data N cap w z tau d :=
  P4AUpperTaggedParityCompiler.raw_le_coefficient (heldRetain data N)
    (historicalTag data N) N cap w z tau d

theorem historicalTag_preserved (data : OriginalData) (N cap : ℕ) (w z tau : ℝ)
    {d e : ℕ}
    (he : e ∈ P4AUpperTaggedParityCompiler.cell (historicalTag data N) N cap w z tau d) :
    historicalTag data N e = historicalTag data N d :=
  P4AUpperTaggedParityCompiler.cell_frozen_tag (historicalTag data N) N cap w z tau he

theorem coefficient_error_eq_actual_changedMass (data : OriginalData)
    (N cap : ℕ) (w z tau : ℝ) :
    reciprocalTotientDensity (P4AUpperTaggedParityCompiler.universe N cap w z)
      (fun d => |compiledCoefficient data N cap w z tau d -
        fixedRoughCoefficient (policy8 data (N : ℝ) false) N cap w z d|) =
          changedMass data N cap w z tau :=
  P4AUpperTaggedParityCompiler.coefficient_error_eq_changedMass
    (heldRetain data N) (historicalTag data N) N cap w z tau

theorem actual_changedMass_le_crossingMass (data : OriginalData)
    (N cap : ℕ) (w z tau : ℝ) :
    changedMass data N cap w z tau ≤ crossingMass data N cap w z tau :=
  P4AUpperTaggedParityCompiler.changedMass_le_crossingMass
    (heldRetain data N) (historicalTag data N) N cap w z tau

theorem compiledRho_majorant (data : OriginalData) (N cap : ℕ) (w z tau L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (P4AUpperTaggedBetaAttachment.support N cap w z)
        (compiledRho data N cap w z tau L) n.natAbs :=
  P4AUpperTaggedBetaAttachment.rho_majorant (heldRetain data N) (historicalTag data N)
    N cap w z tau L hL hwL hwz hzcap n

/-- Exact old physical function after zero extension to the compiler carrier. -/
theorem held_raw_attachment_eq_common_rho (data : OriginalData) (N cap : ℕ)
    (w z L : ℝ) :
    smallRoughRho (actualSmallRosserSupport N cap w)
      (P4AUpperTaggedParityCompiler.universe N cap w z)
      (fixedRoughCoefficient (policy8 data (N : ℝ) false) N cap w z)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) =
        P5OriginalCommonRefinedConstructor.rho data N cap w z L :=
  P4AUpperTaggedBetaAttachment.raw_attachment_eq_actual (heldRetain data N) N cap w z L

/-- Keep the genuine continuation correction with its exact favorable sign.
No assertion that the correction itself tends to zero is needed for an upper projection. -/
theorem held_physical_minus_full_raw (data : OriginalData) (N cap : ℕ)
    (w z L : ℝ) (hwz : w ≤ z) :
    p4aReservePhysicalDensity (heldRetain data N) N cap w z L -
      p4aReserveRawDensity (heldRetain data N) N cap 0 z =
        (p4aReservePhysicalDensity (heldRetain data N) N cap w z L -
          actualSmallEulerProduct N cap w *
            p4aReserveRawDensity (heldRetain data N) N cap w z) -
              p4aActualPresieveCorrection (heldRetain data N) N cap w z := by
  rw [p4a_fullRaw_eq_euler_presieved_add_correction (heldRetain data N) N cap w z hwz]
  ring

/-- A finite symbolic counterexample to treating arbitrary continuation corrections
as zero: a policy stopping at the first odd node has polynomial exactly one. -/
theorem stopFirstOdd_polynomial {α : Type*} (h : α → ℝ) (carrier : List α) :
    oddFirstExitRetainedPolynomial (fun _ => false) h carrier = 1 := by
  unfold oddFirstExitRetainedPolynomial
  induction carrier with
  | nil => rfl
  | cons p ps ih =>
      simpa only [firstExitRetainedPolynomial, oddFirstExitPolicy, Bool.not_true,
        Bool.false_or, Bool.false_eq_true, if_false, add_zero] using ih

theorem stopFirstOdd_rawDensity (N cap : ℕ) (w z : ℝ) :
    p4aReserveRawDensity (fun _ => false) N cap w z = 1 := by
  unfold p4aReserveRawDensity
  rw [← oddFirstExitRetainedPolynomial_eq_fixedRoughDensity]
  exact stopFirstOdd_polynomial _ _

/-- Sign alone cannot make the policy-independent correction disappear. -/
theorem stopFirstOdd_correction (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    p4aActualPresieveCorrection (fun _ => false) N cap w z =
      1 - actualSmallEulerProduct N cap w := by
  have h := p4a_fullRaw_eq_euler_presieved_add_correction (fun _ => false) N cap w z hwz
  rw [stopFirstOdd_rawDensity, stopFirstOdd_rawDensity, mul_one] at h
  linarith only [h]

end
end ImbalancedChen.P4ACommonPolicyTaggedCompiler
