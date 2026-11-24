import ImbalancedChen.P5OriginalEighthNavigationMap
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The verified H3 cell00 navigation record has an exact rational strict
center. Its 99 affine constraints omit two constant identities, including
the old mask9 winner plane. Thus the 63 old-plane rows consist of 62
strict rows and one equality at every point. The theorem below checks
those 62 rows directly from the transcribed center and the literal
Phase10 mask assignment. It does not establish the causal third/sixth
ancestor, density, or complete physical row feasibility.
-/

namespace ImbalancedChen.P5OriginalH3Cell00StrictOldPlanes

noncomputable section
open P5OriginalAdoptedEighthPhysicalMasks
open P5OriginalEighthAffineRowRecipe
open P5OriginalEighthNavigationMap
open VariableEnvelope

/-- Published global index 58 is first-failure H3 cell00. -/
def slot : Cell := ⟨58, by omega⟩
def winnerMask : OldMask := {0, 3}

/-- Exact `strict_center` coordinates in the verified H3 cell00
navigation JSON, in physical t1,...,t8 order. -/
def strictCenter : Point := ![
  1061930909 / 7812500000,
  111291629207 / 1000000000000,
  4241932747 / 40000000000,
  460093481 / 8000000000,
  14190755429 / 500000000000,
  3454105931 / 125000000000,
  26884184039 / 1000000000000,
  26134853963 / 1000000000000
]

/-- The old mask9 A-plane is literally the sixth comparison R6,
independently of the chosen point. It cannot have strict slack. -/
theorem winner_plane_identity (t : Point) :
    (if oldMaskCode winnerMask ∈ firstFailureH3LeftCodes 0 then
        A (oldSubsetSum t winnerMask)
      else C (oldSubsetSum t winnerMask)) = oldComparison slot t := by
  norm_num [winnerMask, slot, oldMaskCode, firstFailureH3LeftCodes,
    oldSubsetSum, oldComparison, e, A, C] <;> ring

/-- All 62 proper old-plane rows have exact positive slack at the
source's strict rational center. The winning identity is excluded. -/
theorem strict_center_proper_old_planes :
    ∀ I ∈ oldMasks, I ≠ winnerMask →
      (if oldMaskCode I ∈ firstFailureH3LeftCodes 0 then
          A (oldSubsetSum strictCenter I)
        else C (oldSubsetSum strictCenter I)) <
        oldComparison slot strictCenter := by
  intro I hI hproper
  fin_cases I <;>
    norm_num [oldMasks, winnerMask, slot, oldMaskCode,
      firstFailureH3LeftCodes, oldSubsetSum, oldComparison,
      strictCenter, e, A, C] at *

theorem strict_center_all_old_planes :
    oldPlaneRows slot (firstFailureH3LeftCodes 0) strictCenter := by
  intro I hI
  by_cases h : I = winnerMask
  · subst I
    exact le_of_eq (winner_plane_identity strictCenter)
  · exact le_of_lt (strict_center_proper_old_planes I hI h)

/-- This is why asking for strict slack in all 63 rows is impossible.
The source's two constant identities are intentionally outside its 99
proper affine constraints. -/
theorem no_all_strict_old_planes (t : Point) :
    ¬ ∀ I ∈ oldMasks,
      (if oldMaskCode I ∈ firstFailureH3LeftCodes 0 then
          A (oldSubsetSum t I)
        else C (oldSubsetSum t I)) < oldComparison slot t := by
  intro h
  have hw : winnerMask ∈ oldMasks := by decide
  have hs := h winnerMask hw
  rw [winner_plane_identity t] at hs
  exact (lt_irrefl _ hs)

end
end ImbalancedChen.P5OriginalH3Cell00StrictOldPlanes