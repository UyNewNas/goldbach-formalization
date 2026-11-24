import ImbalancedChen.P5OriginalEighthPhysicalRowBag
import ImbalancedChen.P5OriginalAboveMuThirdRaisedAdmission
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The eighth family is applied to the corrected combined above-mu second/third
parent, not the superseded Phase5 global-lower policy. Both later splices
retain this parent through rank six. Consequently its original firstStop
decision and first new test after a selected rank-three node are inherited.
The eighth signed coefficient below is the actual small/rough product rho of
that same family policy. The chosen eighth guard supplies the physical square
rows and level; all 63 assigned old planes require the explicit source-cell
premise. No causal common-parent or density conclusion follows from a row map.
-/

namespace ImbalancedChen.P5OriginalPhaseBPhysicalBinding

noncomputable section
open scoped Classical
open P5OriginalAdoptedEighthPhysicalMasks
open P5OriginalEighthAffineRowRecipe
open P5OriginalEighthNavigationMap
open P5OriginalEighthPhysicalRowBag
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

/-- The corrected third fallback is the actual old parent of the rank-six
and rank-eight updates. The physical sixth level remains a caller input. -/
def physicalPolicy (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) : Bool → List ℕ → Bool :=
  familyPolicy N lambda3 lambda6 (finalPolicy e chi m omega N)

/-- The same fixed signed small/rough coefficient used at integer tests. -/
def physicalRho (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z L : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (q : ℕ) : ℝ :=
  actualSmallRoughRho
    ((physicalPolicy e chi m omega (N : ℝ) lambda3 lambda6) false)
    N cap w z L q

/-- At the paper's small/rough scales this is definitionally the one
attached upper coefficient, with the corrected fallback and eighth update
as its single retained policy. -/
theorem physical_rho_eq_attached
    (e chi : ℝ) (m : ℕ) (omega nu r epsilon : ℝ)
    (cap : ℕ → ℕ) (N q : ℕ) (lambda3 lambda6 : List ℕ → ℝ) :
    physicalRho e chi m omega N (cap N)
      ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
      ((N : ℝ) ^ (nu * epsilon)) lambda3 lambda6 q =
    attachedUpperCoefficient nu r epsilon
      (fun M => (physicalPolicy e chi m omega (M : ℝ) lambda3 lambda6) false)
      cap N q := rfl
/-- Both later splices preserve every decision through the sixth selected
rank, including the original third fallback and firstStop admission. -/
theorem through_sixth_eq_corrected_parent
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (positive : Bool)
    (pre : List ℕ) (hlen : pre.length ≤ 6) :
    physicalPolicy e chi m omega N lambda3 lambda6 positive pre =
      finalPolicy e chi m omega N positive pre := by
  have h8 : pre.length ≤ 8 := by omega
  simp [physicalPolicy, familyPolicy, parentPolicy,
    P4AOriginalEighthParentPhysicalLedger.parentPolicy,
    P4AActualSixthFrozenEighthAdmission.sixthPolicy,
    firstExitDepthSplicePolicy, hlen, h8]

theorem physical_firstStop_iff
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (p : ℕ) :
    physicalPolicy e chi m omega N lambda3 lambda6 false [p] = true ↔
      ordinaryRosserPrefixAdmissible false
        (N ^ HistoricalThirdCoarse.initial e) [p] ∧
      HistoricalThirdCoarse.firstStop e m N [p] := by
  rw [through_sixth_eq_corrected_parent e chi m omega N
    lambda3 lambda6 false [p] (by simp)]
  exact final_first_test e chi m omega N p

/-- The next odd full-rank test after an actual selected-pair third node
is at rank five and inherits the corrected global-upper policy. Its
ordinary residual is lower, with the physical level N^v(y+z). -/
theorem physical_third_first_descendant_test
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (hlen : pre.length = 5) (hguard : thirdGuard N pre) :
    physicalPolicy e chi m omega N lambda3 lambda6 false pre =
      decide (ordinaryRosserPrefixAdmissible false
        (thirdQ N (rosserAncestor 3 pre)) pre) := by
  rw [through_sixth_eq_corrected_parent e chi m omega N
    lambda3 lambda6 false pre (by omega)]
  exact third_hit_odd_test e chi m omega N pre (by omega) hguard

/-- Every published eighth slot has a literal selected mask and all its
tagged common rows. The old-plane premise is not inferred from the guard. -/
theorem chosen_actual_physical_rows
    (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (hguard : adoptedGuard N lambda3 lambda6 pre) :
    let i := Classical.choose hguard
    let t := primeHistoryLogCoordinates N 8 pre
    (adoptedOldPlanes i).isSome ∧
      raisedExponent N lambda3 lambda6 pre = newCap i t ∧
      fullSquareRows i t ∧ selectedComplementRows i t ∧
      (physicalRowBag i).card =
        (if i.val < 30 then 77 else if i.val = 43 then 75 else 76) := by
  dsimp
  refine ⟨adopted_old_planes_all _, ?_, ?_, ?_, every_slot_row_card _⟩
  · exact (chosen_guard_square_rows N lambda3 lambda6 pre hguard).1
  · exact (chosen_guard_square_rows N lambda3 lambda6 pre hguard).2.1
  · exact (chosen_guard_square_rows N lambda3 lambda6 pre hguard).2.2

/-- If the source-cell old-plane inequalities hold at the selected
physical history, they combine with the guard's eighth square rows to
give the entire 63+8+complement row bag. -/
theorem chosen_actual_row_bag_of_old_planes
    (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (hguard : adoptedGuard N lambda3 lambda6 pre)
    (hplanes :
      ∀ leftCodes, adoptedOldPlanes (Classical.choose hguard) = some leftCodes →
        oldPlaneRows (Classical.choose hguard) leftCodes
          (primeHistoryLogCoordinates N 8 pre)) :
    ∃ leftCodes,
      adoptedOldPlanes (Classical.choose hguard) = some leftCodes ∧
      ∀ r ∈ physicalRowBag (Classical.choose hguard),
        rowHolds (Classical.choose hguard) leftCodes
          (primeHistoryLogCoordinates N 8 pre) r := by
  let i := Classical.choose hguard
  let t := primeHistoryLogCoordinates N 8 pre
  have hp := adopted_old_planes_all i
  cases hleft : adoptedOldPlanes i with
  | none => simp [hleft] at hp
  | some leftCodes =>
      have hs := chosen_guard_square_rows N lambda3 lambda6 pre hguard
      refine ⟨leftCodes, hleft, (physical_row_bag_holds_iff i leftCodes t).2 ?_⟩
      exact ⟨hplanes leftCodes hleft, hs.2.1, hs.2.2⟩

/-- First exact vertex in the verified H3 cell00 witness, global slot 58.
The witness lists the eight physical coordinates in this order. -/
def h3Cell00Vertex : Point := ![
  118140461 / 884000000,
  1534379 / 13600000,
  93296767 / 884000000,
  12421847 / 221000000,
  12421847 / 442000000,
  12421847 / 442000000,
  12421847 / 442000000,
  23234227 / 884000000
]

/-- Concrete rational old-plane check for one recovered first-failure
cell. This is only the 63 assigned plane rows at one witness vertex;
it is not strict interior feasibility or a causal ancestor certificate. -/
theorem h3_cell00_vertex_old_planes :
    oldPlaneRows (⟨58, by omega⟩ : Cell)
      (firstFailureH3LeftCodes 0) h3Cell00Vertex := by
  intro I hI
  fin_cases I <;>
    norm_num [oldMasks, oldMaskCode, oldSubsetSum, oldComparison,
      firstFailureH3LeftCodes, h3Cell00Vertex, A, C] at *
/-- The occupied rho uses the very same corrected-parent/eighth policy;
its modulus is physical, squarefree, target-coprime and one-bounded. -/
theorem physical_rho_nonzero_support
    (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z L : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (q : ℕ) (hq :
      physicalRho e chi m omega N cap w z L lambda3 lambda6 q ≠ 0) :
    q ∈ actualSmallRoughModuli
        ((physicalPolicy e chi m omega (N : ℝ) lambda3 lambda6) false)
        N cap w z ∧
      Squarefree q ∧ q.Coprime N ∧
      |physicalRho e chi m omega N cap w z L lambda3 lambda6 q| ≤ 1 := by
  exact adopted_nonzero_physical_support N cap w z L lambda3 lambda6
    (finalPolicy e chi m omega (N : ℝ)) q hq

end
end ImbalancedChen.P5OriginalPhaseBPhysicalBinding
