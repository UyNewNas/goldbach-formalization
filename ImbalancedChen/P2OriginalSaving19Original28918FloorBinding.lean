import ImbalancedChen.P2OriginalSaving19Original28918
import ImbalancedChen.P2OriginalSaving19HigherMoments

/-!
SOURCE ONLY. UNCOMPILED. All closed finite proof terms UNEVALUATED.
The higher-moment theorem is supplied by the separate M owner, with the
exact original rational duplicated-node formula. No integral equality is
an input to fullMomentRow. K and the higher-moment module remain held,
uncompiled source dependencies; neither a hash nor this import is credit.
-/

namespace ImbalancedChen.P2OriginalSaving19Original28918FloorBinding

set_option maxRecDepth 1000000

open scoped BigOperators
open MeasureTheory
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalLogMomentQ96CheckerSourceOnly
open P2OriginalSaving19Archive
open P2OriginalSaving19Original28918
open P2OriginalSaving19HigherMoments

/-- The archive stores Q80 integers, not a power-moment table. This
computation uses precisely its original physical vertices and saved max. -/
def momentsQ (r : OriginalRowIndex) (j : Fin 10) (k : ℕ) : ℚ :=
  rationalMoment (fun i => gapQ (rawVertex r i))
    (fun i => 1 - factorsQ (rawVertex r i) j / topsQ r j) k

def FloorChecks (r : OriginalRowIndex) : Prop :=
  (∀ j, momentsQ r j 1 = 1 - meansQ r j / topsQ r j) ∧
  (∀ j : Fin 10, (rawMomentRow r).factorFloorsQ80[j.val]! =
    factorFloorQ80 (momentsQ r j)) ∧
  (rawMomentRow r).oldFloorQ96 = (rawGeometryRow r).jensenFloorQ96 ∧
  (rawMomentRow r).oldFloorQ96 = oldFloorQ96 (massQ r) (meansQ r) ∧
  (rawMomentRow r).newFloorQ96 =
    max (oldFloorQ96 (massQ r) (meansQ r))
      (newFloorQ96 (massQ r) (meansQ r) (momentsQ r))

instance (r : OriginalRowIndex) : Decidable (FloorChecks r) := by
  unfold FloorChecks
  infer_instance

/-- Closed kernel source-data guard; neither execution nor acceptance
is claimed. No premise certifies the saved floor or its aggregate. -/
theorem original_floor_checks : ∀ r, FloorChecks r := by decide

theorem firstMomentEncoding (r : OriginalRowIndex) (j : Fin 10) :
    momentsQ r j 1 = 1 - meansQ r j / topsQ r j :=
  (original_floor_checks r).1 j

theorem saved_Q80_binding (r : OriginalRowIndex) (j : Fin 10) :
    (rawMomentRow r).factorFloorsQ80[j.val]! = factorFloorQ80 (momentsQ r j) :=
  (original_floor_checks r).2.1 j

noncomputable section

def algebraicMomentRow (r : OriginalRowIndex) : AlgebraicMomentRow where
  linear := rowLinear r
  base := rowBase r
  physicalVertices := row_physicalVertices r
  positiveGapTotal := row_positiveGapTotal r
  massQ := massQ r
  meansQ := meansQ r
  topsQ := topsQ r
  momentsQ := momentsQ r
  gapsQ := fun i => gapQ (rawVertex r i)
  factorsQ := fun i j => factorsQ (rawVertex r i) j
  massEncoding := row_massEncoding r
  meansEncoding := row_meansEncoding r
  topsEncoding := row_topsEncoding r
  gapsEncoding := row_gapsEncoding r
  factorsEncoding := row_factorsEncoding r
  firstMomentEncoding := firstMomentEncoding r
  higherMomentEncoding := fun _ _ _ _ => rfl

/-- Actual typed ORIGINAL13/28918 family, with analytic higher powers
derived by the peer theorem. No MomentRow-valued family is a parameter. -/
def fullMomentRow (r : OriginalRowIndex) : MomentRow :=
  (algebraicMomentRow r).toMomentRow

theorem fullMomentRow_linear (r : OriginalRowIndex) :
    (fullMomentRow r).linear = rowLinear r := rfl

theorem fullMomentRow_base (r : OriginalRowIndex) :
    (fullMomentRow r).base = rowBase r := rfl

theorem saved_Q96_binding (r : OriginalRowIndex) :
    ((rawMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 =
      originalRowFloor (fullMomentRow r) := by
  change ((rawMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 =
    ((max (oldFloorQ96 (massQ r) (meansQ r))
      (newFloorQ96 (massQ r) (meansQ r) (momentsQ r)) : ℤ) : ℚ) / (2 : ℚ)^96
  rw [(original_floor_checks r).2.2.2.2]

theorem saved_row_floor_le_actual_simplex_integral (r : OriginalRowIndex) :
    (((rawMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℝ) ≤
      ∫ t in support (rowLinear r) (rowBase r), conservativeDensity t := by
  rw [saved_Q96_binding]
  exact originalRowFloor_sound (fullMomentRow r)

/-- Still closed and UNEVALUATED. These are replacement totals for the
same rows. No second gain is manufactured by adding old and new. -/
theorem saved_new_total :
    (∑ r : OriginalRowIndex, (rawMomentRow r).newFloorQ96) =
      283388722705335806564439 := by decide

theorem saved_old_total :
    (∑ r : OriginalRowIndex, (rawMomentRow r).oldFloorQ96) =
      4 * 69876938299079768108917 := by decide

theorem saved_replacement_increment :
    (∑ r : OriginalRowIndex,
      ((rawMomentRow r).newFloorQ96 - (rawMomentRow r).oldFloorQ96)) =
      3880969509016734128771 := by
  rw [Finset.sum_sub_distrib, saved_new_total, saved_old_total]
  norm_num

theorem original_floor_total :
    (∑ r : OriginalRowIndex, originalRowFloor (fullMomentRow r)) =
      (283388722705335806564439 : ℚ) / (2 : ℚ)^96 := by
  simp_rw [← saved_Q96_binding]
  rw [← Finset.sum_div, ← Int.cast_sum, saved_new_total]

/-- Endpoint only for the sum of these true physical simplex integrals.
The selectedSaving inclusion/ownership bridge is deliberately absent. -/
theorem original_endpoint_le_simplex_integral_sum :
    (283388722705335806564439 : ℝ) / (2 : ℝ)^96 ≤
      ∑ r : OriginalRowIndex,
        ∫ t in support (rowLinear r) (rowBase r), conservativeDensity t := by
  have h := original_family_floor_sum_le_integral_sum fullMomentRow
  have he : (∑ r : OriginalRowIndex, (originalRowFloor (fullMomentRow r) : ℝ)) =
      (283388722705335806564439 : ℝ) / (2 : ℝ)^96 := by
    exact_mod_cast original_floor_total
  rw [he] at h
  exact h

end

end ImbalancedChen.P2OriginalSaving19Original28918FloorBinding
