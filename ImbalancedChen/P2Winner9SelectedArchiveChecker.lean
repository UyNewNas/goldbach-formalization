import ImbalancedChen.P2Winner9FastLogCertificates
import ImbalancedChen.P2Winner9GenericRowIntegral
import ImbalancedChen.P2Winner9RowArithmeticChecker

/-! A checked winning branch supplies the selected floor of an original physical row. -/

namespace ImbalancedChen.P2Winner9SelectedArchiveChecker

open MeasureTheory
open P2Winner9CompleteSeedTypes (RawRow)
open P2Winner9SelectedRowRealJacobian (RationalVertices sourceSupport)
open P2Winner9PhysicalAffineTransfer (physicalUpperIntegrand)
open P2Winner9CurvatureExactMomentFloor (q96)
open P2Winner9RowArithmeticChecker

def row (v : RationalVertices) (r : RawRow) (h : BasicChecks v r) :
    P2Winner9GenericRowIntegral.Row :=
  let h := basic_sound h
  ⟨v, r.means, r.jensen, h.det_ne, h.gap_nonneg, h.gap_sum_pos, h.factor_pos, h.means_pos,
    h.p_mean, h.jensen_eq⟩

def logGeometry (v : RationalVertices) (r : RawRow) (h : BasicChecks v r) :
    P2Winner9GenericLogBranch.Geometry :=
  let h := basic_sound h
  ⟨v, h.det_ne, h.gap_nonneg, h.gap_sum_pos, h.factor_pos⟩

private theorem log_jensen_eq {v : RationalVertices} {r : RawRow} (h : BasicChecks v r) :
    r.jensen = P2Winner9GenericLogBranch.jensenQ (logGeometry v r h) := by
  rw [(basic_sound h).jensen_eq]
  simp only [P2Winner9GenericLogBranch.jensenQ, P2Winner9GenericLogBranch.meansQ, logGeometry,
    (basic_sound h).factor_mean]

def logFloors (r : RawRow) (j : Fin 10) : ℕ := r.logGapFloors[j.val]!

open P2Winner9GenericLogBranch (savedGapQ logGapQ logPriceQ)
open P2Winner9FastLogCertificates (logFloorCheck logFloorCheck_iff)

abbrev LogChecks (v : RationalVertices) (r : RawRow) (h : BasicChecks v r) : Prop :=
  (∀ j, savedGapQ (logFloors r) j ≤ logGapQ (logGeometry v r h) j) ∧
    (r.logSelected : ℚ) / q96 ≤ logPriceQ r.jensen (logFloors r)

def checkLog (v : RationalVertices) (r : RawRow) : Bool :=
  withRowNumerics v r fun v' r' =>
    letI : Decidable (BasicChecks v' r') := basicDecidable v' r'
    if h : BasicChecks v' r' then
      decide ((∀ j, logFloorCheck (logGeometry v' r' h) j (logFloors r' j)) ∧
        (r'.logSelected : ℚ) / q96 ≤ logPriceQ r'.jensen (logFloors r'))
    else false

theorem checkLog_sound {v : RationalVertices} {r : RawRow} (h : checkLog v r = true) :
    ∃ hb : BasicChecks v r, LogChecks v r hb := by
  rw [checkLog, withRowNumerics_eq] at h
  split at h
  · rename_i hb
    obtain ⟨hg, hf⟩ := of_decide_eq_true h
    exact ⟨hb, fun j => (logFloorCheck_iff _ j _).mp (hg j), hf⟩
  · contradiction

/-- The stored comparison selects which of the two integral certificates to evaluate. -/
def checkSelected (r : RawRow) : Bool :=
  if r.logSelected ≤ r.mixedRaw then checkQ6 (archiveVertices r) r
  else checkLog (archiveVertices r) r

theorem checkSelected_basic {r : RawRow} (h : checkSelected r = true) :
    BasicChecks (archiveVertices r) r := by
  unfold checkSelected at h
  split at h
  · exact (checkQ6_sound h).choose
  · exact (checkLog_sound h).choose

/-- The selected archive numerator bounds the original physical density integral. -/
theorem checkSelected_sound {r : RawRow} (h : checkSelected r = true)
    (hselected : r.mixedSelected = max r.logSelected r.mixedRaw) :
    (r.mixedSelected : ℝ) / (q96 : ℝ) ≤
      ∫ z in sourceSupport (archiveVertices r), physicalUpperIntegrand z := by
  unfold checkSelected at h
  rw [hselected]
  split at h
  · rename_i horder
    rw [max_eq_right horder]
    obtain ⟨hb, hq⟩ := checkQ6_sound h
    exact P2Winner9GenericRowIntegral.Q6_floor_actual_integral
      (row (archiveVertices r) r hb) r.mixedRaw (q6_lower_normalized hb hq)
  · rename_i horder
    rw [max_eq_left (Nat.le_of_not_ge horder)]
    obtain ⟨hb, hg, hf⟩ := checkLog_sound h
    exact P2Winner9GenericLogBranch.directed_log_floor (logGeometry (archiveVertices r) r hb)
      r.jensen (logFloors r) r.logSelected (log_jensen_eq hb) hg hf

end ImbalancedChen.P2Winner9SelectedArchiveChecker
