import ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerPositive
import Mathlib.Data.Rat.Floor

/-!
CODE_ONLY / uncompiled. This is a genuine Q80 floor certified by the
original Wu source lower theorem at the first positive bank cell's right
endpoint. It is deliberately distinct from the larger copied enhanced-bank
entry and does not assert `BankEndpointLicences`.
-/

namespace ImbalancedChen.P2HBankSourceFloor50

noncomputable section

open Certificates.P2HistoricQ80DefectLookup
open P2HistoricSavedOrdinaryDefectAssembly

theorem right50 : bankCellRight 50 = (101 / 50 : ℚ) := by
  norm_num [bankCellRight]

theorem copied50 : bankLowerTable 50 = 37335258798817765329518 := by
  norm_num [bankLowerTable, bankLowerNumerators]

/-- A concrete explicit lower line found in the pinned original-Wu
supplier at this endpoint is `37/18750`. We round this value downward with
the same Q80 convention as the historical bank. -/
def sourceFloor50 : ℤ := ⌊((37 / 18750 : ℚ) * (Q : ℚ))⌋

theorem sourceFloor50_decode_le :
    P2HistoricOrdinaryParentClosed.decodeQ80 sourceFloor50 ≤ (37 / 18750 : ℝ) := by
  have hfloor : (sourceFloor50 : ℚ) ≤ (37 / 18750 : ℚ) * (Q : ℚ) := by
    exact Int.floor_le _
  have hrat : ((sourceFloor50 : ℚ) / (Q : ℚ) : ℚ) ≤ 37 / 18750 := by
    apply (div_le_iff₀ Q_pos).mpr
    exact hfloor
  change (((sourceFloor50 : ℚ) / (Q : ℚ) : ℚ) : ℝ) ≤ (37 / 18750 : ℝ)
  exact_mod_cast hrat

/-- A concrete positive original-family Q80 endpoint licence. It certifies
the source floor above, with no h-bank or saved-result hypothesis. -/
theorem sourceFloor50_le_actual_h :
    P2HistoricOrdinaryParentClosed.decodeQ80 sourceFloor50 ≤
      P2TableActionSourceOnly.h (1 / 1000) (bankCellRight 50 : ℝ) := by
  have hs : (37 / 18750 : ℝ) <
      Wu2008DoubleSieve.wuImprovementLimit false (1 / 1000) (101 / 50) := by
    convert Wu2008DoubleSieve.SecondFunctionalLowerPositive.h_strict
      (s := (101 / 50 : ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  rw [right50]
  change P2HistoricOrdinaryParentClosed.decodeQ80 sourceFloor50 ≤
    Wu2008DoubleSieve.wuImprovementLimit false (1 / 1000) (101 / 50)
  exact (sourceFloor50_decode_le).trans hs.le

/-- Exact quantitative shortfall: the copied entry exceeds the rounded
original-source lower line. This says nothing adverse about the true h;
it isolates why the available lower theorem cannot license this bank cell. -/
theorem sourceFloor50_lt_copied50 : sourceFloor50 < bankLowerTable 50 := by
  have hfloor : (sourceFloor50 : ℚ) ≤ (37 / 18750 : ℚ) * (Q : ℚ) :=
    Int.floor_le _
  have hgap : (37 / 18750 : ℚ) * (Q : ℚ) < (bankLowerTable 50 : ℚ) := by
    rw [copied50]
    norm_num [Q]
  exact_mod_cast hfloor.trans_lt hgap

end

end ImbalancedChen.P2HBankSourceFloor50
