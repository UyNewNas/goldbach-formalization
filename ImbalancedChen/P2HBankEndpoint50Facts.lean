import ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerPositive

/-!
CODE_ONLY / uncompiled.

This module records the first positive literal h-bank entry and the actual
right endpoint of its closed cell. It deliberately does not claim the missing
bank-to-Wu endpoint licence. The copied bank is a finite 248-generation table;
the source h below is the infinite depth limit of the original Wu family.
-/

namespace ImbalancedChen.P2HBankEndpoint50Facts

noncomputable section

open Certificates.P2HistoricQ80DefectLookup
open P2HistoricSavedOrdinaryDefectAssembly

theorem bankCellRight_fifty : bankCellRight 50 = (101 / 50 : ℚ) := by
  norm_num [bankCellRight]

theorem bankLowerTable_fifty :
    bankLowerTable 50 = 37335258798817765329518 := by
  norm_num [bankLowerTable, bankLowerNumerators]

theorem bankLowerTable_fifty_decode :
    P2HistoricOrdinaryParentClosed.decodeQ80 (bankLowerTable 50) =
      (((37335258798817765329518 : ℚ) / (2 ^ 80 : ℚ) : ℚ) : ℝ) := by
  rw [bankLowerTable_fifty]
  rfl

/-- The strongest explicit lower source line found near this point is positive
but falls short of the copied bank coefficient. It is a theorem about the
actual original Wu limit, not a certificate for the finite bank. -/
theorem source_lower_fifty :
    ((7 / 2 - 101 / 50 : ℝ) / 750) <
      Wu2008DoubleSieve.wuImprovementLimit false (1 / 1000) (101 / 50) := by
  exact Wu2008DoubleSieve.SecondFunctionalLowerPositive.h_strict
    (by norm_num) (by norm_num)

theorem source_lower_fifty_below_bank :
    ((7 / 2 - 101 / 50 : ℝ) / 750) <
      P2HistoricOrdinaryParentClosed.decodeQ80 (bankLowerTable 50) := by
  rw [bankLowerTable_fifty_decode]
  norm_num

end

end ImbalancedChen.P2HBankEndpoint50Facts
