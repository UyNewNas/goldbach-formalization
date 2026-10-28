import ImbalancedChen.P2Winner9CompleteSeedData
import ImbalancedChen.P2Winner9SelectedRowIntegralFloor
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact ports of the two prior analytic rows into the complete literal seed
family. These two simplexes do NOT establish all11026 rows or ledger
slot21/22 by themselves. No arbitrary selected index set is used.
-/

namespace ImbalancedChen.P2Winner9CompleteSeedAnalyticPorts

noncomputable section

open Set MeasureTheory
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9SelectedRowIntegralFloor

def row21Index : RowIndex := ⟨21, by decide⟩
def row22Index : RowIndex := ⟨22, by decide⟩

def physicalSupport (i : RowIndex) : Set Ambient := sourceSupport (physicalVertices i)

/-- Original actual-array lookup matches the frozen physical vertices,
stored means and final floors used by the F analytic theorem. No matrix,
geometry or floor computation was run; this closed equality is source only. -/
theorem row21_literal_port :
    physicalVertices row21Index = row21 ∧
      (entry row21Index).means = Row21.means ∧
      (entry row21Index).mixedRaw = 33553775924834770601 ∧
      (entry row21Index).mixedSelected = 33553775924834770601 := by
  decide +kernel

theorem row22_literal_port :
    physicalVertices row22Index = row22 ∧
      (entry row22Index).means = Row22.means ∧
      (entry row22Index).mixedRaw = 6463231997558714529 ∧
      (entry row22Index).mixedSelected = 6463231997558714529 := by
  decide +kernel

theorem row21_actual_support_identity :
    physicalSupport row21Index = sourceSupport row21 := by
  rw [physicalSupport, row21_literal_port.1]

theorem row22_actual_support_identity :
    physicalSupport row22Index = sourceSupport row22 := by
  rw [physicalSupport, row22_literal_port.1]

/-- One real complete-family member consumes its proved same-support
analytic enclosure; no family-wide enclosure is assumed. -/
theorem actual_row21_selected_floor :
    ((entry row21Index).mixedSelected : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in physicalSupport row21Index, physicalUpperIntegrand z := by
  rw [row21_literal_port.2.2.2, row21_actual_support_identity]
  exact row21_original_Q96_integral_lower

theorem actual_row22_selected_floor :
    ((entry row22Index).mixedSelected : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in physicalSupport row22Index, physicalUpperIntegrand z := by
  rw [row22_literal_port.2.2.2, row22_actual_support_identity]
  exact row22_original_Q96_integral_lower

end

end ImbalancedChen.P2Winner9CompleteSeedAnalyticPorts
