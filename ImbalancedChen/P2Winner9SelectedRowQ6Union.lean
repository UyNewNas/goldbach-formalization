import ImbalancedChen.P2Winner9SelectedRowQ6Floor
import ImbalancedChen.P2Winner9SelectedRowUnion

/-! The original mixed Q96 floors on the union of the two physical simplices. -/

namespace ImbalancedChen.P2Winner9SelectedRowQ6Union

open MeasureTheory
open P2Winner9PhysicalAffineTransfer P2Winner9SelectedRowAnalyticCaps
open P2Winner9SelectedRowEdgeGeometry P2Winner9SelectedRowRealJacobian
open P2Winner9SelectedRowQ6Floor P2Winner9SelectedRowUnion

/-- The two original directed mixed floors are additive on their physical union. -/
theorem row21_row22_Q96_union_lower :
    (40017007922393485130 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in sourceSupport row21 ∪ sourceSupport row22, physicalUpperIntegrand z := by
  have h21 : IntegrableOn physicalUpperIntegrand (sourceSupport row21) := by
    simpa [vertices] using density_integrable (0 : Fin 2)
  have h22 : IntegrableOn physicalUpperIntegrand (sourceSupport row22) := by
    simpa [vertices] using density_integrable (1 : Fin 2)
  rw [row21_row22_union_integral h21 h22]
  calc
    _ = (33553775924834770601 : ℝ) / 79228162514264337593543950336 +
        (6463231997558714529 : ℝ) / 79228162514264337593543950336 := by norm_num
    _ ≤ _ := add_le_add row21_original_Q96_integral_lower row22_original_Q96_integral_lower

end ImbalancedChen.P2Winner9SelectedRowQ6Union
