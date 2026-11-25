import ImbalancedChen.P2Winner9CompleteSeedBlock38
import ImbalancedChen.P2Winner9SelectedArchiveChecker
import ImbalancedChen.P2Winner9SeedArchiveChecks
import ImbalancedChen.P2Winner9MaterializedLogChecker

/-! Original selected numerical certificates for ordinals 9888–9903. -/

namespace ImbalancedChen.P2Winner9NumericalPage0618
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)
open P2Winner9MaterializedLogChecker (checkSelectedMaterialized_sound)

set_option maxRecDepth 50000
set_option maxHeartbeats 40000000
set_option Elab.async true

private theorem row00 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[0]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row01 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[1]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row02 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[2]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row03 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[3]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row04 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[4]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row05 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[5]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row06 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[6]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row07 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[7]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row08 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[8]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row09 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[9]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row10 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[10]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row11 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[11]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row12 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[12]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row13 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[13]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row14 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[14]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

private theorem row15 : checkSelected (P2Winner9CompleteSeedBlock38.pages[10]!)[15]! = true := by
  apply checkSelectedMaterialized_sound
  decide +kernel

theorem checked : Checked (fun _ r => checkSelected r = true) 9888 16
    (P2Winner9CompleteSeedBlock38.pages[10]!) := by
  refine ⟨by decide +kernel, fun i => ?_⟩
  fin_cases i
  · exact row00
  · exact row01
  · exact row02
  · exact row03
  · exact row04
  · exact row05
  · exact row06
  · exact row07
  · exact row08
  · exact row09
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15

end ImbalancedChen.P2Winner9NumericalPage0618
