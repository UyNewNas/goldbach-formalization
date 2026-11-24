import ImbalancedChen.P2Winner9CompleteSeedBlock36
import ImbalancedChen.P2Winner9SelectedArchiveChecker
import ImbalancedChen.P2Winner9SeedArchiveChecks

/-! Original selected numerical certificates for ordinals 9392–9407. -/

namespace ImbalancedChen.P2Winner9NumericalPage0587
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 50000
set_option maxHeartbeats 40000000
set_option Elab.async true

private theorem row00 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[0]! = true := by
  decide +kernel

private theorem row01 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[1]! = true := by
  decide +kernel

private theorem row02 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[2]! = true := by
  decide +kernel

private theorem row03 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[3]! = true := by
  decide +kernel

private theorem row04 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[4]! = true := by
  decide +kernel

private theorem row05 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[5]! = true := by
  decide +kernel

private theorem row06 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[6]! = true := by
  decide +kernel

private theorem row07 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[7]! = true := by
  decide +kernel

private theorem row08 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[8]! = true := by
  decide +kernel

private theorem row09 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[9]! = true := by
  decide +kernel

private theorem row10 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[10]! = true := by
  decide +kernel

private theorem row11 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[11]! = true := by
  decide +kernel

private theorem row12 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[12]! = true := by
  decide +kernel

private theorem row13 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[13]! = true := by
  decide +kernel

private theorem row14 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[14]! = true := by
  decide +kernel

private theorem row15 : checkSelected (P2Winner9CompleteSeedBlock36.pages[11]!)[15]! = true := by
  decide +kernel

theorem checked : Checked (fun _ r => checkSelected r = true) 9392 16
    (P2Winner9CompleteSeedBlock36.pages[11]!) := by
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

end ImbalancedChen.P2Winner9NumericalPage0587
