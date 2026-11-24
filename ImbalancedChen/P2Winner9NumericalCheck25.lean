import ImbalancedChen.P2Winner9NumericalPage0400
import ImbalancedChen.P2Winner9NumericalPage0401
import ImbalancedChen.P2Winner9NumericalPage0402
import ImbalancedChen.P2Winner9NumericalPage0403
import ImbalancedChen.P2Winner9NumericalPage0404
import ImbalancedChen.P2Winner9NumericalPage0405
import ImbalancedChen.P2Winner9NumericalPage0406
import ImbalancedChen.P2Winner9NumericalPage0407
import ImbalancedChen.P2Winner9NumericalPage0408
import ImbalancedChen.P2Winner9NumericalPage0409
import ImbalancedChen.P2Winner9NumericalPage0410
import ImbalancedChen.P2Winner9NumericalPage0411
import ImbalancedChen.P2Winner9NumericalPage0412
import ImbalancedChen.P2Winner9NumericalPage0413
import ImbalancedChen.P2Winner9NumericalPage0414
import ImbalancedChen.P2Winner9NumericalPage0415

namespace ImbalancedChen.P2Winner9NumericalCheck25
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 6400 256
    P2Winner9CompleteSeedBlock25.rows := by
  change Checked (fun _ r => checkSelected r = true) 6400 256 ([
    P2Winner9CompleteSeedBlock25.pages[0]!,
    P2Winner9CompleteSeedBlock25.pages[1]!,
    P2Winner9CompleteSeedBlock25.pages[2]!,
    P2Winner9CompleteSeedBlock25.pages[3]!,
    P2Winner9CompleteSeedBlock25.pages[4]!,
    P2Winner9CompleteSeedBlock25.pages[5]!,
    P2Winner9CompleteSeedBlock25.pages[6]!,
    P2Winner9CompleteSeedBlock25.pages[7]!,
    P2Winner9CompleteSeedBlock25.pages[8]!,
    P2Winner9CompleteSeedBlock25.pages[9]!,
    P2Winner9CompleteSeedBlock25.pages[10]!,
    P2Winner9CompleteSeedBlock25.pages[11]!,
    P2Winner9CompleteSeedBlock25.pages[12]!,
    P2Winner9CompleteSeedBlock25.pages[13]!,
    P2Winner9CompleteSeedBlock25.pages[14]!,
    P2Winner9CompleteSeedBlock25.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0400.checked.flatten_cons <|
    P2Winner9NumericalPage0401.checked.flatten_cons <|
    P2Winner9NumericalPage0402.checked.flatten_cons <|
    P2Winner9NumericalPage0403.checked.flatten_cons <|
    P2Winner9NumericalPage0404.checked.flatten_cons <|
    P2Winner9NumericalPage0405.checked.flatten_cons <|
    P2Winner9NumericalPage0406.checked.flatten_cons <|
    P2Winner9NumericalPage0407.checked.flatten_cons <|
    P2Winner9NumericalPage0408.checked.flatten_cons <|
    P2Winner9NumericalPage0409.checked.flatten_cons <|
    P2Winner9NumericalPage0410.checked.flatten_cons <|
    P2Winner9NumericalPage0411.checked.flatten_cons <|
    P2Winner9NumericalPage0412.checked.flatten_cons <|
    P2Winner9NumericalPage0413.checked.flatten_cons <|
    P2Winner9NumericalPage0414.checked.flatten_cons <|
    P2Winner9NumericalPage0415.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck25
