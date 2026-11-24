import ImbalancedChen.P2Winner9NumericalPage0128
import ImbalancedChen.P2Winner9NumericalPage0129
import ImbalancedChen.P2Winner9NumericalPage0130
import ImbalancedChen.P2Winner9NumericalPage0131
import ImbalancedChen.P2Winner9NumericalPage0132
import ImbalancedChen.P2Winner9NumericalPage0133
import ImbalancedChen.P2Winner9NumericalPage0134
import ImbalancedChen.P2Winner9NumericalPage0135
import ImbalancedChen.P2Winner9NumericalPage0136
import ImbalancedChen.P2Winner9NumericalPage0137
import ImbalancedChen.P2Winner9NumericalPage0138
import ImbalancedChen.P2Winner9NumericalPage0139
import ImbalancedChen.P2Winner9NumericalPage0140
import ImbalancedChen.P2Winner9NumericalPage0141
import ImbalancedChen.P2Winner9NumericalPage0142
import ImbalancedChen.P2Winner9NumericalPage0143

namespace ImbalancedChen.P2Winner9NumericalCheck08
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 2048 256
    P2Winner9CompleteSeedBlock08.rows := by
  change Checked (fun _ r => checkSelected r = true) 2048 256 ([
    P2Winner9CompleteSeedBlock08.pages[0]!,
    P2Winner9CompleteSeedBlock08.pages[1]!,
    P2Winner9CompleteSeedBlock08.pages[2]!,
    P2Winner9CompleteSeedBlock08.pages[3]!,
    P2Winner9CompleteSeedBlock08.pages[4]!,
    P2Winner9CompleteSeedBlock08.pages[5]!,
    P2Winner9CompleteSeedBlock08.pages[6]!,
    P2Winner9CompleteSeedBlock08.pages[7]!,
    P2Winner9CompleteSeedBlock08.pages[8]!,
    P2Winner9CompleteSeedBlock08.pages[9]!,
    P2Winner9CompleteSeedBlock08.pages[10]!,
    P2Winner9CompleteSeedBlock08.pages[11]!,
    P2Winner9CompleteSeedBlock08.pages[12]!,
    P2Winner9CompleteSeedBlock08.pages[13]!,
    P2Winner9CompleteSeedBlock08.pages[14]!,
    P2Winner9CompleteSeedBlock08.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0128.checked.flatten_cons <|
    P2Winner9NumericalPage0129.checked.flatten_cons <|
    P2Winner9NumericalPage0130.checked.flatten_cons <|
    P2Winner9NumericalPage0131.checked.flatten_cons <|
    P2Winner9NumericalPage0132.checked.flatten_cons <|
    P2Winner9NumericalPage0133.checked.flatten_cons <|
    P2Winner9NumericalPage0134.checked.flatten_cons <|
    P2Winner9NumericalPage0135.checked.flatten_cons <|
    P2Winner9NumericalPage0136.checked.flatten_cons <|
    P2Winner9NumericalPage0137.checked.flatten_cons <|
    P2Winner9NumericalPage0138.checked.flatten_cons <|
    P2Winner9NumericalPage0139.checked.flatten_cons <|
    P2Winner9NumericalPage0140.checked.flatten_cons <|
    P2Winner9NumericalPage0141.checked.flatten_cons <|
    P2Winner9NumericalPage0142.checked.flatten_cons <|
    P2Winner9NumericalPage0143.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck08
