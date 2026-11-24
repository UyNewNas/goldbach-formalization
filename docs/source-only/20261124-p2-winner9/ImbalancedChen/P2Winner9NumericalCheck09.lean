import ImbalancedChen.P2Winner9NumericalPage0144
import ImbalancedChen.P2Winner9NumericalPage0145
import ImbalancedChen.P2Winner9NumericalPage0146
import ImbalancedChen.P2Winner9NumericalPage0147
import ImbalancedChen.P2Winner9NumericalPage0148
import ImbalancedChen.P2Winner9NumericalPage0149
import ImbalancedChen.P2Winner9NumericalPage0150
import ImbalancedChen.P2Winner9NumericalPage0151
import ImbalancedChen.P2Winner9NumericalPage0152
import ImbalancedChen.P2Winner9NumericalPage0153
import ImbalancedChen.P2Winner9NumericalPage0154
import ImbalancedChen.P2Winner9NumericalPage0155
import ImbalancedChen.P2Winner9NumericalPage0156
import ImbalancedChen.P2Winner9NumericalPage0157
import ImbalancedChen.P2Winner9NumericalPage0158
import ImbalancedChen.P2Winner9NumericalPage0159

namespace ImbalancedChen.P2Winner9NumericalCheck09
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 2304 256
    P2Winner9CompleteSeedBlock09.rows := by
  change Checked (fun _ r => checkSelected r = true) 2304 256 ([
    P2Winner9CompleteSeedBlock09.pages[0]!,
    P2Winner9CompleteSeedBlock09.pages[1]!,
    P2Winner9CompleteSeedBlock09.pages[2]!,
    P2Winner9CompleteSeedBlock09.pages[3]!,
    P2Winner9CompleteSeedBlock09.pages[4]!,
    P2Winner9CompleteSeedBlock09.pages[5]!,
    P2Winner9CompleteSeedBlock09.pages[6]!,
    P2Winner9CompleteSeedBlock09.pages[7]!,
    P2Winner9CompleteSeedBlock09.pages[8]!,
    P2Winner9CompleteSeedBlock09.pages[9]!,
    P2Winner9CompleteSeedBlock09.pages[10]!,
    P2Winner9CompleteSeedBlock09.pages[11]!,
    P2Winner9CompleteSeedBlock09.pages[12]!,
    P2Winner9CompleteSeedBlock09.pages[13]!,
    P2Winner9CompleteSeedBlock09.pages[14]!,
    P2Winner9CompleteSeedBlock09.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0144.checked.flatten_cons <|
    P2Winner9NumericalPage0145.checked.flatten_cons <|
    P2Winner9NumericalPage0146.checked.flatten_cons <|
    P2Winner9NumericalPage0147.checked.flatten_cons <|
    P2Winner9NumericalPage0148.checked.flatten_cons <|
    P2Winner9NumericalPage0149.checked.flatten_cons <|
    P2Winner9NumericalPage0150.checked.flatten_cons <|
    P2Winner9NumericalPage0151.checked.flatten_cons <|
    P2Winner9NumericalPage0152.checked.flatten_cons <|
    P2Winner9NumericalPage0153.checked.flatten_cons <|
    P2Winner9NumericalPage0154.checked.flatten_cons <|
    P2Winner9NumericalPage0155.checked.flatten_cons <|
    P2Winner9NumericalPage0156.checked.flatten_cons <|
    P2Winner9NumericalPage0157.checked.flatten_cons <|
    P2Winner9NumericalPage0158.checked.flatten_cons <|
    P2Winner9NumericalPage0159.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck09
