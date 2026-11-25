import ImbalancedChen.P2Winner9NumericalPage0112
import ImbalancedChen.P2Winner9NumericalPage0113
import ImbalancedChen.P2Winner9NumericalPage0114
import ImbalancedChen.P2Winner9NumericalPage0115
import ImbalancedChen.P2Winner9NumericalPage0116
import ImbalancedChen.P2Winner9NumericalPage0117
import ImbalancedChen.P2Winner9NumericalPage0118
import ImbalancedChen.P2Winner9NumericalPage0119
import ImbalancedChen.P2Winner9NumericalPage0120
import ImbalancedChen.P2Winner9NumericalPage0121
import ImbalancedChen.P2Winner9NumericalPage0122
import ImbalancedChen.P2Winner9NumericalPage0123
import ImbalancedChen.P2Winner9NumericalPage0124
import ImbalancedChen.P2Winner9NumericalPage0125
import ImbalancedChen.P2Winner9NumericalPage0126
import ImbalancedChen.P2Winner9NumericalPage0127

namespace ImbalancedChen.P2Winner9NumericalCheck07
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 1792 256
    P2Winner9CompleteSeedBlock07.rows := by
  change Checked (fun _ r => checkSelected r = true) 1792 256 ([
    P2Winner9CompleteSeedBlock07.pages[0]!,
    P2Winner9CompleteSeedBlock07.pages[1]!,
    P2Winner9CompleteSeedBlock07.pages[2]!,
    P2Winner9CompleteSeedBlock07.pages[3]!,
    P2Winner9CompleteSeedBlock07.pages[4]!,
    P2Winner9CompleteSeedBlock07.pages[5]!,
    P2Winner9CompleteSeedBlock07.pages[6]!,
    P2Winner9CompleteSeedBlock07.pages[7]!,
    P2Winner9CompleteSeedBlock07.pages[8]!,
    P2Winner9CompleteSeedBlock07.pages[9]!,
    P2Winner9CompleteSeedBlock07.pages[10]!,
    P2Winner9CompleteSeedBlock07.pages[11]!,
    P2Winner9CompleteSeedBlock07.pages[12]!,
    P2Winner9CompleteSeedBlock07.pages[13]!,
    P2Winner9CompleteSeedBlock07.pages[14]!,
    P2Winner9CompleteSeedBlock07.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0112.checked.flatten_cons <|
    P2Winner9NumericalPage0113.checked.flatten_cons <|
    P2Winner9NumericalPage0114.checked.flatten_cons <|
    P2Winner9NumericalPage0115.checked.flatten_cons <|
    P2Winner9NumericalPage0116.checked.flatten_cons <|
    P2Winner9NumericalPage0117.checked.flatten_cons <|
    P2Winner9NumericalPage0118.checked.flatten_cons <|
    P2Winner9NumericalPage0119.checked.flatten_cons <|
    P2Winner9NumericalPage0120.checked.flatten_cons <|
    P2Winner9NumericalPage0121.checked.flatten_cons <|
    P2Winner9NumericalPage0122.checked.flatten_cons <|
    P2Winner9NumericalPage0123.checked.flatten_cons <|
    P2Winner9NumericalPage0124.checked.flatten_cons <|
    P2Winner9NumericalPage0125.checked.flatten_cons <|
    P2Winner9NumericalPage0126.checked.flatten_cons <|
    P2Winner9NumericalPage0127.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck07
