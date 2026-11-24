import ImbalancedChen.P2Winner9NumericalPage0224
import ImbalancedChen.P2Winner9NumericalPage0225
import ImbalancedChen.P2Winner9NumericalPage0226
import ImbalancedChen.P2Winner9NumericalPage0227
import ImbalancedChen.P2Winner9NumericalPage0228
import ImbalancedChen.P2Winner9NumericalPage0229
import ImbalancedChen.P2Winner9NumericalPage0230
import ImbalancedChen.P2Winner9NumericalPage0231
import ImbalancedChen.P2Winner9NumericalPage0232
import ImbalancedChen.P2Winner9NumericalPage0233
import ImbalancedChen.P2Winner9NumericalPage0234
import ImbalancedChen.P2Winner9NumericalPage0235
import ImbalancedChen.P2Winner9NumericalPage0236
import ImbalancedChen.P2Winner9NumericalPage0237
import ImbalancedChen.P2Winner9NumericalPage0238
import ImbalancedChen.P2Winner9NumericalPage0239

namespace ImbalancedChen.P2Winner9NumericalCheck14
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 3584 256
    P2Winner9CompleteSeedBlock14.rows := by
  change Checked (fun _ r => checkSelected r = true) 3584 256 ([
    P2Winner9CompleteSeedBlock14.pages[0]!,
    P2Winner9CompleteSeedBlock14.pages[1]!,
    P2Winner9CompleteSeedBlock14.pages[2]!,
    P2Winner9CompleteSeedBlock14.pages[3]!,
    P2Winner9CompleteSeedBlock14.pages[4]!,
    P2Winner9CompleteSeedBlock14.pages[5]!,
    P2Winner9CompleteSeedBlock14.pages[6]!,
    P2Winner9CompleteSeedBlock14.pages[7]!,
    P2Winner9CompleteSeedBlock14.pages[8]!,
    P2Winner9CompleteSeedBlock14.pages[9]!,
    P2Winner9CompleteSeedBlock14.pages[10]!,
    P2Winner9CompleteSeedBlock14.pages[11]!,
    P2Winner9CompleteSeedBlock14.pages[12]!,
    P2Winner9CompleteSeedBlock14.pages[13]!,
    P2Winner9CompleteSeedBlock14.pages[14]!,
    P2Winner9CompleteSeedBlock14.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0224.checked.flatten_cons <|
    P2Winner9NumericalPage0225.checked.flatten_cons <|
    P2Winner9NumericalPage0226.checked.flatten_cons <|
    P2Winner9NumericalPage0227.checked.flatten_cons <|
    P2Winner9NumericalPage0228.checked.flatten_cons <|
    P2Winner9NumericalPage0229.checked.flatten_cons <|
    P2Winner9NumericalPage0230.checked.flatten_cons <|
    P2Winner9NumericalPage0231.checked.flatten_cons <|
    P2Winner9NumericalPage0232.checked.flatten_cons <|
    P2Winner9NumericalPage0233.checked.flatten_cons <|
    P2Winner9NumericalPage0234.checked.flatten_cons <|
    P2Winner9NumericalPage0235.checked.flatten_cons <|
    P2Winner9NumericalPage0236.checked.flatten_cons <|
    P2Winner9NumericalPage0237.checked.flatten_cons <|
    P2Winner9NumericalPage0238.checked.flatten_cons <|
    P2Winner9NumericalPage0239.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck14
