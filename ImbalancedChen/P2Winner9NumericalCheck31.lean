import ImbalancedChen.P2Winner9NumericalPage0496
import ImbalancedChen.P2Winner9NumericalPage0497
import ImbalancedChen.P2Winner9NumericalPage0498
import ImbalancedChen.P2Winner9NumericalPage0499
import ImbalancedChen.P2Winner9NumericalPage0500
import ImbalancedChen.P2Winner9NumericalPage0501
import ImbalancedChen.P2Winner9NumericalPage0502
import ImbalancedChen.P2Winner9NumericalPage0503
import ImbalancedChen.P2Winner9NumericalPage0504
import ImbalancedChen.P2Winner9NumericalPage0505
import ImbalancedChen.P2Winner9NumericalPage0506
import ImbalancedChen.P2Winner9NumericalPage0507
import ImbalancedChen.P2Winner9NumericalPage0508
import ImbalancedChen.P2Winner9NumericalPage0509
import ImbalancedChen.P2Winner9NumericalPage0510
import ImbalancedChen.P2Winner9NumericalPage0511

namespace ImbalancedChen.P2Winner9NumericalCheck31
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 7936 256
    P2Winner9CompleteSeedBlock31.rows := by
  change Checked (fun _ r => checkSelected r = true) 7936 256 ([
    P2Winner9CompleteSeedBlock31.pages[0]!,
    P2Winner9CompleteSeedBlock31.pages[1]!,
    P2Winner9CompleteSeedBlock31.pages[2]!,
    P2Winner9CompleteSeedBlock31.pages[3]!,
    P2Winner9CompleteSeedBlock31.pages[4]!,
    P2Winner9CompleteSeedBlock31.pages[5]!,
    P2Winner9CompleteSeedBlock31.pages[6]!,
    P2Winner9CompleteSeedBlock31.pages[7]!,
    P2Winner9CompleteSeedBlock31.pages[8]!,
    P2Winner9CompleteSeedBlock31.pages[9]!,
    P2Winner9CompleteSeedBlock31.pages[10]!,
    P2Winner9CompleteSeedBlock31.pages[11]!,
    P2Winner9CompleteSeedBlock31.pages[12]!,
    P2Winner9CompleteSeedBlock31.pages[13]!,
    P2Winner9CompleteSeedBlock31.pages[14]!,
    P2Winner9CompleteSeedBlock31.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0496.checked.flatten_cons <|
    P2Winner9NumericalPage0497.checked.flatten_cons <|
    P2Winner9NumericalPage0498.checked.flatten_cons <|
    P2Winner9NumericalPage0499.checked.flatten_cons <|
    P2Winner9NumericalPage0500.checked.flatten_cons <|
    P2Winner9NumericalPage0501.checked.flatten_cons <|
    P2Winner9NumericalPage0502.checked.flatten_cons <|
    P2Winner9NumericalPage0503.checked.flatten_cons <|
    P2Winner9NumericalPage0504.checked.flatten_cons <|
    P2Winner9NumericalPage0505.checked.flatten_cons <|
    P2Winner9NumericalPage0506.checked.flatten_cons <|
    P2Winner9NumericalPage0507.checked.flatten_cons <|
    P2Winner9NumericalPage0508.checked.flatten_cons <|
    P2Winner9NumericalPage0509.checked.flatten_cons <|
    P2Winner9NumericalPage0510.checked.flatten_cons <|
    P2Winner9NumericalPage0511.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck31
