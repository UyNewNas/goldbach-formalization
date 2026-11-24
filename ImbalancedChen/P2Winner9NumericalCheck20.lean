import ImbalancedChen.P2Winner9NumericalPage0320
import ImbalancedChen.P2Winner9NumericalPage0321
import ImbalancedChen.P2Winner9NumericalPage0322
import ImbalancedChen.P2Winner9NumericalPage0323
import ImbalancedChen.P2Winner9NumericalPage0324
import ImbalancedChen.P2Winner9NumericalPage0325
import ImbalancedChen.P2Winner9NumericalPage0326
import ImbalancedChen.P2Winner9NumericalPage0327
import ImbalancedChen.P2Winner9NumericalPage0328
import ImbalancedChen.P2Winner9NumericalPage0329
import ImbalancedChen.P2Winner9NumericalPage0330
import ImbalancedChen.P2Winner9NumericalPage0331
import ImbalancedChen.P2Winner9NumericalPage0332
import ImbalancedChen.P2Winner9NumericalPage0333
import ImbalancedChen.P2Winner9NumericalPage0334
import ImbalancedChen.P2Winner9NumericalPage0335

namespace ImbalancedChen.P2Winner9NumericalCheck20
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 5120 256
    P2Winner9CompleteSeedBlock20.rows := by
  change Checked (fun _ r => checkSelected r = true) 5120 256 ([
    P2Winner9CompleteSeedBlock20.pages[0]!,
    P2Winner9CompleteSeedBlock20.pages[1]!,
    P2Winner9CompleteSeedBlock20.pages[2]!,
    P2Winner9CompleteSeedBlock20.pages[3]!,
    P2Winner9CompleteSeedBlock20.pages[4]!,
    P2Winner9CompleteSeedBlock20.pages[5]!,
    P2Winner9CompleteSeedBlock20.pages[6]!,
    P2Winner9CompleteSeedBlock20.pages[7]!,
    P2Winner9CompleteSeedBlock20.pages[8]!,
    P2Winner9CompleteSeedBlock20.pages[9]!,
    P2Winner9CompleteSeedBlock20.pages[10]!,
    P2Winner9CompleteSeedBlock20.pages[11]!,
    P2Winner9CompleteSeedBlock20.pages[12]!,
    P2Winner9CompleteSeedBlock20.pages[13]!,
    P2Winner9CompleteSeedBlock20.pages[14]!,
    P2Winner9CompleteSeedBlock20.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0320.checked.flatten_cons <|
    P2Winner9NumericalPage0321.checked.flatten_cons <|
    P2Winner9NumericalPage0322.checked.flatten_cons <|
    P2Winner9NumericalPage0323.checked.flatten_cons <|
    P2Winner9NumericalPage0324.checked.flatten_cons <|
    P2Winner9NumericalPage0325.checked.flatten_cons <|
    P2Winner9NumericalPage0326.checked.flatten_cons <|
    P2Winner9NumericalPage0327.checked.flatten_cons <|
    P2Winner9NumericalPage0328.checked.flatten_cons <|
    P2Winner9NumericalPage0329.checked.flatten_cons <|
    P2Winner9NumericalPage0330.checked.flatten_cons <|
    P2Winner9NumericalPage0331.checked.flatten_cons <|
    P2Winner9NumericalPage0332.checked.flatten_cons <|
    P2Winner9NumericalPage0333.checked.flatten_cons <|
    P2Winner9NumericalPage0334.checked.flatten_cons <|
    P2Winner9NumericalPage0335.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck20
