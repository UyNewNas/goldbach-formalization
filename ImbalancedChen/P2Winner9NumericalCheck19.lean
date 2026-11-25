import ImbalancedChen.P2Winner9NumericalPage0304
import ImbalancedChen.P2Winner9NumericalPage0305
import ImbalancedChen.P2Winner9NumericalPage0306
import ImbalancedChen.P2Winner9NumericalPage0307
import ImbalancedChen.P2Winner9NumericalPage0308
import ImbalancedChen.P2Winner9NumericalPage0309
import ImbalancedChen.P2Winner9NumericalPage0310
import ImbalancedChen.P2Winner9NumericalPage0311
import ImbalancedChen.P2Winner9NumericalPage0312
import ImbalancedChen.P2Winner9NumericalPage0313
import ImbalancedChen.P2Winner9NumericalPage0314
import ImbalancedChen.P2Winner9NumericalPage0315
import ImbalancedChen.P2Winner9NumericalPage0316
import ImbalancedChen.P2Winner9NumericalPage0317
import ImbalancedChen.P2Winner9NumericalPage0318
import ImbalancedChen.P2Winner9NumericalPage0319

namespace ImbalancedChen.P2Winner9NumericalCheck19
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 4864 256
    P2Winner9CompleteSeedBlock19.rows := by
  change Checked (fun _ r => checkSelected r = true) 4864 256 ([
    P2Winner9CompleteSeedBlock19.pages[0]!,
    P2Winner9CompleteSeedBlock19.pages[1]!,
    P2Winner9CompleteSeedBlock19.pages[2]!,
    P2Winner9CompleteSeedBlock19.pages[3]!,
    P2Winner9CompleteSeedBlock19.pages[4]!,
    P2Winner9CompleteSeedBlock19.pages[5]!,
    P2Winner9CompleteSeedBlock19.pages[6]!,
    P2Winner9CompleteSeedBlock19.pages[7]!,
    P2Winner9CompleteSeedBlock19.pages[8]!,
    P2Winner9CompleteSeedBlock19.pages[9]!,
    P2Winner9CompleteSeedBlock19.pages[10]!,
    P2Winner9CompleteSeedBlock19.pages[11]!,
    P2Winner9CompleteSeedBlock19.pages[12]!,
    P2Winner9CompleteSeedBlock19.pages[13]!,
    P2Winner9CompleteSeedBlock19.pages[14]!,
    P2Winner9CompleteSeedBlock19.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0304.checked.flatten_cons <|
    P2Winner9NumericalPage0305.checked.flatten_cons <|
    P2Winner9NumericalPage0306.checked.flatten_cons <|
    P2Winner9NumericalPage0307.checked.flatten_cons <|
    P2Winner9NumericalPage0308.checked.flatten_cons <|
    P2Winner9NumericalPage0309.checked.flatten_cons <|
    P2Winner9NumericalPage0310.checked.flatten_cons <|
    P2Winner9NumericalPage0311.checked.flatten_cons <|
    P2Winner9NumericalPage0312.checked.flatten_cons <|
    P2Winner9NumericalPage0313.checked.flatten_cons <|
    P2Winner9NumericalPage0314.checked.flatten_cons <|
    P2Winner9NumericalPage0315.checked.flatten_cons <|
    P2Winner9NumericalPage0316.checked.flatten_cons <|
    P2Winner9NumericalPage0317.checked.flatten_cons <|
    P2Winner9NumericalPage0318.checked.flatten_cons <|
    P2Winner9NumericalPage0319.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck19
