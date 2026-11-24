import ImbalancedChen.P2Winner9NumericalPage0256
import ImbalancedChen.P2Winner9NumericalPage0257
import ImbalancedChen.P2Winner9NumericalPage0258
import ImbalancedChen.P2Winner9NumericalPage0259
import ImbalancedChen.P2Winner9NumericalPage0260
import ImbalancedChen.P2Winner9NumericalPage0261
import ImbalancedChen.P2Winner9NumericalPage0262
import ImbalancedChen.P2Winner9NumericalPage0263
import ImbalancedChen.P2Winner9NumericalPage0264
import ImbalancedChen.P2Winner9NumericalPage0265
import ImbalancedChen.P2Winner9NumericalPage0266
import ImbalancedChen.P2Winner9NumericalPage0267
import ImbalancedChen.P2Winner9NumericalPage0268
import ImbalancedChen.P2Winner9NumericalPage0269
import ImbalancedChen.P2Winner9NumericalPage0270
import ImbalancedChen.P2Winner9NumericalPage0271

namespace ImbalancedChen.P2Winner9NumericalCheck16
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 4096 256
    P2Winner9CompleteSeedBlock16.rows := by
  change Checked (fun _ r => checkSelected r = true) 4096 256 ([
    P2Winner9CompleteSeedBlock16.pages[0]!,
    P2Winner9CompleteSeedBlock16.pages[1]!,
    P2Winner9CompleteSeedBlock16.pages[2]!,
    P2Winner9CompleteSeedBlock16.pages[3]!,
    P2Winner9CompleteSeedBlock16.pages[4]!,
    P2Winner9CompleteSeedBlock16.pages[5]!,
    P2Winner9CompleteSeedBlock16.pages[6]!,
    P2Winner9CompleteSeedBlock16.pages[7]!,
    P2Winner9CompleteSeedBlock16.pages[8]!,
    P2Winner9CompleteSeedBlock16.pages[9]!,
    P2Winner9CompleteSeedBlock16.pages[10]!,
    P2Winner9CompleteSeedBlock16.pages[11]!,
    P2Winner9CompleteSeedBlock16.pages[12]!,
    P2Winner9CompleteSeedBlock16.pages[13]!,
    P2Winner9CompleteSeedBlock16.pages[14]!,
    P2Winner9CompleteSeedBlock16.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0256.checked.flatten_cons <|
    P2Winner9NumericalPage0257.checked.flatten_cons <|
    P2Winner9NumericalPage0258.checked.flatten_cons <|
    P2Winner9NumericalPage0259.checked.flatten_cons <|
    P2Winner9NumericalPage0260.checked.flatten_cons <|
    P2Winner9NumericalPage0261.checked.flatten_cons <|
    P2Winner9NumericalPage0262.checked.flatten_cons <|
    P2Winner9NumericalPage0263.checked.flatten_cons <|
    P2Winner9NumericalPage0264.checked.flatten_cons <|
    P2Winner9NumericalPage0265.checked.flatten_cons <|
    P2Winner9NumericalPage0266.checked.flatten_cons <|
    P2Winner9NumericalPage0267.checked.flatten_cons <|
    P2Winner9NumericalPage0268.checked.flatten_cons <|
    P2Winner9NumericalPage0269.checked.flatten_cons <|
    P2Winner9NumericalPage0270.checked.flatten_cons <|
    P2Winner9NumericalPage0271.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck16
