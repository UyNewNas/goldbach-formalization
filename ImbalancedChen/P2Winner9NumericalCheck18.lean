import ImbalancedChen.P2Winner9NumericalPage0288
import ImbalancedChen.P2Winner9NumericalPage0289
import ImbalancedChen.P2Winner9NumericalPage0290
import ImbalancedChen.P2Winner9NumericalPage0291
import ImbalancedChen.P2Winner9NumericalPage0292
import ImbalancedChen.P2Winner9NumericalPage0293
import ImbalancedChen.P2Winner9NumericalPage0294
import ImbalancedChen.P2Winner9NumericalPage0295
import ImbalancedChen.P2Winner9NumericalPage0296
import ImbalancedChen.P2Winner9NumericalPage0297
import ImbalancedChen.P2Winner9NumericalPage0298
import ImbalancedChen.P2Winner9NumericalPage0299
import ImbalancedChen.P2Winner9NumericalPage0300
import ImbalancedChen.P2Winner9NumericalPage0301
import ImbalancedChen.P2Winner9NumericalPage0302
import ImbalancedChen.P2Winner9NumericalPage0303

namespace ImbalancedChen.P2Winner9NumericalCheck18
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 4608 256
    P2Winner9CompleteSeedBlock18.rows := by
  change Checked (fun _ r => checkSelected r = true) 4608 256 ([
    P2Winner9CompleteSeedBlock18.pages[0]!,
    P2Winner9CompleteSeedBlock18.pages[1]!,
    P2Winner9CompleteSeedBlock18.pages[2]!,
    P2Winner9CompleteSeedBlock18.pages[3]!,
    P2Winner9CompleteSeedBlock18.pages[4]!,
    P2Winner9CompleteSeedBlock18.pages[5]!,
    P2Winner9CompleteSeedBlock18.pages[6]!,
    P2Winner9CompleteSeedBlock18.pages[7]!,
    P2Winner9CompleteSeedBlock18.pages[8]!,
    P2Winner9CompleteSeedBlock18.pages[9]!,
    P2Winner9CompleteSeedBlock18.pages[10]!,
    P2Winner9CompleteSeedBlock18.pages[11]!,
    P2Winner9CompleteSeedBlock18.pages[12]!,
    P2Winner9CompleteSeedBlock18.pages[13]!,
    P2Winner9CompleteSeedBlock18.pages[14]!,
    P2Winner9CompleteSeedBlock18.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0288.checked.flatten_cons <|
    P2Winner9NumericalPage0289.checked.flatten_cons <|
    P2Winner9NumericalPage0290.checked.flatten_cons <|
    P2Winner9NumericalPage0291.checked.flatten_cons <|
    P2Winner9NumericalPage0292.checked.flatten_cons <|
    P2Winner9NumericalPage0293.checked.flatten_cons <|
    P2Winner9NumericalPage0294.checked.flatten_cons <|
    P2Winner9NumericalPage0295.checked.flatten_cons <|
    P2Winner9NumericalPage0296.checked.flatten_cons <|
    P2Winner9NumericalPage0297.checked.flatten_cons <|
    P2Winner9NumericalPage0298.checked.flatten_cons <|
    P2Winner9NumericalPage0299.checked.flatten_cons <|
    P2Winner9NumericalPage0300.checked.flatten_cons <|
    P2Winner9NumericalPage0301.checked.flatten_cons <|
    P2Winner9NumericalPage0302.checked.flatten_cons <|
    P2Winner9NumericalPage0303.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck18
