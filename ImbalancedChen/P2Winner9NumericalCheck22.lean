import ImbalancedChen.P2Winner9NumericalPage0352
import ImbalancedChen.P2Winner9NumericalPage0353
import ImbalancedChen.P2Winner9NumericalPage0354
import ImbalancedChen.P2Winner9NumericalPage0355
import ImbalancedChen.P2Winner9NumericalPage0356
import ImbalancedChen.P2Winner9NumericalPage0357
import ImbalancedChen.P2Winner9NumericalPage0358
import ImbalancedChen.P2Winner9NumericalPage0359
import ImbalancedChen.P2Winner9NumericalPage0360
import ImbalancedChen.P2Winner9NumericalPage0361
import ImbalancedChen.P2Winner9NumericalPage0362
import ImbalancedChen.P2Winner9NumericalPage0363
import ImbalancedChen.P2Winner9NumericalPage0364
import ImbalancedChen.P2Winner9NumericalPage0365
import ImbalancedChen.P2Winner9NumericalPage0366
import ImbalancedChen.P2Winner9NumericalPage0367

namespace ImbalancedChen.P2Winner9NumericalCheck22
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 5632 256
    P2Winner9CompleteSeedBlock22.rows := by
  change Checked (fun _ r => checkSelected r = true) 5632 256 ([
    P2Winner9CompleteSeedBlock22.pages[0]!,
    P2Winner9CompleteSeedBlock22.pages[1]!,
    P2Winner9CompleteSeedBlock22.pages[2]!,
    P2Winner9CompleteSeedBlock22.pages[3]!,
    P2Winner9CompleteSeedBlock22.pages[4]!,
    P2Winner9CompleteSeedBlock22.pages[5]!,
    P2Winner9CompleteSeedBlock22.pages[6]!,
    P2Winner9CompleteSeedBlock22.pages[7]!,
    P2Winner9CompleteSeedBlock22.pages[8]!,
    P2Winner9CompleteSeedBlock22.pages[9]!,
    P2Winner9CompleteSeedBlock22.pages[10]!,
    P2Winner9CompleteSeedBlock22.pages[11]!,
    P2Winner9CompleteSeedBlock22.pages[12]!,
    P2Winner9CompleteSeedBlock22.pages[13]!,
    P2Winner9CompleteSeedBlock22.pages[14]!,
    P2Winner9CompleteSeedBlock22.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0352.checked.flatten_cons <|
    P2Winner9NumericalPage0353.checked.flatten_cons <|
    P2Winner9NumericalPage0354.checked.flatten_cons <|
    P2Winner9NumericalPage0355.checked.flatten_cons <|
    P2Winner9NumericalPage0356.checked.flatten_cons <|
    P2Winner9NumericalPage0357.checked.flatten_cons <|
    P2Winner9NumericalPage0358.checked.flatten_cons <|
    P2Winner9NumericalPage0359.checked.flatten_cons <|
    P2Winner9NumericalPage0360.checked.flatten_cons <|
    P2Winner9NumericalPage0361.checked.flatten_cons <|
    P2Winner9NumericalPage0362.checked.flatten_cons <|
    P2Winner9NumericalPage0363.checked.flatten_cons <|
    P2Winner9NumericalPage0364.checked.flatten_cons <|
    P2Winner9NumericalPage0365.checked.flatten_cons <|
    P2Winner9NumericalPage0366.checked.flatten_cons <|
    P2Winner9NumericalPage0367.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck22
