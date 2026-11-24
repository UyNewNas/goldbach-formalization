import ImbalancedChen.P2Winner9NumericalPage0080
import ImbalancedChen.P2Winner9NumericalPage0081
import ImbalancedChen.P2Winner9NumericalPage0082
import ImbalancedChen.P2Winner9NumericalPage0083
import ImbalancedChen.P2Winner9NumericalPage0084
import ImbalancedChen.P2Winner9NumericalPage0085
import ImbalancedChen.P2Winner9NumericalPage0086
import ImbalancedChen.P2Winner9NumericalPage0087
import ImbalancedChen.P2Winner9NumericalPage0088
import ImbalancedChen.P2Winner9NumericalPage0089
import ImbalancedChen.P2Winner9NumericalPage0090
import ImbalancedChen.P2Winner9NumericalPage0091
import ImbalancedChen.P2Winner9NumericalPage0092
import ImbalancedChen.P2Winner9NumericalPage0093
import ImbalancedChen.P2Winner9NumericalPage0094
import ImbalancedChen.P2Winner9NumericalPage0095

namespace ImbalancedChen.P2Winner9NumericalCheck05
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 1280 256
    P2Winner9CompleteSeedBlock05.rows := by
  change Checked (fun _ r => checkSelected r = true) 1280 256 ([
    P2Winner9CompleteSeedBlock05.pages[0]!,
    P2Winner9CompleteSeedBlock05.pages[1]!,
    P2Winner9CompleteSeedBlock05.pages[2]!,
    P2Winner9CompleteSeedBlock05.pages[3]!,
    P2Winner9CompleteSeedBlock05.pages[4]!,
    P2Winner9CompleteSeedBlock05.pages[5]!,
    P2Winner9CompleteSeedBlock05.pages[6]!,
    P2Winner9CompleteSeedBlock05.pages[7]!,
    P2Winner9CompleteSeedBlock05.pages[8]!,
    P2Winner9CompleteSeedBlock05.pages[9]!,
    P2Winner9CompleteSeedBlock05.pages[10]!,
    P2Winner9CompleteSeedBlock05.pages[11]!,
    P2Winner9CompleteSeedBlock05.pages[12]!,
    P2Winner9CompleteSeedBlock05.pages[13]!,
    P2Winner9CompleteSeedBlock05.pages[14]!,
    P2Winner9CompleteSeedBlock05.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0080.checked.flatten_cons <|
    P2Winner9NumericalPage0081.checked.flatten_cons <|
    P2Winner9NumericalPage0082.checked.flatten_cons <|
    P2Winner9NumericalPage0083.checked.flatten_cons <|
    P2Winner9NumericalPage0084.checked.flatten_cons <|
    P2Winner9NumericalPage0085.checked.flatten_cons <|
    P2Winner9NumericalPage0086.checked.flatten_cons <|
    P2Winner9NumericalPage0087.checked.flatten_cons <|
    P2Winner9NumericalPage0088.checked.flatten_cons <|
    P2Winner9NumericalPage0089.checked.flatten_cons <|
    P2Winner9NumericalPage0090.checked.flatten_cons <|
    P2Winner9NumericalPage0091.checked.flatten_cons <|
    P2Winner9NumericalPage0092.checked.flatten_cons <|
    P2Winner9NumericalPage0093.checked.flatten_cons <|
    P2Winner9NumericalPage0094.checked.flatten_cons <|
    P2Winner9NumericalPage0095.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck05
