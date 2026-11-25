import ImbalancedChen.P2Winner9NumericalPage0208
import ImbalancedChen.P2Winner9NumericalPage0209
import ImbalancedChen.P2Winner9NumericalPage0210
import ImbalancedChen.P2Winner9NumericalPage0211
import ImbalancedChen.P2Winner9NumericalPage0212
import ImbalancedChen.P2Winner9NumericalPage0213
import ImbalancedChen.P2Winner9NumericalPage0214
import ImbalancedChen.P2Winner9NumericalPage0215
import ImbalancedChen.P2Winner9NumericalPage0216
import ImbalancedChen.P2Winner9NumericalPage0217
import ImbalancedChen.P2Winner9NumericalPage0218
import ImbalancedChen.P2Winner9NumericalPage0219
import ImbalancedChen.P2Winner9NumericalPage0220
import ImbalancedChen.P2Winner9NumericalPage0221
import ImbalancedChen.P2Winner9NumericalPage0222
import ImbalancedChen.P2Winner9NumericalPage0223

namespace ImbalancedChen.P2Winner9NumericalCheck13
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 3328 256
    P2Winner9CompleteSeedBlock13.rows := by
  change Checked (fun _ r => checkSelected r = true) 3328 256 ([
    P2Winner9CompleteSeedBlock13.pages[0]!,
    P2Winner9CompleteSeedBlock13.pages[1]!,
    P2Winner9CompleteSeedBlock13.pages[2]!,
    P2Winner9CompleteSeedBlock13.pages[3]!,
    P2Winner9CompleteSeedBlock13.pages[4]!,
    P2Winner9CompleteSeedBlock13.pages[5]!,
    P2Winner9CompleteSeedBlock13.pages[6]!,
    P2Winner9CompleteSeedBlock13.pages[7]!,
    P2Winner9CompleteSeedBlock13.pages[8]!,
    P2Winner9CompleteSeedBlock13.pages[9]!,
    P2Winner9CompleteSeedBlock13.pages[10]!,
    P2Winner9CompleteSeedBlock13.pages[11]!,
    P2Winner9CompleteSeedBlock13.pages[12]!,
    P2Winner9CompleteSeedBlock13.pages[13]!,
    P2Winner9CompleteSeedBlock13.pages[14]!,
    P2Winner9CompleteSeedBlock13.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0208.checked.flatten_cons <|
    P2Winner9NumericalPage0209.checked.flatten_cons <|
    P2Winner9NumericalPage0210.checked.flatten_cons <|
    P2Winner9NumericalPage0211.checked.flatten_cons <|
    P2Winner9NumericalPage0212.checked.flatten_cons <|
    P2Winner9NumericalPage0213.checked.flatten_cons <|
    P2Winner9NumericalPage0214.checked.flatten_cons <|
    P2Winner9NumericalPage0215.checked.flatten_cons <|
    P2Winner9NumericalPage0216.checked.flatten_cons <|
    P2Winner9NumericalPage0217.checked.flatten_cons <|
    P2Winner9NumericalPage0218.checked.flatten_cons <|
    P2Winner9NumericalPage0219.checked.flatten_cons <|
    P2Winner9NumericalPage0220.checked.flatten_cons <|
    P2Winner9NumericalPage0221.checked.flatten_cons <|
    P2Winner9NumericalPage0222.checked.flatten_cons <|
    P2Winner9NumericalPage0223.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck13
