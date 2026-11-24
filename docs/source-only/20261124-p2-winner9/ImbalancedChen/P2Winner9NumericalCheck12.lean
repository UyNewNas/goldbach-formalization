import ImbalancedChen.P2Winner9NumericalPage0192
import ImbalancedChen.P2Winner9NumericalPage0193
import ImbalancedChen.P2Winner9NumericalPage0194
import ImbalancedChen.P2Winner9NumericalPage0195
import ImbalancedChen.P2Winner9NumericalPage0196
import ImbalancedChen.P2Winner9NumericalPage0197
import ImbalancedChen.P2Winner9NumericalPage0198
import ImbalancedChen.P2Winner9NumericalPage0199
import ImbalancedChen.P2Winner9NumericalPage0200
import ImbalancedChen.P2Winner9NumericalPage0201
import ImbalancedChen.P2Winner9NumericalPage0202
import ImbalancedChen.P2Winner9NumericalPage0203
import ImbalancedChen.P2Winner9NumericalPage0204
import ImbalancedChen.P2Winner9NumericalPage0205
import ImbalancedChen.P2Winner9NumericalPage0206
import ImbalancedChen.P2Winner9NumericalPage0207

namespace ImbalancedChen.P2Winner9NumericalCheck12
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 3072 256
    P2Winner9CompleteSeedBlock12.rows := by
  change Checked (fun _ r => checkSelected r = true) 3072 256 ([
    P2Winner9CompleteSeedBlock12.pages[0]!,
    P2Winner9CompleteSeedBlock12.pages[1]!,
    P2Winner9CompleteSeedBlock12.pages[2]!,
    P2Winner9CompleteSeedBlock12.pages[3]!,
    P2Winner9CompleteSeedBlock12.pages[4]!,
    P2Winner9CompleteSeedBlock12.pages[5]!,
    P2Winner9CompleteSeedBlock12.pages[6]!,
    P2Winner9CompleteSeedBlock12.pages[7]!,
    P2Winner9CompleteSeedBlock12.pages[8]!,
    P2Winner9CompleteSeedBlock12.pages[9]!,
    P2Winner9CompleteSeedBlock12.pages[10]!,
    P2Winner9CompleteSeedBlock12.pages[11]!,
    P2Winner9CompleteSeedBlock12.pages[12]!,
    P2Winner9CompleteSeedBlock12.pages[13]!,
    P2Winner9CompleteSeedBlock12.pages[14]!,
    P2Winner9CompleteSeedBlock12.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0192.checked.flatten_cons <|
    P2Winner9NumericalPage0193.checked.flatten_cons <|
    P2Winner9NumericalPage0194.checked.flatten_cons <|
    P2Winner9NumericalPage0195.checked.flatten_cons <|
    P2Winner9NumericalPage0196.checked.flatten_cons <|
    P2Winner9NumericalPage0197.checked.flatten_cons <|
    P2Winner9NumericalPage0198.checked.flatten_cons <|
    P2Winner9NumericalPage0199.checked.flatten_cons <|
    P2Winner9NumericalPage0200.checked.flatten_cons <|
    P2Winner9NumericalPage0201.checked.flatten_cons <|
    P2Winner9NumericalPage0202.checked.flatten_cons <|
    P2Winner9NumericalPage0203.checked.flatten_cons <|
    P2Winner9NumericalPage0204.checked.flatten_cons <|
    P2Winner9NumericalPage0205.checked.flatten_cons <|
    P2Winner9NumericalPage0206.checked.flatten_cons <|
    P2Winner9NumericalPage0207.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck12
