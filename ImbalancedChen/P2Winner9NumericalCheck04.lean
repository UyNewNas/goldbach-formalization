import ImbalancedChen.P2Winner9NumericalPage0064
import ImbalancedChen.P2Winner9NumericalPage0065
import ImbalancedChen.P2Winner9NumericalPage0066
import ImbalancedChen.P2Winner9NumericalPage0067
import ImbalancedChen.P2Winner9NumericalPage0068
import ImbalancedChen.P2Winner9NumericalPage0069
import ImbalancedChen.P2Winner9NumericalPage0070
import ImbalancedChen.P2Winner9NumericalPage0071
import ImbalancedChen.P2Winner9NumericalPage0072
import ImbalancedChen.P2Winner9NumericalPage0073
import ImbalancedChen.P2Winner9NumericalPage0074
import ImbalancedChen.P2Winner9NumericalPage0075
import ImbalancedChen.P2Winner9NumericalPage0076
import ImbalancedChen.P2Winner9NumericalPage0077
import ImbalancedChen.P2Winner9NumericalPage0078
import ImbalancedChen.P2Winner9NumericalPage0079

namespace ImbalancedChen.P2Winner9NumericalCheck04
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 1024 256
    P2Winner9CompleteSeedBlock04.rows := by
  change Checked (fun _ r => checkSelected r = true) 1024 256 ([
    P2Winner9CompleteSeedBlock04.pages[0]!,
    P2Winner9CompleteSeedBlock04.pages[1]!,
    P2Winner9CompleteSeedBlock04.pages[2]!,
    P2Winner9CompleteSeedBlock04.pages[3]!,
    P2Winner9CompleteSeedBlock04.pages[4]!,
    P2Winner9CompleteSeedBlock04.pages[5]!,
    P2Winner9CompleteSeedBlock04.pages[6]!,
    P2Winner9CompleteSeedBlock04.pages[7]!,
    P2Winner9CompleteSeedBlock04.pages[8]!,
    P2Winner9CompleteSeedBlock04.pages[9]!,
    P2Winner9CompleteSeedBlock04.pages[10]!,
    P2Winner9CompleteSeedBlock04.pages[11]!,
    P2Winner9CompleteSeedBlock04.pages[12]!,
    P2Winner9CompleteSeedBlock04.pages[13]!,
    P2Winner9CompleteSeedBlock04.pages[14]!,
    P2Winner9CompleteSeedBlock04.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0064.checked.flatten_cons <|
    P2Winner9NumericalPage0065.checked.flatten_cons <|
    P2Winner9NumericalPage0066.checked.flatten_cons <|
    P2Winner9NumericalPage0067.checked.flatten_cons <|
    P2Winner9NumericalPage0068.checked.flatten_cons <|
    P2Winner9NumericalPage0069.checked.flatten_cons <|
    P2Winner9NumericalPage0070.checked.flatten_cons <|
    P2Winner9NumericalPage0071.checked.flatten_cons <|
    P2Winner9NumericalPage0072.checked.flatten_cons <|
    P2Winner9NumericalPage0073.checked.flatten_cons <|
    P2Winner9NumericalPage0074.checked.flatten_cons <|
    P2Winner9NumericalPage0075.checked.flatten_cons <|
    P2Winner9NumericalPage0076.checked.flatten_cons <|
    P2Winner9NumericalPage0077.checked.flatten_cons <|
    P2Winner9NumericalPage0078.checked.flatten_cons <|
    P2Winner9NumericalPage0079.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck04
