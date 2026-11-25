import ImbalancedChen.P2Winner9NumericalPage0096
import ImbalancedChen.P2Winner9NumericalPage0097
import ImbalancedChen.P2Winner9NumericalPage0098
import ImbalancedChen.P2Winner9NumericalPage0099
import ImbalancedChen.P2Winner9NumericalPage0100
import ImbalancedChen.P2Winner9NumericalPage0101
import ImbalancedChen.P2Winner9NumericalPage0102
import ImbalancedChen.P2Winner9NumericalPage0103
import ImbalancedChen.P2Winner9NumericalPage0104
import ImbalancedChen.P2Winner9NumericalPage0105
import ImbalancedChen.P2Winner9NumericalPage0106
import ImbalancedChen.P2Winner9NumericalPage0107
import ImbalancedChen.P2Winner9NumericalPage0108
import ImbalancedChen.P2Winner9NumericalPage0109
import ImbalancedChen.P2Winner9NumericalPage0110
import ImbalancedChen.P2Winner9NumericalPage0111

namespace ImbalancedChen.P2Winner9NumericalCheck06
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 1536 256
    P2Winner9CompleteSeedBlock06.rows := by
  change Checked (fun _ r => checkSelected r = true) 1536 256 ([
    P2Winner9CompleteSeedBlock06.pages[0]!,
    P2Winner9CompleteSeedBlock06.pages[1]!,
    P2Winner9CompleteSeedBlock06.pages[2]!,
    P2Winner9CompleteSeedBlock06.pages[3]!,
    P2Winner9CompleteSeedBlock06.pages[4]!,
    P2Winner9CompleteSeedBlock06.pages[5]!,
    P2Winner9CompleteSeedBlock06.pages[6]!,
    P2Winner9CompleteSeedBlock06.pages[7]!,
    P2Winner9CompleteSeedBlock06.pages[8]!,
    P2Winner9CompleteSeedBlock06.pages[9]!,
    P2Winner9CompleteSeedBlock06.pages[10]!,
    P2Winner9CompleteSeedBlock06.pages[11]!,
    P2Winner9CompleteSeedBlock06.pages[12]!,
    P2Winner9CompleteSeedBlock06.pages[13]!,
    P2Winner9CompleteSeedBlock06.pages[14]!,
    P2Winner9CompleteSeedBlock06.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0096.checked.flatten_cons <|
    P2Winner9NumericalPage0097.checked.flatten_cons <|
    P2Winner9NumericalPage0098.checked.flatten_cons <|
    P2Winner9NumericalPage0099.checked.flatten_cons <|
    P2Winner9NumericalPage0100.checked.flatten_cons <|
    P2Winner9NumericalPage0101.checked.flatten_cons <|
    P2Winner9NumericalPage0102.checked.flatten_cons <|
    P2Winner9NumericalPage0103.checked.flatten_cons <|
    P2Winner9NumericalPage0104.checked.flatten_cons <|
    P2Winner9NumericalPage0105.checked.flatten_cons <|
    P2Winner9NumericalPage0106.checked.flatten_cons <|
    P2Winner9NumericalPage0107.checked.flatten_cons <|
    P2Winner9NumericalPage0108.checked.flatten_cons <|
    P2Winner9NumericalPage0109.checked.flatten_cons <|
    P2Winner9NumericalPage0110.checked.flatten_cons <|
    P2Winner9NumericalPage0111.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck06
