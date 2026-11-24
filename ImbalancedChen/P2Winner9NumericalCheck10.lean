import ImbalancedChen.P2Winner9NumericalPage0160
import ImbalancedChen.P2Winner9NumericalPage0161
import ImbalancedChen.P2Winner9NumericalPage0162
import ImbalancedChen.P2Winner9NumericalPage0163
import ImbalancedChen.P2Winner9NumericalPage0164
import ImbalancedChen.P2Winner9NumericalPage0165
import ImbalancedChen.P2Winner9NumericalPage0166
import ImbalancedChen.P2Winner9NumericalPage0167
import ImbalancedChen.P2Winner9NumericalPage0168
import ImbalancedChen.P2Winner9NumericalPage0169
import ImbalancedChen.P2Winner9NumericalPage0170
import ImbalancedChen.P2Winner9NumericalPage0171
import ImbalancedChen.P2Winner9NumericalPage0172
import ImbalancedChen.P2Winner9NumericalPage0173
import ImbalancedChen.P2Winner9NumericalPage0174
import ImbalancedChen.P2Winner9NumericalPage0175

namespace ImbalancedChen.P2Winner9NumericalCheck10
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 2560 256
    P2Winner9CompleteSeedBlock10.rows := by
  change Checked (fun _ r => checkSelected r = true) 2560 256 ([
    P2Winner9CompleteSeedBlock10.pages[0]!,
    P2Winner9CompleteSeedBlock10.pages[1]!,
    P2Winner9CompleteSeedBlock10.pages[2]!,
    P2Winner9CompleteSeedBlock10.pages[3]!,
    P2Winner9CompleteSeedBlock10.pages[4]!,
    P2Winner9CompleteSeedBlock10.pages[5]!,
    P2Winner9CompleteSeedBlock10.pages[6]!,
    P2Winner9CompleteSeedBlock10.pages[7]!,
    P2Winner9CompleteSeedBlock10.pages[8]!,
    P2Winner9CompleteSeedBlock10.pages[9]!,
    P2Winner9CompleteSeedBlock10.pages[10]!,
    P2Winner9CompleteSeedBlock10.pages[11]!,
    P2Winner9CompleteSeedBlock10.pages[12]!,
    P2Winner9CompleteSeedBlock10.pages[13]!,
    P2Winner9CompleteSeedBlock10.pages[14]!,
    P2Winner9CompleteSeedBlock10.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0160.checked.flatten_cons <|
    P2Winner9NumericalPage0161.checked.flatten_cons <|
    P2Winner9NumericalPage0162.checked.flatten_cons <|
    P2Winner9NumericalPage0163.checked.flatten_cons <|
    P2Winner9NumericalPage0164.checked.flatten_cons <|
    P2Winner9NumericalPage0165.checked.flatten_cons <|
    P2Winner9NumericalPage0166.checked.flatten_cons <|
    P2Winner9NumericalPage0167.checked.flatten_cons <|
    P2Winner9NumericalPage0168.checked.flatten_cons <|
    P2Winner9NumericalPage0169.checked.flatten_cons <|
    P2Winner9NumericalPage0170.checked.flatten_cons <|
    P2Winner9NumericalPage0171.checked.flatten_cons <|
    P2Winner9NumericalPage0172.checked.flatten_cons <|
    P2Winner9NumericalPage0173.checked.flatten_cons <|
    P2Winner9NumericalPage0174.checked.flatten_cons <|
    P2Winner9NumericalPage0175.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck10
