import ImbalancedChen.P2Winner9NumericalPage0016
import ImbalancedChen.P2Winner9NumericalPage0017
import ImbalancedChen.P2Winner9NumericalPage0018
import ImbalancedChen.P2Winner9NumericalPage0019
import ImbalancedChen.P2Winner9NumericalPage0020
import ImbalancedChen.P2Winner9NumericalPage0021
import ImbalancedChen.P2Winner9NumericalPage0022
import ImbalancedChen.P2Winner9NumericalPage0023
import ImbalancedChen.P2Winner9NumericalPage0024
import ImbalancedChen.P2Winner9NumericalPage0025
import ImbalancedChen.P2Winner9NumericalPage0026
import ImbalancedChen.P2Winner9NumericalPage0027
import ImbalancedChen.P2Winner9NumericalPage0028
import ImbalancedChen.P2Winner9NumericalPage0029
import ImbalancedChen.P2Winner9NumericalPage0030
import ImbalancedChen.P2Winner9NumericalPage0031

namespace ImbalancedChen.P2Winner9NumericalCheck01
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 256 256
    P2Winner9CompleteSeedBlock01.rows := by
  change Checked (fun _ r => checkSelected r = true) 256 256 ([
    P2Winner9CompleteSeedBlock01.pages[0]!,
    P2Winner9CompleteSeedBlock01.pages[1]!,
    P2Winner9CompleteSeedBlock01.pages[2]!,
    P2Winner9CompleteSeedBlock01.pages[3]!,
    P2Winner9CompleteSeedBlock01.pages[4]!,
    P2Winner9CompleteSeedBlock01.pages[5]!,
    P2Winner9CompleteSeedBlock01.pages[6]!,
    P2Winner9CompleteSeedBlock01.pages[7]!,
    P2Winner9CompleteSeedBlock01.pages[8]!,
    P2Winner9CompleteSeedBlock01.pages[9]!,
    P2Winner9CompleteSeedBlock01.pages[10]!,
    P2Winner9CompleteSeedBlock01.pages[11]!,
    P2Winner9CompleteSeedBlock01.pages[12]!,
    P2Winner9CompleteSeedBlock01.pages[13]!,
    P2Winner9CompleteSeedBlock01.pages[14]!,
    P2Winner9CompleteSeedBlock01.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0016.checked.flatten_cons <|
    P2Winner9NumericalPage0017.checked.flatten_cons <|
    P2Winner9NumericalPage0018.checked.flatten_cons <|
    P2Winner9NumericalPage0019.checked.flatten_cons <|
    P2Winner9NumericalPage0020.checked.flatten_cons <|
    P2Winner9NumericalPage0021.checked.flatten_cons <|
    P2Winner9NumericalPage0022.checked.flatten_cons <|
    P2Winner9NumericalPage0023.checked.flatten_cons <|
    P2Winner9NumericalPage0024.checked.flatten_cons <|
    P2Winner9NumericalPage0025.checked.flatten_cons <|
    P2Winner9NumericalPage0026.checked.flatten_cons <|
    P2Winner9NumericalPage0027.checked.flatten_cons <|
    P2Winner9NumericalPage0028.checked.flatten_cons <|
    P2Winner9NumericalPage0029.checked.flatten_cons <|
    P2Winner9NumericalPage0030.checked.flatten_cons <|
    P2Winner9NumericalPage0031.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck01
