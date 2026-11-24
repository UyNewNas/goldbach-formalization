import ImbalancedChen.P2Winner9NumericalPage0448
import ImbalancedChen.P2Winner9NumericalPage0449
import ImbalancedChen.P2Winner9NumericalPage0450
import ImbalancedChen.P2Winner9NumericalPage0451
import ImbalancedChen.P2Winner9NumericalPage0452
import ImbalancedChen.P2Winner9NumericalPage0453
import ImbalancedChen.P2Winner9NumericalPage0454
import ImbalancedChen.P2Winner9NumericalPage0455
import ImbalancedChen.P2Winner9NumericalPage0456
import ImbalancedChen.P2Winner9NumericalPage0457
import ImbalancedChen.P2Winner9NumericalPage0458
import ImbalancedChen.P2Winner9NumericalPage0459
import ImbalancedChen.P2Winner9NumericalPage0460
import ImbalancedChen.P2Winner9NumericalPage0461
import ImbalancedChen.P2Winner9NumericalPage0462
import ImbalancedChen.P2Winner9NumericalPage0463

namespace ImbalancedChen.P2Winner9NumericalCheck28
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 7168 256
    P2Winner9CompleteSeedBlock28.rows := by
  change Checked (fun _ r => checkSelected r = true) 7168 256 ([
    P2Winner9CompleteSeedBlock28.pages[0]!,
    P2Winner9CompleteSeedBlock28.pages[1]!,
    P2Winner9CompleteSeedBlock28.pages[2]!,
    P2Winner9CompleteSeedBlock28.pages[3]!,
    P2Winner9CompleteSeedBlock28.pages[4]!,
    P2Winner9CompleteSeedBlock28.pages[5]!,
    P2Winner9CompleteSeedBlock28.pages[6]!,
    P2Winner9CompleteSeedBlock28.pages[7]!,
    P2Winner9CompleteSeedBlock28.pages[8]!,
    P2Winner9CompleteSeedBlock28.pages[9]!,
    P2Winner9CompleteSeedBlock28.pages[10]!,
    P2Winner9CompleteSeedBlock28.pages[11]!,
    P2Winner9CompleteSeedBlock28.pages[12]!,
    P2Winner9CompleteSeedBlock28.pages[13]!,
    P2Winner9CompleteSeedBlock28.pages[14]!,
    P2Winner9CompleteSeedBlock28.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0448.checked.flatten_cons <|
    P2Winner9NumericalPage0449.checked.flatten_cons <|
    P2Winner9NumericalPage0450.checked.flatten_cons <|
    P2Winner9NumericalPage0451.checked.flatten_cons <|
    P2Winner9NumericalPage0452.checked.flatten_cons <|
    P2Winner9NumericalPage0453.checked.flatten_cons <|
    P2Winner9NumericalPage0454.checked.flatten_cons <|
    P2Winner9NumericalPage0455.checked.flatten_cons <|
    P2Winner9NumericalPage0456.checked.flatten_cons <|
    P2Winner9NumericalPage0457.checked.flatten_cons <|
    P2Winner9NumericalPage0458.checked.flatten_cons <|
    P2Winner9NumericalPage0459.checked.flatten_cons <|
    P2Winner9NumericalPage0460.checked.flatten_cons <|
    P2Winner9NumericalPage0461.checked.flatten_cons <|
    P2Winner9NumericalPage0462.checked.flatten_cons <|
    P2Winner9NumericalPage0463.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck28
