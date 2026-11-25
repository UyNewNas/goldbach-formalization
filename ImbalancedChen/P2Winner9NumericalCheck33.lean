import ImbalancedChen.P2Winner9NumericalPage0528
import ImbalancedChen.P2Winner9NumericalPage0529
import ImbalancedChen.P2Winner9NumericalPage0530
import ImbalancedChen.P2Winner9NumericalPage0531
import ImbalancedChen.P2Winner9NumericalPage0532
import ImbalancedChen.P2Winner9NumericalPage0533
import ImbalancedChen.P2Winner9NumericalPage0534
import ImbalancedChen.P2Winner9NumericalPage0535
import ImbalancedChen.P2Winner9NumericalPage0536
import ImbalancedChen.P2Winner9NumericalPage0537
import ImbalancedChen.P2Winner9NumericalPage0538
import ImbalancedChen.P2Winner9NumericalPage0539
import ImbalancedChen.P2Winner9NumericalPage0540
import ImbalancedChen.P2Winner9NumericalPage0541
import ImbalancedChen.P2Winner9NumericalPage0542
import ImbalancedChen.P2Winner9NumericalPage0543

namespace ImbalancedChen.P2Winner9NumericalCheck33
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 8448 256
    P2Winner9CompleteSeedBlock33.rows := by
  change Checked (fun _ r => checkSelected r = true) 8448 256 ([
    P2Winner9CompleteSeedBlock33.pages[0]!,
    P2Winner9CompleteSeedBlock33.pages[1]!,
    P2Winner9CompleteSeedBlock33.pages[2]!,
    P2Winner9CompleteSeedBlock33.pages[3]!,
    P2Winner9CompleteSeedBlock33.pages[4]!,
    P2Winner9CompleteSeedBlock33.pages[5]!,
    P2Winner9CompleteSeedBlock33.pages[6]!,
    P2Winner9CompleteSeedBlock33.pages[7]!,
    P2Winner9CompleteSeedBlock33.pages[8]!,
    P2Winner9CompleteSeedBlock33.pages[9]!,
    P2Winner9CompleteSeedBlock33.pages[10]!,
    P2Winner9CompleteSeedBlock33.pages[11]!,
    P2Winner9CompleteSeedBlock33.pages[12]!,
    P2Winner9CompleteSeedBlock33.pages[13]!,
    P2Winner9CompleteSeedBlock33.pages[14]!,
    P2Winner9CompleteSeedBlock33.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0528.checked.flatten_cons <|
    P2Winner9NumericalPage0529.checked.flatten_cons <|
    P2Winner9NumericalPage0530.checked.flatten_cons <|
    P2Winner9NumericalPage0531.checked.flatten_cons <|
    P2Winner9NumericalPage0532.checked.flatten_cons <|
    P2Winner9NumericalPage0533.checked.flatten_cons <|
    P2Winner9NumericalPage0534.checked.flatten_cons <|
    P2Winner9NumericalPage0535.checked.flatten_cons <|
    P2Winner9NumericalPage0536.checked.flatten_cons <|
    P2Winner9NumericalPage0537.checked.flatten_cons <|
    P2Winner9NumericalPage0538.checked.flatten_cons <|
    P2Winner9NumericalPage0539.checked.flatten_cons <|
    P2Winner9NumericalPage0540.checked.flatten_cons <|
    P2Winner9NumericalPage0541.checked.flatten_cons <|
    P2Winner9NumericalPage0542.checked.flatten_cons <|
    P2Winner9NumericalPage0543.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck33
