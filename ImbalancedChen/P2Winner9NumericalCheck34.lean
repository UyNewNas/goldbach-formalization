import ImbalancedChen.P2Winner9NumericalPage0544
import ImbalancedChen.P2Winner9NumericalPage0545
import ImbalancedChen.P2Winner9NumericalPage0546
import ImbalancedChen.P2Winner9NumericalPage0547
import ImbalancedChen.P2Winner9NumericalPage0548
import ImbalancedChen.P2Winner9NumericalPage0549
import ImbalancedChen.P2Winner9NumericalPage0550
import ImbalancedChen.P2Winner9NumericalPage0551
import ImbalancedChen.P2Winner9NumericalPage0552
import ImbalancedChen.P2Winner9NumericalPage0553
import ImbalancedChen.P2Winner9NumericalPage0554
import ImbalancedChen.P2Winner9NumericalPage0555
import ImbalancedChen.P2Winner9NumericalPage0556
import ImbalancedChen.P2Winner9NumericalPage0557
import ImbalancedChen.P2Winner9NumericalPage0558
import ImbalancedChen.P2Winner9NumericalPage0559

namespace ImbalancedChen.P2Winner9NumericalCheck34
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 8704 256
    P2Winner9CompleteSeedBlock34.rows := by
  change Checked (fun _ r => checkSelected r = true) 8704 256 ([
    P2Winner9CompleteSeedBlock34.pages[0]!,
    P2Winner9CompleteSeedBlock34.pages[1]!,
    P2Winner9CompleteSeedBlock34.pages[2]!,
    P2Winner9CompleteSeedBlock34.pages[3]!,
    P2Winner9CompleteSeedBlock34.pages[4]!,
    P2Winner9CompleteSeedBlock34.pages[5]!,
    P2Winner9CompleteSeedBlock34.pages[6]!,
    P2Winner9CompleteSeedBlock34.pages[7]!,
    P2Winner9CompleteSeedBlock34.pages[8]!,
    P2Winner9CompleteSeedBlock34.pages[9]!,
    P2Winner9CompleteSeedBlock34.pages[10]!,
    P2Winner9CompleteSeedBlock34.pages[11]!,
    P2Winner9CompleteSeedBlock34.pages[12]!,
    P2Winner9CompleteSeedBlock34.pages[13]!,
    P2Winner9CompleteSeedBlock34.pages[14]!,
    P2Winner9CompleteSeedBlock34.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0544.checked.flatten_cons <|
    P2Winner9NumericalPage0545.checked.flatten_cons <|
    P2Winner9NumericalPage0546.checked.flatten_cons <|
    P2Winner9NumericalPage0547.checked.flatten_cons <|
    P2Winner9NumericalPage0548.checked.flatten_cons <|
    P2Winner9NumericalPage0549.checked.flatten_cons <|
    P2Winner9NumericalPage0550.checked.flatten_cons <|
    P2Winner9NumericalPage0551.checked.flatten_cons <|
    P2Winner9NumericalPage0552.checked.flatten_cons <|
    P2Winner9NumericalPage0553.checked.flatten_cons <|
    P2Winner9NumericalPage0554.checked.flatten_cons <|
    P2Winner9NumericalPage0555.checked.flatten_cons <|
    P2Winner9NumericalPage0556.checked.flatten_cons <|
    P2Winner9NumericalPage0557.checked.flatten_cons <|
    P2Winner9NumericalPage0558.checked.flatten_cons <|
    P2Winner9NumericalPage0559.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck34
