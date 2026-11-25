import ImbalancedChen.P2Winner9NumericalPage0560
import ImbalancedChen.P2Winner9NumericalPage0561
import ImbalancedChen.P2Winner9NumericalPage0562
import ImbalancedChen.P2Winner9NumericalPage0563
import ImbalancedChen.P2Winner9NumericalPage0564
import ImbalancedChen.P2Winner9NumericalPage0565
import ImbalancedChen.P2Winner9NumericalPage0566
import ImbalancedChen.P2Winner9NumericalPage0567
import ImbalancedChen.P2Winner9NumericalPage0568
import ImbalancedChen.P2Winner9NumericalPage0569
import ImbalancedChen.P2Winner9NumericalPage0570
import ImbalancedChen.P2Winner9NumericalPage0571
import ImbalancedChen.P2Winner9NumericalPage0572
import ImbalancedChen.P2Winner9NumericalPage0573
import ImbalancedChen.P2Winner9NumericalPage0574
import ImbalancedChen.P2Winner9NumericalPage0575

namespace ImbalancedChen.P2Winner9NumericalCheck35
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 8960 256
    P2Winner9CompleteSeedBlock35.rows := by
  change Checked (fun _ r => checkSelected r = true) 8960 256 ([
    P2Winner9CompleteSeedBlock35.pages[0]!,
    P2Winner9CompleteSeedBlock35.pages[1]!,
    P2Winner9CompleteSeedBlock35.pages[2]!,
    P2Winner9CompleteSeedBlock35.pages[3]!,
    P2Winner9CompleteSeedBlock35.pages[4]!,
    P2Winner9CompleteSeedBlock35.pages[5]!,
    P2Winner9CompleteSeedBlock35.pages[6]!,
    P2Winner9CompleteSeedBlock35.pages[7]!,
    P2Winner9CompleteSeedBlock35.pages[8]!,
    P2Winner9CompleteSeedBlock35.pages[9]!,
    P2Winner9CompleteSeedBlock35.pages[10]!,
    P2Winner9CompleteSeedBlock35.pages[11]!,
    P2Winner9CompleteSeedBlock35.pages[12]!,
    P2Winner9CompleteSeedBlock35.pages[13]!,
    P2Winner9CompleteSeedBlock35.pages[14]!,
    P2Winner9CompleteSeedBlock35.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0560.checked.flatten_cons <|
    P2Winner9NumericalPage0561.checked.flatten_cons <|
    P2Winner9NumericalPage0562.checked.flatten_cons <|
    P2Winner9NumericalPage0563.checked.flatten_cons <|
    P2Winner9NumericalPage0564.checked.flatten_cons <|
    P2Winner9NumericalPage0565.checked.flatten_cons <|
    P2Winner9NumericalPage0566.checked.flatten_cons <|
    P2Winner9NumericalPage0567.checked.flatten_cons <|
    P2Winner9NumericalPage0568.checked.flatten_cons <|
    P2Winner9NumericalPage0569.checked.flatten_cons <|
    P2Winner9NumericalPage0570.checked.flatten_cons <|
    P2Winner9NumericalPage0571.checked.flatten_cons <|
    P2Winner9NumericalPage0572.checked.flatten_cons <|
    P2Winner9NumericalPage0573.checked.flatten_cons <|
    P2Winner9NumericalPage0574.checked.flatten_cons <|
    P2Winner9NumericalPage0575.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck35
