import ImbalancedChen.P2Winner9NumericalPage0480
import ImbalancedChen.P2Winner9NumericalPage0481
import ImbalancedChen.P2Winner9NumericalPage0482
import ImbalancedChen.P2Winner9NumericalPage0483
import ImbalancedChen.P2Winner9NumericalPage0484
import ImbalancedChen.P2Winner9NumericalPage0485
import ImbalancedChen.P2Winner9NumericalPage0486
import ImbalancedChen.P2Winner9NumericalPage0487
import ImbalancedChen.P2Winner9NumericalPage0488
import ImbalancedChen.P2Winner9NumericalPage0489
import ImbalancedChen.P2Winner9NumericalPage0490
import ImbalancedChen.P2Winner9NumericalPage0491
import ImbalancedChen.P2Winner9NumericalPage0492
import ImbalancedChen.P2Winner9NumericalPage0493
import ImbalancedChen.P2Winner9NumericalPage0494
import ImbalancedChen.P2Winner9NumericalPage0495

namespace ImbalancedChen.P2Winner9NumericalCheck30
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 7680 256
    P2Winner9CompleteSeedBlock30.rows := by
  change Checked (fun _ r => checkSelected r = true) 7680 256 ([
    P2Winner9CompleteSeedBlock30.pages[0]!,
    P2Winner9CompleteSeedBlock30.pages[1]!,
    P2Winner9CompleteSeedBlock30.pages[2]!,
    P2Winner9CompleteSeedBlock30.pages[3]!,
    P2Winner9CompleteSeedBlock30.pages[4]!,
    P2Winner9CompleteSeedBlock30.pages[5]!,
    P2Winner9CompleteSeedBlock30.pages[6]!,
    P2Winner9CompleteSeedBlock30.pages[7]!,
    P2Winner9CompleteSeedBlock30.pages[8]!,
    P2Winner9CompleteSeedBlock30.pages[9]!,
    P2Winner9CompleteSeedBlock30.pages[10]!,
    P2Winner9CompleteSeedBlock30.pages[11]!,
    P2Winner9CompleteSeedBlock30.pages[12]!,
    P2Winner9CompleteSeedBlock30.pages[13]!,
    P2Winner9CompleteSeedBlock30.pages[14]!,
    P2Winner9CompleteSeedBlock30.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0480.checked.flatten_cons <|
    P2Winner9NumericalPage0481.checked.flatten_cons <|
    P2Winner9NumericalPage0482.checked.flatten_cons <|
    P2Winner9NumericalPage0483.checked.flatten_cons <|
    P2Winner9NumericalPage0484.checked.flatten_cons <|
    P2Winner9NumericalPage0485.checked.flatten_cons <|
    P2Winner9NumericalPage0486.checked.flatten_cons <|
    P2Winner9NumericalPage0487.checked.flatten_cons <|
    P2Winner9NumericalPage0488.checked.flatten_cons <|
    P2Winner9NumericalPage0489.checked.flatten_cons <|
    P2Winner9NumericalPage0490.checked.flatten_cons <|
    P2Winner9NumericalPage0491.checked.flatten_cons <|
    P2Winner9NumericalPage0492.checked.flatten_cons <|
    P2Winner9NumericalPage0493.checked.flatten_cons <|
    P2Winner9NumericalPage0494.checked.flatten_cons <|
    P2Winner9NumericalPage0495.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck30
