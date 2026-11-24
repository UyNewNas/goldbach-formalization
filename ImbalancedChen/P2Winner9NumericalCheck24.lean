import ImbalancedChen.P2Winner9NumericalPage0384
import ImbalancedChen.P2Winner9NumericalPage0385
import ImbalancedChen.P2Winner9NumericalPage0386
import ImbalancedChen.P2Winner9NumericalPage0387
import ImbalancedChen.P2Winner9NumericalPage0388
import ImbalancedChen.P2Winner9NumericalPage0389
import ImbalancedChen.P2Winner9NumericalPage0390
import ImbalancedChen.P2Winner9NumericalPage0391
import ImbalancedChen.P2Winner9NumericalPage0392
import ImbalancedChen.P2Winner9NumericalPage0393
import ImbalancedChen.P2Winner9NumericalPage0394
import ImbalancedChen.P2Winner9NumericalPage0395
import ImbalancedChen.P2Winner9NumericalPage0396
import ImbalancedChen.P2Winner9NumericalPage0397
import ImbalancedChen.P2Winner9NumericalPage0398
import ImbalancedChen.P2Winner9NumericalPage0399

namespace ImbalancedChen.P2Winner9NumericalCheck24
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 6144 256
    P2Winner9CompleteSeedBlock24.rows := by
  change Checked (fun _ r => checkSelected r = true) 6144 256 ([
    P2Winner9CompleteSeedBlock24.pages[0]!,
    P2Winner9CompleteSeedBlock24.pages[1]!,
    P2Winner9CompleteSeedBlock24.pages[2]!,
    P2Winner9CompleteSeedBlock24.pages[3]!,
    P2Winner9CompleteSeedBlock24.pages[4]!,
    P2Winner9CompleteSeedBlock24.pages[5]!,
    P2Winner9CompleteSeedBlock24.pages[6]!,
    P2Winner9CompleteSeedBlock24.pages[7]!,
    P2Winner9CompleteSeedBlock24.pages[8]!,
    P2Winner9CompleteSeedBlock24.pages[9]!,
    P2Winner9CompleteSeedBlock24.pages[10]!,
    P2Winner9CompleteSeedBlock24.pages[11]!,
    P2Winner9CompleteSeedBlock24.pages[12]!,
    P2Winner9CompleteSeedBlock24.pages[13]!,
    P2Winner9CompleteSeedBlock24.pages[14]!,
    P2Winner9CompleteSeedBlock24.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0384.checked.flatten_cons <|
    P2Winner9NumericalPage0385.checked.flatten_cons <|
    P2Winner9NumericalPage0386.checked.flatten_cons <|
    P2Winner9NumericalPage0387.checked.flatten_cons <|
    P2Winner9NumericalPage0388.checked.flatten_cons <|
    P2Winner9NumericalPage0389.checked.flatten_cons <|
    P2Winner9NumericalPage0390.checked.flatten_cons <|
    P2Winner9NumericalPage0391.checked.flatten_cons <|
    P2Winner9NumericalPage0392.checked.flatten_cons <|
    P2Winner9NumericalPage0393.checked.flatten_cons <|
    P2Winner9NumericalPage0394.checked.flatten_cons <|
    P2Winner9NumericalPage0395.checked.flatten_cons <|
    P2Winner9NumericalPage0396.checked.flatten_cons <|
    P2Winner9NumericalPage0397.checked.flatten_cons <|
    P2Winner9NumericalPage0398.checked.flatten_cons <|
    P2Winner9NumericalPage0399.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck24
