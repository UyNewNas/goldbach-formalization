import ImbalancedChen.P2Winner9NumericalPage0368
import ImbalancedChen.P2Winner9NumericalPage0369
import ImbalancedChen.P2Winner9NumericalPage0370
import ImbalancedChen.P2Winner9NumericalPage0371
import ImbalancedChen.P2Winner9NumericalPage0372
import ImbalancedChen.P2Winner9NumericalPage0373
import ImbalancedChen.P2Winner9NumericalPage0374
import ImbalancedChen.P2Winner9NumericalPage0375
import ImbalancedChen.P2Winner9NumericalPage0376
import ImbalancedChen.P2Winner9NumericalPage0377
import ImbalancedChen.P2Winner9NumericalPage0378
import ImbalancedChen.P2Winner9NumericalPage0379
import ImbalancedChen.P2Winner9NumericalPage0380
import ImbalancedChen.P2Winner9NumericalPage0381
import ImbalancedChen.P2Winner9NumericalPage0382
import ImbalancedChen.P2Winner9NumericalPage0383

namespace ImbalancedChen.P2Winner9NumericalCheck23
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 5888 256
    P2Winner9CompleteSeedBlock23.rows := by
  change Checked (fun _ r => checkSelected r = true) 5888 256 ([
    P2Winner9CompleteSeedBlock23.pages[0]!,
    P2Winner9CompleteSeedBlock23.pages[1]!,
    P2Winner9CompleteSeedBlock23.pages[2]!,
    P2Winner9CompleteSeedBlock23.pages[3]!,
    P2Winner9CompleteSeedBlock23.pages[4]!,
    P2Winner9CompleteSeedBlock23.pages[5]!,
    P2Winner9CompleteSeedBlock23.pages[6]!,
    P2Winner9CompleteSeedBlock23.pages[7]!,
    P2Winner9CompleteSeedBlock23.pages[8]!,
    P2Winner9CompleteSeedBlock23.pages[9]!,
    P2Winner9CompleteSeedBlock23.pages[10]!,
    P2Winner9CompleteSeedBlock23.pages[11]!,
    P2Winner9CompleteSeedBlock23.pages[12]!,
    P2Winner9CompleteSeedBlock23.pages[13]!,
    P2Winner9CompleteSeedBlock23.pages[14]!,
    P2Winner9CompleteSeedBlock23.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0368.checked.flatten_cons <|
    P2Winner9NumericalPage0369.checked.flatten_cons <|
    P2Winner9NumericalPage0370.checked.flatten_cons <|
    P2Winner9NumericalPage0371.checked.flatten_cons <|
    P2Winner9NumericalPage0372.checked.flatten_cons <|
    P2Winner9NumericalPage0373.checked.flatten_cons <|
    P2Winner9NumericalPage0374.checked.flatten_cons <|
    P2Winner9NumericalPage0375.checked.flatten_cons <|
    P2Winner9NumericalPage0376.checked.flatten_cons <|
    P2Winner9NumericalPage0377.checked.flatten_cons <|
    P2Winner9NumericalPage0378.checked.flatten_cons <|
    P2Winner9NumericalPage0379.checked.flatten_cons <|
    P2Winner9NumericalPage0380.checked.flatten_cons <|
    P2Winner9NumericalPage0381.checked.flatten_cons <|
    P2Winner9NumericalPage0382.checked.flatten_cons <|
    P2Winner9NumericalPage0383.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck23
