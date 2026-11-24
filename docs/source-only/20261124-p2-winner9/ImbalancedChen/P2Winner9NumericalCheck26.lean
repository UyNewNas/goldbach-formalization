import ImbalancedChen.P2Winner9NumericalPage0416
import ImbalancedChen.P2Winner9NumericalPage0417
import ImbalancedChen.P2Winner9NumericalPage0418
import ImbalancedChen.P2Winner9NumericalPage0419
import ImbalancedChen.P2Winner9NumericalPage0420
import ImbalancedChen.P2Winner9NumericalPage0421
import ImbalancedChen.P2Winner9NumericalPage0422
import ImbalancedChen.P2Winner9NumericalPage0423
import ImbalancedChen.P2Winner9NumericalPage0424
import ImbalancedChen.P2Winner9NumericalPage0425
import ImbalancedChen.P2Winner9NumericalPage0426
import ImbalancedChen.P2Winner9NumericalPage0427
import ImbalancedChen.P2Winner9NumericalPage0428
import ImbalancedChen.P2Winner9NumericalPage0429
import ImbalancedChen.P2Winner9NumericalPage0430
import ImbalancedChen.P2Winner9NumericalPage0431

namespace ImbalancedChen.P2Winner9NumericalCheck26
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 6656 256
    P2Winner9CompleteSeedBlock26.rows := by
  change Checked (fun _ r => checkSelected r = true) 6656 256 ([
    P2Winner9CompleteSeedBlock26.pages[0]!,
    P2Winner9CompleteSeedBlock26.pages[1]!,
    P2Winner9CompleteSeedBlock26.pages[2]!,
    P2Winner9CompleteSeedBlock26.pages[3]!,
    P2Winner9CompleteSeedBlock26.pages[4]!,
    P2Winner9CompleteSeedBlock26.pages[5]!,
    P2Winner9CompleteSeedBlock26.pages[6]!,
    P2Winner9CompleteSeedBlock26.pages[7]!,
    P2Winner9CompleteSeedBlock26.pages[8]!,
    P2Winner9CompleteSeedBlock26.pages[9]!,
    P2Winner9CompleteSeedBlock26.pages[10]!,
    P2Winner9CompleteSeedBlock26.pages[11]!,
    P2Winner9CompleteSeedBlock26.pages[12]!,
    P2Winner9CompleteSeedBlock26.pages[13]!,
    P2Winner9CompleteSeedBlock26.pages[14]!,
    P2Winner9CompleteSeedBlock26.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0416.checked.flatten_cons <|
    P2Winner9NumericalPage0417.checked.flatten_cons <|
    P2Winner9NumericalPage0418.checked.flatten_cons <|
    P2Winner9NumericalPage0419.checked.flatten_cons <|
    P2Winner9NumericalPage0420.checked.flatten_cons <|
    P2Winner9NumericalPage0421.checked.flatten_cons <|
    P2Winner9NumericalPage0422.checked.flatten_cons <|
    P2Winner9NumericalPage0423.checked.flatten_cons <|
    P2Winner9NumericalPage0424.checked.flatten_cons <|
    P2Winner9NumericalPage0425.checked.flatten_cons <|
    P2Winner9NumericalPage0426.checked.flatten_cons <|
    P2Winner9NumericalPage0427.checked.flatten_cons <|
    P2Winner9NumericalPage0428.checked.flatten_cons <|
    P2Winner9NumericalPage0429.checked.flatten_cons <|
    P2Winner9NumericalPage0430.checked.flatten_cons <|
    P2Winner9NumericalPage0431.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck26
