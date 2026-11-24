import ImbalancedChen.P2Winner9NumericalPage0432
import ImbalancedChen.P2Winner9NumericalPage0433
import ImbalancedChen.P2Winner9NumericalPage0434
import ImbalancedChen.P2Winner9NumericalPage0435
import ImbalancedChen.P2Winner9NumericalPage0436
import ImbalancedChen.P2Winner9NumericalPage0437
import ImbalancedChen.P2Winner9NumericalPage0438
import ImbalancedChen.P2Winner9NumericalPage0439
import ImbalancedChen.P2Winner9NumericalPage0440
import ImbalancedChen.P2Winner9NumericalPage0441
import ImbalancedChen.P2Winner9NumericalPage0442
import ImbalancedChen.P2Winner9NumericalPage0443
import ImbalancedChen.P2Winner9NumericalPage0444
import ImbalancedChen.P2Winner9NumericalPage0445
import ImbalancedChen.P2Winner9NumericalPage0446
import ImbalancedChen.P2Winner9NumericalPage0447

namespace ImbalancedChen.P2Winner9NumericalCheck27
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 6912 256
    P2Winner9CompleteSeedBlock27.rows := by
  change Checked (fun _ r => checkSelected r = true) 6912 256 ([
    P2Winner9CompleteSeedBlock27.pages[0]!,
    P2Winner9CompleteSeedBlock27.pages[1]!,
    P2Winner9CompleteSeedBlock27.pages[2]!,
    P2Winner9CompleteSeedBlock27.pages[3]!,
    P2Winner9CompleteSeedBlock27.pages[4]!,
    P2Winner9CompleteSeedBlock27.pages[5]!,
    P2Winner9CompleteSeedBlock27.pages[6]!,
    P2Winner9CompleteSeedBlock27.pages[7]!,
    P2Winner9CompleteSeedBlock27.pages[8]!,
    P2Winner9CompleteSeedBlock27.pages[9]!,
    P2Winner9CompleteSeedBlock27.pages[10]!,
    P2Winner9CompleteSeedBlock27.pages[11]!,
    P2Winner9CompleteSeedBlock27.pages[12]!,
    P2Winner9CompleteSeedBlock27.pages[13]!,
    P2Winner9CompleteSeedBlock27.pages[14]!,
    P2Winner9CompleteSeedBlock27.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0432.checked.flatten_cons <|
    P2Winner9NumericalPage0433.checked.flatten_cons <|
    P2Winner9NumericalPage0434.checked.flatten_cons <|
    P2Winner9NumericalPage0435.checked.flatten_cons <|
    P2Winner9NumericalPage0436.checked.flatten_cons <|
    P2Winner9NumericalPage0437.checked.flatten_cons <|
    P2Winner9NumericalPage0438.checked.flatten_cons <|
    P2Winner9NumericalPage0439.checked.flatten_cons <|
    P2Winner9NumericalPage0440.checked.flatten_cons <|
    P2Winner9NumericalPage0441.checked.flatten_cons <|
    P2Winner9NumericalPage0442.checked.flatten_cons <|
    P2Winner9NumericalPage0443.checked.flatten_cons <|
    P2Winner9NumericalPage0444.checked.flatten_cons <|
    P2Winner9NumericalPage0445.checked.flatten_cons <|
    P2Winner9NumericalPage0446.checked.flatten_cons <|
    P2Winner9NumericalPage0447.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck27
