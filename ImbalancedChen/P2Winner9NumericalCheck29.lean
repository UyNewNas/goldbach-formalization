import ImbalancedChen.P2Winner9NumericalPage0464
import ImbalancedChen.P2Winner9NumericalPage0465
import ImbalancedChen.P2Winner9NumericalPage0466
import ImbalancedChen.P2Winner9NumericalPage0467
import ImbalancedChen.P2Winner9NumericalPage0468
import ImbalancedChen.P2Winner9NumericalPage0469
import ImbalancedChen.P2Winner9NumericalPage0470
import ImbalancedChen.P2Winner9NumericalPage0471
import ImbalancedChen.P2Winner9NumericalPage0472
import ImbalancedChen.P2Winner9NumericalPage0473
import ImbalancedChen.P2Winner9NumericalPage0474
import ImbalancedChen.P2Winner9NumericalPage0475
import ImbalancedChen.P2Winner9NumericalPage0476
import ImbalancedChen.P2Winner9NumericalPage0477
import ImbalancedChen.P2Winner9NumericalPage0478
import ImbalancedChen.P2Winner9NumericalPage0479

namespace ImbalancedChen.P2Winner9NumericalCheck29
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 7424 256
    P2Winner9CompleteSeedBlock29.rows := by
  change Checked (fun _ r => checkSelected r = true) 7424 256 ([
    P2Winner9CompleteSeedBlock29.pages[0]!,
    P2Winner9CompleteSeedBlock29.pages[1]!,
    P2Winner9CompleteSeedBlock29.pages[2]!,
    P2Winner9CompleteSeedBlock29.pages[3]!,
    P2Winner9CompleteSeedBlock29.pages[4]!,
    P2Winner9CompleteSeedBlock29.pages[5]!,
    P2Winner9CompleteSeedBlock29.pages[6]!,
    P2Winner9CompleteSeedBlock29.pages[7]!,
    P2Winner9CompleteSeedBlock29.pages[8]!,
    P2Winner9CompleteSeedBlock29.pages[9]!,
    P2Winner9CompleteSeedBlock29.pages[10]!,
    P2Winner9CompleteSeedBlock29.pages[11]!,
    P2Winner9CompleteSeedBlock29.pages[12]!,
    P2Winner9CompleteSeedBlock29.pages[13]!,
    P2Winner9CompleteSeedBlock29.pages[14]!,
    P2Winner9CompleteSeedBlock29.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0464.checked.flatten_cons <|
    P2Winner9NumericalPage0465.checked.flatten_cons <|
    P2Winner9NumericalPage0466.checked.flatten_cons <|
    P2Winner9NumericalPage0467.checked.flatten_cons <|
    P2Winner9NumericalPage0468.checked.flatten_cons <|
    P2Winner9NumericalPage0469.checked.flatten_cons <|
    P2Winner9NumericalPage0470.checked.flatten_cons <|
    P2Winner9NumericalPage0471.checked.flatten_cons <|
    P2Winner9NumericalPage0472.checked.flatten_cons <|
    P2Winner9NumericalPage0473.checked.flatten_cons <|
    P2Winner9NumericalPage0474.checked.flatten_cons <|
    P2Winner9NumericalPage0475.checked.flatten_cons <|
    P2Winner9NumericalPage0476.checked.flatten_cons <|
    P2Winner9NumericalPage0477.checked.flatten_cons <|
    P2Winner9NumericalPage0478.checked.flatten_cons <|
    P2Winner9NumericalPage0479.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck29
