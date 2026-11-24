import ImbalancedChen.P2Winner9NumericalPage0512
import ImbalancedChen.P2Winner9NumericalPage0513
import ImbalancedChen.P2Winner9NumericalPage0514
import ImbalancedChen.P2Winner9NumericalPage0515
import ImbalancedChen.P2Winner9NumericalPage0516
import ImbalancedChen.P2Winner9NumericalPage0517
import ImbalancedChen.P2Winner9NumericalPage0518
import ImbalancedChen.P2Winner9NumericalPage0519
import ImbalancedChen.P2Winner9NumericalPage0520
import ImbalancedChen.P2Winner9NumericalPage0521
import ImbalancedChen.P2Winner9NumericalPage0522
import ImbalancedChen.P2Winner9NumericalPage0523
import ImbalancedChen.P2Winner9NumericalPage0524
import ImbalancedChen.P2Winner9NumericalPage0525
import ImbalancedChen.P2Winner9NumericalPage0526
import ImbalancedChen.P2Winner9NumericalPage0527

namespace ImbalancedChen.P2Winner9NumericalCheck32
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 8192 256
    P2Winner9CompleteSeedBlock32.rows := by
  change Checked (fun _ r => checkSelected r = true) 8192 256 ([
    P2Winner9CompleteSeedBlock32.pages[0]!,
    P2Winner9CompleteSeedBlock32.pages[1]!,
    P2Winner9CompleteSeedBlock32.pages[2]!,
    P2Winner9CompleteSeedBlock32.pages[3]!,
    P2Winner9CompleteSeedBlock32.pages[4]!,
    P2Winner9CompleteSeedBlock32.pages[5]!,
    P2Winner9CompleteSeedBlock32.pages[6]!,
    P2Winner9CompleteSeedBlock32.pages[7]!,
    P2Winner9CompleteSeedBlock32.pages[8]!,
    P2Winner9CompleteSeedBlock32.pages[9]!,
    P2Winner9CompleteSeedBlock32.pages[10]!,
    P2Winner9CompleteSeedBlock32.pages[11]!,
    P2Winner9CompleteSeedBlock32.pages[12]!,
    P2Winner9CompleteSeedBlock32.pages[13]!,
    P2Winner9CompleteSeedBlock32.pages[14]!,
    P2Winner9CompleteSeedBlock32.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0512.checked.flatten_cons <|
    P2Winner9NumericalPage0513.checked.flatten_cons <|
    P2Winner9NumericalPage0514.checked.flatten_cons <|
    P2Winner9NumericalPage0515.checked.flatten_cons <|
    P2Winner9NumericalPage0516.checked.flatten_cons <|
    P2Winner9NumericalPage0517.checked.flatten_cons <|
    P2Winner9NumericalPage0518.checked.flatten_cons <|
    P2Winner9NumericalPage0519.checked.flatten_cons <|
    P2Winner9NumericalPage0520.checked.flatten_cons <|
    P2Winner9NumericalPage0521.checked.flatten_cons <|
    P2Winner9NumericalPage0522.checked.flatten_cons <|
    P2Winner9NumericalPage0523.checked.flatten_cons <|
    P2Winner9NumericalPage0524.checked.flatten_cons <|
    P2Winner9NumericalPage0525.checked.flatten_cons <|
    P2Winner9NumericalPage0526.checked.flatten_cons <|
    P2Winner9NumericalPage0527.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck32
