import ImbalancedChen.P2Winner9NumericalPage0592
import ImbalancedChen.P2Winner9NumericalPage0593
import ImbalancedChen.P2Winner9NumericalPage0594
import ImbalancedChen.P2Winner9NumericalPage0595
import ImbalancedChen.P2Winner9NumericalPage0596
import ImbalancedChen.P2Winner9NumericalPage0597
import ImbalancedChen.P2Winner9NumericalPage0598
import ImbalancedChen.P2Winner9NumericalPage0599
import ImbalancedChen.P2Winner9NumericalPage0600
import ImbalancedChen.P2Winner9NumericalPage0601
import ImbalancedChen.P2Winner9NumericalPage0602
import ImbalancedChen.P2Winner9NumericalPage0603
import ImbalancedChen.P2Winner9NumericalPage0604
import ImbalancedChen.P2Winner9NumericalPage0605
import ImbalancedChen.P2Winner9NumericalPage0606
import ImbalancedChen.P2Winner9NumericalPage0607

namespace ImbalancedChen.P2Winner9NumericalCheck37
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 9472 256
    P2Winner9CompleteSeedBlock37.rows := by
  change Checked (fun _ r => checkSelected r = true) 9472 256 ([
    P2Winner9CompleteSeedBlock37.pages[0]!,
    P2Winner9CompleteSeedBlock37.pages[1]!,
    P2Winner9CompleteSeedBlock37.pages[2]!,
    P2Winner9CompleteSeedBlock37.pages[3]!,
    P2Winner9CompleteSeedBlock37.pages[4]!,
    P2Winner9CompleteSeedBlock37.pages[5]!,
    P2Winner9CompleteSeedBlock37.pages[6]!,
    P2Winner9CompleteSeedBlock37.pages[7]!,
    P2Winner9CompleteSeedBlock37.pages[8]!,
    P2Winner9CompleteSeedBlock37.pages[9]!,
    P2Winner9CompleteSeedBlock37.pages[10]!,
    P2Winner9CompleteSeedBlock37.pages[11]!,
    P2Winner9CompleteSeedBlock37.pages[12]!,
    P2Winner9CompleteSeedBlock37.pages[13]!,
    P2Winner9CompleteSeedBlock37.pages[14]!,
    P2Winner9CompleteSeedBlock37.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0592.checked.flatten_cons <|
    P2Winner9NumericalPage0593.checked.flatten_cons <|
    P2Winner9NumericalPage0594.checked.flatten_cons <|
    P2Winner9NumericalPage0595.checked.flatten_cons <|
    P2Winner9NumericalPage0596.checked.flatten_cons <|
    P2Winner9NumericalPage0597.checked.flatten_cons <|
    P2Winner9NumericalPage0598.checked.flatten_cons <|
    P2Winner9NumericalPage0599.checked.flatten_cons <|
    P2Winner9NumericalPage0600.checked.flatten_cons <|
    P2Winner9NumericalPage0601.checked.flatten_cons <|
    P2Winner9NumericalPage0602.checked.flatten_cons <|
    P2Winner9NumericalPage0603.checked.flatten_cons <|
    P2Winner9NumericalPage0604.checked.flatten_cons <|
    P2Winner9NumericalPage0605.checked.flatten_cons <|
    P2Winner9NumericalPage0606.checked.flatten_cons <|
    P2Winner9NumericalPage0607.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck37
