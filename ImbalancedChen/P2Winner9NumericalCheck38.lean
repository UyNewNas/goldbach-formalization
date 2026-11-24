import ImbalancedChen.P2Winner9NumericalPage0608
import ImbalancedChen.P2Winner9NumericalPage0609
import ImbalancedChen.P2Winner9NumericalPage0610
import ImbalancedChen.P2Winner9NumericalPage0611
import ImbalancedChen.P2Winner9NumericalPage0612
import ImbalancedChen.P2Winner9NumericalPage0613
import ImbalancedChen.P2Winner9NumericalPage0614
import ImbalancedChen.P2Winner9NumericalPage0615
import ImbalancedChen.P2Winner9NumericalPage0616
import ImbalancedChen.P2Winner9NumericalPage0617
import ImbalancedChen.P2Winner9NumericalPage0618
import ImbalancedChen.P2Winner9NumericalPage0619
import ImbalancedChen.P2Winner9NumericalPage0620
import ImbalancedChen.P2Winner9NumericalPage0621
import ImbalancedChen.P2Winner9NumericalPage0622
import ImbalancedChen.P2Winner9NumericalPage0623

namespace ImbalancedChen.P2Winner9NumericalCheck38
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 9728 256
    P2Winner9CompleteSeedBlock38.rows := by
  change Checked (fun _ r => checkSelected r = true) 9728 256 ([
    P2Winner9CompleteSeedBlock38.pages[0]!,
    P2Winner9CompleteSeedBlock38.pages[1]!,
    P2Winner9CompleteSeedBlock38.pages[2]!,
    P2Winner9CompleteSeedBlock38.pages[3]!,
    P2Winner9CompleteSeedBlock38.pages[4]!,
    P2Winner9CompleteSeedBlock38.pages[5]!,
    P2Winner9CompleteSeedBlock38.pages[6]!,
    P2Winner9CompleteSeedBlock38.pages[7]!,
    P2Winner9CompleteSeedBlock38.pages[8]!,
    P2Winner9CompleteSeedBlock38.pages[9]!,
    P2Winner9CompleteSeedBlock38.pages[10]!,
    P2Winner9CompleteSeedBlock38.pages[11]!,
    P2Winner9CompleteSeedBlock38.pages[12]!,
    P2Winner9CompleteSeedBlock38.pages[13]!,
    P2Winner9CompleteSeedBlock38.pages[14]!,
    P2Winner9CompleteSeedBlock38.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0608.checked.flatten_cons <|
    P2Winner9NumericalPage0609.checked.flatten_cons <|
    P2Winner9NumericalPage0610.checked.flatten_cons <|
    P2Winner9NumericalPage0611.checked.flatten_cons <|
    P2Winner9NumericalPage0612.checked.flatten_cons <|
    P2Winner9NumericalPage0613.checked.flatten_cons <|
    P2Winner9NumericalPage0614.checked.flatten_cons <|
    P2Winner9NumericalPage0615.checked.flatten_cons <|
    P2Winner9NumericalPage0616.checked.flatten_cons <|
    P2Winner9NumericalPage0617.checked.flatten_cons <|
    P2Winner9NumericalPage0618.checked.flatten_cons <|
    P2Winner9NumericalPage0619.checked.flatten_cons <|
    P2Winner9NumericalPage0620.checked.flatten_cons <|
    P2Winner9NumericalPage0621.checked.flatten_cons <|
    P2Winner9NumericalPage0622.checked.flatten_cons <|
    P2Winner9NumericalPage0623.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck38
