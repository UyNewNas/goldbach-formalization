import ImbalancedChen.P2Winner9NumericalPage0032
import ImbalancedChen.P2Winner9NumericalPage0033
import ImbalancedChen.P2Winner9NumericalPage0034
import ImbalancedChen.P2Winner9NumericalPage0035
import ImbalancedChen.P2Winner9NumericalPage0036
import ImbalancedChen.P2Winner9NumericalPage0037
import ImbalancedChen.P2Winner9NumericalPage0038
import ImbalancedChen.P2Winner9NumericalPage0039
import ImbalancedChen.P2Winner9NumericalPage0040
import ImbalancedChen.P2Winner9NumericalPage0041
import ImbalancedChen.P2Winner9NumericalPage0042
import ImbalancedChen.P2Winner9NumericalPage0043
import ImbalancedChen.P2Winner9NumericalPage0044
import ImbalancedChen.P2Winner9NumericalPage0045
import ImbalancedChen.P2Winner9NumericalPage0046
import ImbalancedChen.P2Winner9NumericalPage0047

namespace ImbalancedChen.P2Winner9NumericalCheck02
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 512 256
    P2Winner9CompleteSeedBlock02.rows := by
  change Checked (fun _ r => checkSelected r = true) 512 256 ([
    P2Winner9CompleteSeedBlock02.pages[0]!,
    P2Winner9CompleteSeedBlock02.pages[1]!,
    P2Winner9CompleteSeedBlock02.pages[2]!,
    P2Winner9CompleteSeedBlock02.pages[3]!,
    P2Winner9CompleteSeedBlock02.pages[4]!,
    P2Winner9CompleteSeedBlock02.pages[5]!,
    P2Winner9CompleteSeedBlock02.pages[6]!,
    P2Winner9CompleteSeedBlock02.pages[7]!,
    P2Winner9CompleteSeedBlock02.pages[8]!,
    P2Winner9CompleteSeedBlock02.pages[9]!,
    P2Winner9CompleteSeedBlock02.pages[10]!,
    P2Winner9CompleteSeedBlock02.pages[11]!,
    P2Winner9CompleteSeedBlock02.pages[12]!,
    P2Winner9CompleteSeedBlock02.pages[13]!,
    P2Winner9CompleteSeedBlock02.pages[14]!,
    P2Winner9CompleteSeedBlock02.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0032.checked.flatten_cons <|
    P2Winner9NumericalPage0033.checked.flatten_cons <|
    P2Winner9NumericalPage0034.checked.flatten_cons <|
    P2Winner9NumericalPage0035.checked.flatten_cons <|
    P2Winner9NumericalPage0036.checked.flatten_cons <|
    P2Winner9NumericalPage0037.checked.flatten_cons <|
    P2Winner9NumericalPage0038.checked.flatten_cons <|
    P2Winner9NumericalPage0039.checked.flatten_cons <|
    P2Winner9NumericalPage0040.checked.flatten_cons <|
    P2Winner9NumericalPage0041.checked.flatten_cons <|
    P2Winner9NumericalPage0042.checked.flatten_cons <|
    P2Winner9NumericalPage0043.checked.flatten_cons <|
    P2Winner9NumericalPage0044.checked.flatten_cons <|
    P2Winner9NumericalPage0045.checked.flatten_cons <|
    P2Winner9NumericalPage0046.checked.flatten_cons <|
    P2Winner9NumericalPage0047.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck02
