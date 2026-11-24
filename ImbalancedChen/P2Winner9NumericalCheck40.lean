import ImbalancedChen.P2Winner9NumericalPage0640
import ImbalancedChen.P2Winner9NumericalPage0641
import ImbalancedChen.P2Winner9NumericalPage0642
import ImbalancedChen.P2Winner9NumericalPage0643
import ImbalancedChen.P2Winner9NumericalPage0644
import ImbalancedChen.P2Winner9NumericalPage0645
import ImbalancedChen.P2Winner9NumericalPage0646
import ImbalancedChen.P2Winner9NumericalPage0647
import ImbalancedChen.P2Winner9NumericalPage0648
import ImbalancedChen.P2Winner9NumericalPage0649
import ImbalancedChen.P2Winner9NumericalPage0650
import ImbalancedChen.P2Winner9NumericalPage0651
import ImbalancedChen.P2Winner9NumericalPage0652
import ImbalancedChen.P2Winner9NumericalPage0653
import ImbalancedChen.P2Winner9NumericalPage0654
import ImbalancedChen.P2Winner9NumericalPage0655

namespace ImbalancedChen.P2Winner9NumericalCheck40
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 10240 256
    P2Winner9CompleteSeedBlock40.rows := by
  change Checked (fun _ r => checkSelected r = true) 10240 256 ([
    P2Winner9CompleteSeedBlock40.pages[0]!,
    P2Winner9CompleteSeedBlock40.pages[1]!,
    P2Winner9CompleteSeedBlock40.pages[2]!,
    P2Winner9CompleteSeedBlock40.pages[3]!,
    P2Winner9CompleteSeedBlock40.pages[4]!,
    P2Winner9CompleteSeedBlock40.pages[5]!,
    P2Winner9CompleteSeedBlock40.pages[6]!,
    P2Winner9CompleteSeedBlock40.pages[7]!,
    P2Winner9CompleteSeedBlock40.pages[8]!,
    P2Winner9CompleteSeedBlock40.pages[9]!,
    P2Winner9CompleteSeedBlock40.pages[10]!,
    P2Winner9CompleteSeedBlock40.pages[11]!,
    P2Winner9CompleteSeedBlock40.pages[12]!,
    P2Winner9CompleteSeedBlock40.pages[13]!,
    P2Winner9CompleteSeedBlock40.pages[14]!,
    P2Winner9CompleteSeedBlock40.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0640.checked.flatten_cons <|
    P2Winner9NumericalPage0641.checked.flatten_cons <|
    P2Winner9NumericalPage0642.checked.flatten_cons <|
    P2Winner9NumericalPage0643.checked.flatten_cons <|
    P2Winner9NumericalPage0644.checked.flatten_cons <|
    P2Winner9NumericalPage0645.checked.flatten_cons <|
    P2Winner9NumericalPage0646.checked.flatten_cons <|
    P2Winner9NumericalPage0647.checked.flatten_cons <|
    P2Winner9NumericalPage0648.checked.flatten_cons <|
    P2Winner9NumericalPage0649.checked.flatten_cons <|
    P2Winner9NumericalPage0650.checked.flatten_cons <|
    P2Winner9NumericalPage0651.checked.flatten_cons <|
    P2Winner9NumericalPage0652.checked.flatten_cons <|
    P2Winner9NumericalPage0653.checked.flatten_cons <|
    P2Winner9NumericalPage0654.checked.flatten_cons <|
    P2Winner9NumericalPage0655.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck40
