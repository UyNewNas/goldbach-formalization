import ImbalancedChen.P2Winner9NumericalPage0576
import ImbalancedChen.P2Winner9NumericalPage0577
import ImbalancedChen.P2Winner9NumericalPage0578
import ImbalancedChen.P2Winner9NumericalPage0579
import ImbalancedChen.P2Winner9NumericalPage0580
import ImbalancedChen.P2Winner9NumericalPage0581
import ImbalancedChen.P2Winner9NumericalPage0582
import ImbalancedChen.P2Winner9NumericalPage0583
import ImbalancedChen.P2Winner9NumericalPage0584
import ImbalancedChen.P2Winner9NumericalPage0585
import ImbalancedChen.P2Winner9NumericalPage0586
import ImbalancedChen.P2Winner9NumericalPage0587
import ImbalancedChen.P2Winner9NumericalPage0588
import ImbalancedChen.P2Winner9NumericalPage0589
import ImbalancedChen.P2Winner9NumericalPage0590
import ImbalancedChen.P2Winner9NumericalPage0591

namespace ImbalancedChen.P2Winner9NumericalCheck36
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 9216 256
    P2Winner9CompleteSeedBlock36.rows := by
  change Checked (fun _ r => checkSelected r = true) 9216 256 ([
    P2Winner9CompleteSeedBlock36.pages[0]!,
    P2Winner9CompleteSeedBlock36.pages[1]!,
    P2Winner9CompleteSeedBlock36.pages[2]!,
    P2Winner9CompleteSeedBlock36.pages[3]!,
    P2Winner9CompleteSeedBlock36.pages[4]!,
    P2Winner9CompleteSeedBlock36.pages[5]!,
    P2Winner9CompleteSeedBlock36.pages[6]!,
    P2Winner9CompleteSeedBlock36.pages[7]!,
    P2Winner9CompleteSeedBlock36.pages[8]!,
    P2Winner9CompleteSeedBlock36.pages[9]!,
    P2Winner9CompleteSeedBlock36.pages[10]!,
    P2Winner9CompleteSeedBlock36.pages[11]!,
    P2Winner9CompleteSeedBlock36.pages[12]!,
    P2Winner9CompleteSeedBlock36.pages[13]!,
    P2Winner9CompleteSeedBlock36.pages[14]!,
    P2Winner9CompleteSeedBlock36.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0576.checked.flatten_cons <|
    P2Winner9NumericalPage0577.checked.flatten_cons <|
    P2Winner9NumericalPage0578.checked.flatten_cons <|
    P2Winner9NumericalPage0579.checked.flatten_cons <|
    P2Winner9NumericalPage0580.checked.flatten_cons <|
    P2Winner9NumericalPage0581.checked.flatten_cons <|
    P2Winner9NumericalPage0582.checked.flatten_cons <|
    P2Winner9NumericalPage0583.checked.flatten_cons <|
    P2Winner9NumericalPage0584.checked.flatten_cons <|
    P2Winner9NumericalPage0585.checked.flatten_cons <|
    P2Winner9NumericalPage0586.checked.flatten_cons <|
    P2Winner9NumericalPage0587.checked.flatten_cons <|
    P2Winner9NumericalPage0588.checked.flatten_cons <|
    P2Winner9NumericalPage0589.checked.flatten_cons <|
    P2Winner9NumericalPage0590.checked.flatten_cons <|
    P2Winner9NumericalPage0591.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck36
