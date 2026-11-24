import ImbalancedChen.P2Winner9NumericalPage0624
import ImbalancedChen.P2Winner9NumericalPage0625
import ImbalancedChen.P2Winner9NumericalPage0626
import ImbalancedChen.P2Winner9NumericalPage0627
import ImbalancedChen.P2Winner9NumericalPage0628
import ImbalancedChen.P2Winner9NumericalPage0629
import ImbalancedChen.P2Winner9NumericalPage0630
import ImbalancedChen.P2Winner9NumericalPage0631
import ImbalancedChen.P2Winner9NumericalPage0632
import ImbalancedChen.P2Winner9NumericalPage0633
import ImbalancedChen.P2Winner9NumericalPage0634
import ImbalancedChen.P2Winner9NumericalPage0635
import ImbalancedChen.P2Winner9NumericalPage0636
import ImbalancedChen.P2Winner9NumericalPage0637
import ImbalancedChen.P2Winner9NumericalPage0638
import ImbalancedChen.P2Winner9NumericalPage0639

namespace ImbalancedChen.P2Winner9NumericalCheck39
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 9984 256
    P2Winner9CompleteSeedBlock39.rows := by
  change Checked (fun _ r => checkSelected r = true) 9984 256 ([
    P2Winner9CompleteSeedBlock39.pages[0]!,
    P2Winner9CompleteSeedBlock39.pages[1]!,
    P2Winner9CompleteSeedBlock39.pages[2]!,
    P2Winner9CompleteSeedBlock39.pages[3]!,
    P2Winner9CompleteSeedBlock39.pages[4]!,
    P2Winner9CompleteSeedBlock39.pages[5]!,
    P2Winner9CompleteSeedBlock39.pages[6]!,
    P2Winner9CompleteSeedBlock39.pages[7]!,
    P2Winner9CompleteSeedBlock39.pages[8]!,
    P2Winner9CompleteSeedBlock39.pages[9]!,
    P2Winner9CompleteSeedBlock39.pages[10]!,
    P2Winner9CompleteSeedBlock39.pages[11]!,
    P2Winner9CompleteSeedBlock39.pages[12]!,
    P2Winner9CompleteSeedBlock39.pages[13]!,
    P2Winner9CompleteSeedBlock39.pages[14]!,
    P2Winner9CompleteSeedBlock39.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0624.checked.flatten_cons <|
    P2Winner9NumericalPage0625.checked.flatten_cons <|
    P2Winner9NumericalPage0626.checked.flatten_cons <|
    P2Winner9NumericalPage0627.checked.flatten_cons <|
    P2Winner9NumericalPage0628.checked.flatten_cons <|
    P2Winner9NumericalPage0629.checked.flatten_cons <|
    P2Winner9NumericalPage0630.checked.flatten_cons <|
    P2Winner9NumericalPage0631.checked.flatten_cons <|
    P2Winner9NumericalPage0632.checked.flatten_cons <|
    P2Winner9NumericalPage0633.checked.flatten_cons <|
    P2Winner9NumericalPage0634.checked.flatten_cons <|
    P2Winner9NumericalPage0635.checked.flatten_cons <|
    P2Winner9NumericalPage0636.checked.flatten_cons <|
    P2Winner9NumericalPage0637.checked.flatten_cons <|
    P2Winner9NumericalPage0638.checked.flatten_cons <|
    P2Winner9NumericalPage0639.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck39
