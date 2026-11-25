import ImbalancedChen.P2Winner9NumericalPage0656
import ImbalancedChen.P2Winner9NumericalPage0657
import ImbalancedChen.P2Winner9NumericalPage0658
import ImbalancedChen.P2Winner9NumericalPage0659
import ImbalancedChen.P2Winner9NumericalPage0660
import ImbalancedChen.P2Winner9NumericalPage0661
import ImbalancedChen.P2Winner9NumericalPage0662
import ImbalancedChen.P2Winner9NumericalPage0663
import ImbalancedChen.P2Winner9NumericalPage0664
import ImbalancedChen.P2Winner9NumericalPage0665
import ImbalancedChen.P2Winner9NumericalPage0666
import ImbalancedChen.P2Winner9NumericalPage0667
import ImbalancedChen.P2Winner9NumericalPage0668
import ImbalancedChen.P2Winner9NumericalPage0669
import ImbalancedChen.P2Winner9NumericalPage0670
import ImbalancedChen.P2Winner9NumericalPage0671

namespace ImbalancedChen.P2Winner9NumericalCheck41
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 10496 256
    P2Winner9CompleteSeedBlock41.rows := by
  change Checked (fun _ r => checkSelected r = true) 10496 256 ([
    P2Winner9CompleteSeedBlock41.pages[0]!,
    P2Winner9CompleteSeedBlock41.pages[1]!,
    P2Winner9CompleteSeedBlock41.pages[2]!,
    P2Winner9CompleteSeedBlock41.pages[3]!,
    P2Winner9CompleteSeedBlock41.pages[4]!,
    P2Winner9CompleteSeedBlock41.pages[5]!,
    P2Winner9CompleteSeedBlock41.pages[6]!,
    P2Winner9CompleteSeedBlock41.pages[7]!,
    P2Winner9CompleteSeedBlock41.pages[8]!,
    P2Winner9CompleteSeedBlock41.pages[9]!,
    P2Winner9CompleteSeedBlock41.pages[10]!,
    P2Winner9CompleteSeedBlock41.pages[11]!,
    P2Winner9CompleteSeedBlock41.pages[12]!,
    P2Winner9CompleteSeedBlock41.pages[13]!,
    P2Winner9CompleteSeedBlock41.pages[14]!,
    P2Winner9CompleteSeedBlock41.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0656.checked.flatten_cons <|
    P2Winner9NumericalPage0657.checked.flatten_cons <|
    P2Winner9NumericalPage0658.checked.flatten_cons <|
    P2Winner9NumericalPage0659.checked.flatten_cons <|
    P2Winner9NumericalPage0660.checked.flatten_cons <|
    P2Winner9NumericalPage0661.checked.flatten_cons <|
    P2Winner9NumericalPage0662.checked.flatten_cons <|
    P2Winner9NumericalPage0663.checked.flatten_cons <|
    P2Winner9NumericalPage0664.checked.flatten_cons <|
    P2Winner9NumericalPage0665.checked.flatten_cons <|
    P2Winner9NumericalPage0666.checked.flatten_cons <|
    P2Winner9NumericalPage0667.checked.flatten_cons <|
    P2Winner9NumericalPage0668.checked.flatten_cons <|
    P2Winner9NumericalPage0669.checked.flatten_cons <|
    P2Winner9NumericalPage0670.checked.flatten_cons <|
    P2Winner9NumericalPage0671.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck41
