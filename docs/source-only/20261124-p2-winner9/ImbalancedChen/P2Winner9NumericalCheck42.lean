import ImbalancedChen.P2Winner9NumericalPage0672
import ImbalancedChen.P2Winner9NumericalPage0673
import ImbalancedChen.P2Winner9NumericalPage0674
import ImbalancedChen.P2Winner9NumericalPage0675
import ImbalancedChen.P2Winner9NumericalPage0676
import ImbalancedChen.P2Winner9NumericalPage0677
import ImbalancedChen.P2Winner9NumericalPage0678
import ImbalancedChen.P2Winner9NumericalPage0679
import ImbalancedChen.P2Winner9NumericalPage0680
import ImbalancedChen.P2Winner9NumericalPage0681
import ImbalancedChen.P2Winner9NumericalPage0682
import ImbalancedChen.P2Winner9NumericalPage0683
import ImbalancedChen.P2Winner9NumericalPage0684
import ImbalancedChen.P2Winner9NumericalPage0685
import ImbalancedChen.P2Winner9NumericalPage0686
import ImbalancedChen.P2Winner9NumericalPage0687

namespace ImbalancedChen.P2Winner9NumericalCheck42
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 10752 256
    P2Winner9CompleteSeedBlock42.rows := by
  change Checked (fun _ r => checkSelected r = true) 10752 256 ([
    P2Winner9CompleteSeedBlock42.pages[0]!,
    P2Winner9CompleteSeedBlock42.pages[1]!,
    P2Winner9CompleteSeedBlock42.pages[2]!,
    P2Winner9CompleteSeedBlock42.pages[3]!,
    P2Winner9CompleteSeedBlock42.pages[4]!,
    P2Winner9CompleteSeedBlock42.pages[5]!,
    P2Winner9CompleteSeedBlock42.pages[6]!,
    P2Winner9CompleteSeedBlock42.pages[7]!,
    P2Winner9CompleteSeedBlock42.pages[8]!,
    P2Winner9CompleteSeedBlock42.pages[9]!,
    P2Winner9CompleteSeedBlock42.pages[10]!,
    P2Winner9CompleteSeedBlock42.pages[11]!,
    P2Winner9CompleteSeedBlock42.pages[12]!,
    P2Winner9CompleteSeedBlock42.pages[13]!,
    P2Winner9CompleteSeedBlock42.pages[14]!,
    P2Winner9CompleteSeedBlock42.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0672.checked.flatten_cons <|
    P2Winner9NumericalPage0673.checked.flatten_cons <|
    P2Winner9NumericalPage0674.checked.flatten_cons <|
    P2Winner9NumericalPage0675.checked.flatten_cons <|
    P2Winner9NumericalPage0676.checked.flatten_cons <|
    P2Winner9NumericalPage0677.checked.flatten_cons <|
    P2Winner9NumericalPage0678.checked.flatten_cons <|
    P2Winner9NumericalPage0679.checked.flatten_cons <|
    P2Winner9NumericalPage0680.checked.flatten_cons <|
    P2Winner9NumericalPage0681.checked.flatten_cons <|
    P2Winner9NumericalPage0682.checked.flatten_cons <|
    P2Winner9NumericalPage0683.checked.flatten_cons <|
    P2Winner9NumericalPage0684.checked.flatten_cons <|
    P2Winner9NumericalPage0685.checked.flatten_cons <|
    P2Winner9NumericalPage0686.checked.flatten_cons <|
    P2Winner9NumericalPage0687.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck42
