import ImbalancedChen.P2Winner9NumericalPage0048
import ImbalancedChen.P2Winner9NumericalPage0049
import ImbalancedChen.P2Winner9NumericalPage0050
import ImbalancedChen.P2Winner9NumericalPage0051
import ImbalancedChen.P2Winner9NumericalPage0052
import ImbalancedChen.P2Winner9NumericalPage0053
import ImbalancedChen.P2Winner9NumericalPage0054
import ImbalancedChen.P2Winner9NumericalPage0055
import ImbalancedChen.P2Winner9NumericalPage0056
import ImbalancedChen.P2Winner9NumericalPage0057
import ImbalancedChen.P2Winner9NumericalPage0058
import ImbalancedChen.P2Winner9NumericalPage0059
import ImbalancedChen.P2Winner9NumericalPage0060
import ImbalancedChen.P2Winner9NumericalPage0061
import ImbalancedChen.P2Winner9NumericalPage0062
import ImbalancedChen.P2Winner9NumericalPage0063

namespace ImbalancedChen.P2Winner9NumericalCheck03
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 768 256
    P2Winner9CompleteSeedBlock03.rows := by
  change Checked (fun _ r => checkSelected r = true) 768 256 ([
    P2Winner9CompleteSeedBlock03.pages[0]!,
    P2Winner9CompleteSeedBlock03.pages[1]!,
    P2Winner9CompleteSeedBlock03.pages[2]!,
    P2Winner9CompleteSeedBlock03.pages[3]!,
    P2Winner9CompleteSeedBlock03.pages[4]!,
    P2Winner9CompleteSeedBlock03.pages[5]!,
    P2Winner9CompleteSeedBlock03.pages[6]!,
    P2Winner9CompleteSeedBlock03.pages[7]!,
    P2Winner9CompleteSeedBlock03.pages[8]!,
    P2Winner9CompleteSeedBlock03.pages[9]!,
    P2Winner9CompleteSeedBlock03.pages[10]!,
    P2Winner9CompleteSeedBlock03.pages[11]!,
    P2Winner9CompleteSeedBlock03.pages[12]!,
    P2Winner9CompleteSeedBlock03.pages[13]!,
    P2Winner9CompleteSeedBlock03.pages[14]!,
    P2Winner9CompleteSeedBlock03.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0048.checked.flatten_cons <|
    P2Winner9NumericalPage0049.checked.flatten_cons <|
    P2Winner9NumericalPage0050.checked.flatten_cons <|
    P2Winner9NumericalPage0051.checked.flatten_cons <|
    P2Winner9NumericalPage0052.checked.flatten_cons <|
    P2Winner9NumericalPage0053.checked.flatten_cons <|
    P2Winner9NumericalPage0054.checked.flatten_cons <|
    P2Winner9NumericalPage0055.checked.flatten_cons <|
    P2Winner9NumericalPage0056.checked.flatten_cons <|
    P2Winner9NumericalPage0057.checked.flatten_cons <|
    P2Winner9NumericalPage0058.checked.flatten_cons <|
    P2Winner9NumericalPage0059.checked.flatten_cons <|
    P2Winner9NumericalPage0060.checked.flatten_cons <|
    P2Winner9NumericalPage0061.checked.flatten_cons <|
    P2Winner9NumericalPage0062.checked.flatten_cons <|
    P2Winner9NumericalPage0063.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck03
