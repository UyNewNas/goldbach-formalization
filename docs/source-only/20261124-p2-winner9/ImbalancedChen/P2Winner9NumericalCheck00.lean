import ImbalancedChen.P2Winner9NumericalPage0000
import ImbalancedChen.P2Winner9NumericalPage0001
import ImbalancedChen.P2Winner9NumericalPage0002
import ImbalancedChen.P2Winner9NumericalPage0003
import ImbalancedChen.P2Winner9NumericalPage0004
import ImbalancedChen.P2Winner9NumericalPage0005
import ImbalancedChen.P2Winner9NumericalPage0006
import ImbalancedChen.P2Winner9NumericalPage0007
import ImbalancedChen.P2Winner9NumericalPage0008
import ImbalancedChen.P2Winner9NumericalPage0009
import ImbalancedChen.P2Winner9NumericalPage0010
import ImbalancedChen.P2Winner9NumericalPage0011
import ImbalancedChen.P2Winner9NumericalPage0012
import ImbalancedChen.P2Winner9NumericalPage0013
import ImbalancedChen.P2Winner9NumericalPage0014
import ImbalancedChen.P2Winner9NumericalPage0015

namespace ImbalancedChen.P2Winner9NumericalCheck00
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 0 256
    P2Winner9CompleteSeedBlock00.rows := by
  change Checked (fun _ r => checkSelected r = true) 0 256 ([
    P2Winner9CompleteSeedBlock00.pages[0]!,
    P2Winner9CompleteSeedBlock00.pages[1]!,
    P2Winner9CompleteSeedBlock00.pages[2]!,
    P2Winner9CompleteSeedBlock00.pages[3]!,
    P2Winner9CompleteSeedBlock00.pages[4]!,
    P2Winner9CompleteSeedBlock00.pages[5]!,
    P2Winner9CompleteSeedBlock00.pages[6]!,
    P2Winner9CompleteSeedBlock00.pages[7]!,
    P2Winner9CompleteSeedBlock00.pages[8]!,
    P2Winner9CompleteSeedBlock00.pages[9]!,
    P2Winner9CompleteSeedBlock00.pages[10]!,
    P2Winner9CompleteSeedBlock00.pages[11]!,
    P2Winner9CompleteSeedBlock00.pages[12]!,
    P2Winner9CompleteSeedBlock00.pages[13]!,
    P2Winner9CompleteSeedBlock00.pages[14]!,
    P2Winner9CompleteSeedBlock00.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0000.checked.flatten_cons <|
    P2Winner9NumericalPage0001.checked.flatten_cons <|
    P2Winner9NumericalPage0002.checked.flatten_cons <|
    P2Winner9NumericalPage0003.checked.flatten_cons <|
    P2Winner9NumericalPage0004.checked.flatten_cons <|
    P2Winner9NumericalPage0005.checked.flatten_cons <|
    P2Winner9NumericalPage0006.checked.flatten_cons <|
    P2Winner9NumericalPage0007.checked.flatten_cons <|
    P2Winner9NumericalPage0008.checked.flatten_cons <|
    P2Winner9NumericalPage0009.checked.flatten_cons <|
    P2Winner9NumericalPage0010.checked.flatten_cons <|
    P2Winner9NumericalPage0011.checked.flatten_cons <|
    P2Winner9NumericalPage0012.checked.flatten_cons <|
    P2Winner9NumericalPage0013.checked.flatten_cons <|
    P2Winner9NumericalPage0014.checked.flatten_cons <|
    P2Winner9NumericalPage0015.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck00
