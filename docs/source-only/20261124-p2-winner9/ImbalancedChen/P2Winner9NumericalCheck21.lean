import ImbalancedChen.P2Winner9NumericalPage0336
import ImbalancedChen.P2Winner9NumericalPage0337
import ImbalancedChen.P2Winner9NumericalPage0338
import ImbalancedChen.P2Winner9NumericalPage0339
import ImbalancedChen.P2Winner9NumericalPage0340
import ImbalancedChen.P2Winner9NumericalPage0341
import ImbalancedChen.P2Winner9NumericalPage0342
import ImbalancedChen.P2Winner9NumericalPage0343
import ImbalancedChen.P2Winner9NumericalPage0344
import ImbalancedChen.P2Winner9NumericalPage0345
import ImbalancedChen.P2Winner9NumericalPage0346
import ImbalancedChen.P2Winner9NumericalPage0347
import ImbalancedChen.P2Winner9NumericalPage0348
import ImbalancedChen.P2Winner9NumericalPage0349
import ImbalancedChen.P2Winner9NumericalPage0350
import ImbalancedChen.P2Winner9NumericalPage0351

namespace ImbalancedChen.P2Winner9NumericalCheck21
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 5376 256
    P2Winner9CompleteSeedBlock21.rows := by
  change Checked (fun _ r => checkSelected r = true) 5376 256 ([
    P2Winner9CompleteSeedBlock21.pages[0]!,
    P2Winner9CompleteSeedBlock21.pages[1]!,
    P2Winner9CompleteSeedBlock21.pages[2]!,
    P2Winner9CompleteSeedBlock21.pages[3]!,
    P2Winner9CompleteSeedBlock21.pages[4]!,
    P2Winner9CompleteSeedBlock21.pages[5]!,
    P2Winner9CompleteSeedBlock21.pages[6]!,
    P2Winner9CompleteSeedBlock21.pages[7]!,
    P2Winner9CompleteSeedBlock21.pages[8]!,
    P2Winner9CompleteSeedBlock21.pages[9]!,
    P2Winner9CompleteSeedBlock21.pages[10]!,
    P2Winner9CompleteSeedBlock21.pages[11]!,
    P2Winner9CompleteSeedBlock21.pages[12]!,
    P2Winner9CompleteSeedBlock21.pages[13]!,
    P2Winner9CompleteSeedBlock21.pages[14]!,
    P2Winner9CompleteSeedBlock21.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0336.checked.flatten_cons <|
    P2Winner9NumericalPage0337.checked.flatten_cons <|
    P2Winner9NumericalPage0338.checked.flatten_cons <|
    P2Winner9NumericalPage0339.checked.flatten_cons <|
    P2Winner9NumericalPage0340.checked.flatten_cons <|
    P2Winner9NumericalPage0341.checked.flatten_cons <|
    P2Winner9NumericalPage0342.checked.flatten_cons <|
    P2Winner9NumericalPage0343.checked.flatten_cons <|
    P2Winner9NumericalPage0344.checked.flatten_cons <|
    P2Winner9NumericalPage0345.checked.flatten_cons <|
    P2Winner9NumericalPage0346.checked.flatten_cons <|
    P2Winner9NumericalPage0347.checked.flatten_cons <|
    P2Winner9NumericalPage0348.checked.flatten_cons <|
    P2Winner9NumericalPage0349.checked.flatten_cons <|
    P2Winner9NumericalPage0350.checked.flatten_cons <|
    P2Winner9NumericalPage0351.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck21
