import ImbalancedChen.P2Winner9NumericalPage0176
import ImbalancedChen.P2Winner9NumericalPage0177
import ImbalancedChen.P2Winner9NumericalPage0178
import ImbalancedChen.P2Winner9NumericalPage0179
import ImbalancedChen.P2Winner9NumericalPage0180
import ImbalancedChen.P2Winner9NumericalPage0181
import ImbalancedChen.P2Winner9NumericalPage0182
import ImbalancedChen.P2Winner9NumericalPage0183
import ImbalancedChen.P2Winner9NumericalPage0184
import ImbalancedChen.P2Winner9NumericalPage0185
import ImbalancedChen.P2Winner9NumericalPage0186
import ImbalancedChen.P2Winner9NumericalPage0187
import ImbalancedChen.P2Winner9NumericalPage0188
import ImbalancedChen.P2Winner9NumericalPage0189
import ImbalancedChen.P2Winner9NumericalPage0190
import ImbalancedChen.P2Winner9NumericalPage0191

namespace ImbalancedChen.P2Winner9NumericalCheck11
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 2816 256
    P2Winner9CompleteSeedBlock11.rows := by
  change Checked (fun _ r => checkSelected r = true) 2816 256 ([
    P2Winner9CompleteSeedBlock11.pages[0]!,
    P2Winner9CompleteSeedBlock11.pages[1]!,
    P2Winner9CompleteSeedBlock11.pages[2]!,
    P2Winner9CompleteSeedBlock11.pages[3]!,
    P2Winner9CompleteSeedBlock11.pages[4]!,
    P2Winner9CompleteSeedBlock11.pages[5]!,
    P2Winner9CompleteSeedBlock11.pages[6]!,
    P2Winner9CompleteSeedBlock11.pages[7]!,
    P2Winner9CompleteSeedBlock11.pages[8]!,
    P2Winner9CompleteSeedBlock11.pages[9]!,
    P2Winner9CompleteSeedBlock11.pages[10]!,
    P2Winner9CompleteSeedBlock11.pages[11]!,
    P2Winner9CompleteSeedBlock11.pages[12]!,
    P2Winner9CompleteSeedBlock11.pages[13]!,
    P2Winner9CompleteSeedBlock11.pages[14]!,
    P2Winner9CompleteSeedBlock11.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0176.checked.flatten_cons <|
    P2Winner9NumericalPage0177.checked.flatten_cons <|
    P2Winner9NumericalPage0178.checked.flatten_cons <|
    P2Winner9NumericalPage0179.checked.flatten_cons <|
    P2Winner9NumericalPage0180.checked.flatten_cons <|
    P2Winner9NumericalPage0181.checked.flatten_cons <|
    P2Winner9NumericalPage0182.checked.flatten_cons <|
    P2Winner9NumericalPage0183.checked.flatten_cons <|
    P2Winner9NumericalPage0184.checked.flatten_cons <|
    P2Winner9NumericalPage0185.checked.flatten_cons <|
    P2Winner9NumericalPage0186.checked.flatten_cons <|
    P2Winner9NumericalPage0187.checked.flatten_cons <|
    P2Winner9NumericalPage0188.checked.flatten_cons <|
    P2Winner9NumericalPage0189.checked.flatten_cons <|
    P2Winner9NumericalPage0190.checked.flatten_cons <|
    P2Winner9NumericalPage0191.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck11
