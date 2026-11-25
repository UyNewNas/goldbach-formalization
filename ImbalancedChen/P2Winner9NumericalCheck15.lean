import ImbalancedChen.P2Winner9NumericalPage0240
import ImbalancedChen.P2Winner9NumericalPage0241
import ImbalancedChen.P2Winner9NumericalPage0242
import ImbalancedChen.P2Winner9NumericalPage0243
import ImbalancedChen.P2Winner9NumericalPage0244
import ImbalancedChen.P2Winner9NumericalPage0245
import ImbalancedChen.P2Winner9NumericalPage0246
import ImbalancedChen.P2Winner9NumericalPage0247
import ImbalancedChen.P2Winner9NumericalPage0248
import ImbalancedChen.P2Winner9NumericalPage0249
import ImbalancedChen.P2Winner9NumericalPage0250
import ImbalancedChen.P2Winner9NumericalPage0251
import ImbalancedChen.P2Winner9NumericalPage0252
import ImbalancedChen.P2Winner9NumericalPage0253
import ImbalancedChen.P2Winner9NumericalPage0254
import ImbalancedChen.P2Winner9NumericalPage0255

namespace ImbalancedChen.P2Winner9NumericalCheck15
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 3840 256
    P2Winner9CompleteSeedBlock15.rows := by
  change Checked (fun _ r => checkSelected r = true) 3840 256 ([
    P2Winner9CompleteSeedBlock15.pages[0]!,
    P2Winner9CompleteSeedBlock15.pages[1]!,
    P2Winner9CompleteSeedBlock15.pages[2]!,
    P2Winner9CompleteSeedBlock15.pages[3]!,
    P2Winner9CompleteSeedBlock15.pages[4]!,
    P2Winner9CompleteSeedBlock15.pages[5]!,
    P2Winner9CompleteSeedBlock15.pages[6]!,
    P2Winner9CompleteSeedBlock15.pages[7]!,
    P2Winner9CompleteSeedBlock15.pages[8]!,
    P2Winner9CompleteSeedBlock15.pages[9]!,
    P2Winner9CompleteSeedBlock15.pages[10]!,
    P2Winner9CompleteSeedBlock15.pages[11]!,
    P2Winner9CompleteSeedBlock15.pages[12]!,
    P2Winner9CompleteSeedBlock15.pages[13]!,
    P2Winner9CompleteSeedBlock15.pages[14]!,
    P2Winner9CompleteSeedBlock15.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0240.checked.flatten_cons <|
    P2Winner9NumericalPage0241.checked.flatten_cons <|
    P2Winner9NumericalPage0242.checked.flatten_cons <|
    P2Winner9NumericalPage0243.checked.flatten_cons <|
    P2Winner9NumericalPage0244.checked.flatten_cons <|
    P2Winner9NumericalPage0245.checked.flatten_cons <|
    P2Winner9NumericalPage0246.checked.flatten_cons <|
    P2Winner9NumericalPage0247.checked.flatten_cons <|
    P2Winner9NumericalPage0248.checked.flatten_cons <|
    P2Winner9NumericalPage0249.checked.flatten_cons <|
    P2Winner9NumericalPage0250.checked.flatten_cons <|
    P2Winner9NumericalPage0251.checked.flatten_cons <|
    P2Winner9NumericalPage0252.checked.flatten_cons <|
    P2Winner9NumericalPage0253.checked.flatten_cons <|
    P2Winner9NumericalPage0254.checked.flatten_cons <|
    P2Winner9NumericalPage0255.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck15
