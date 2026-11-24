import ImbalancedChen.P2Winner9NumericalPage0272
import ImbalancedChen.P2Winner9NumericalPage0273
import ImbalancedChen.P2Winner9NumericalPage0274
import ImbalancedChen.P2Winner9NumericalPage0275
import ImbalancedChen.P2Winner9NumericalPage0276
import ImbalancedChen.P2Winner9NumericalPage0277
import ImbalancedChen.P2Winner9NumericalPage0278
import ImbalancedChen.P2Winner9NumericalPage0279
import ImbalancedChen.P2Winner9NumericalPage0280
import ImbalancedChen.P2Winner9NumericalPage0281
import ImbalancedChen.P2Winner9NumericalPage0282
import ImbalancedChen.P2Winner9NumericalPage0283
import ImbalancedChen.P2Winner9NumericalPage0284
import ImbalancedChen.P2Winner9NumericalPage0285
import ImbalancedChen.P2Winner9NumericalPage0286
import ImbalancedChen.P2Winner9NumericalPage0287

namespace ImbalancedChen.P2Winner9NumericalCheck17
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 4352 256
    P2Winner9CompleteSeedBlock17.rows := by
  change Checked (fun _ r => checkSelected r = true) 4352 256 ([
    P2Winner9CompleteSeedBlock17.pages[0]!,
    P2Winner9CompleteSeedBlock17.pages[1]!,
    P2Winner9CompleteSeedBlock17.pages[2]!,
    P2Winner9CompleteSeedBlock17.pages[3]!,
    P2Winner9CompleteSeedBlock17.pages[4]!,
    P2Winner9CompleteSeedBlock17.pages[5]!,
    P2Winner9CompleteSeedBlock17.pages[6]!,
    P2Winner9CompleteSeedBlock17.pages[7]!,
    P2Winner9CompleteSeedBlock17.pages[8]!,
    P2Winner9CompleteSeedBlock17.pages[9]!,
    P2Winner9CompleteSeedBlock17.pages[10]!,
    P2Winner9CompleteSeedBlock17.pages[11]!,
    P2Winner9CompleteSeedBlock17.pages[12]!,
    P2Winner9CompleteSeedBlock17.pages[13]!,
    P2Winner9CompleteSeedBlock17.pages[14]!,
    P2Winner9CompleteSeedBlock17.pages[15]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0272.checked.flatten_cons <|
    P2Winner9NumericalPage0273.checked.flatten_cons <|
    P2Winner9NumericalPage0274.checked.flatten_cons <|
    P2Winner9NumericalPage0275.checked.flatten_cons <|
    P2Winner9NumericalPage0276.checked.flatten_cons <|
    P2Winner9NumericalPage0277.checked.flatten_cons <|
    P2Winner9NumericalPage0278.checked.flatten_cons <|
    P2Winner9NumericalPage0279.checked.flatten_cons <|
    P2Winner9NumericalPage0280.checked.flatten_cons <|
    P2Winner9NumericalPage0281.checked.flatten_cons <|
    P2Winner9NumericalPage0282.checked.flatten_cons <|
    P2Winner9NumericalPage0283.checked.flatten_cons <|
    P2Winner9NumericalPage0284.checked.flatten_cons <|
    P2Winner9NumericalPage0285.checked.flatten_cons <|
    P2Winner9NumericalPage0286.checked.flatten_cons <|
    P2Winner9NumericalPage0287.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck17
