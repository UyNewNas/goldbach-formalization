import ImbalancedChen.P2Winner9NumericalPage0688
import ImbalancedChen.P2Winner9NumericalPage0689

namespace ImbalancedChen.P2Winner9NumericalCheck43
open P2Winner9SelectedArchiveChecker (checkSelected)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000

theorem checked : Checked (fun _ r => checkSelected r = true) 11008 18
    P2Winner9CompleteSeedBlock43.rows := by
  change Checked (fun _ r => checkSelected r = true) 11008 18 ([
    P2Winner9CompleteSeedBlock43.pages[0]!,
    P2Winner9CompleteSeedBlock43.pages[1]!]).toArray.flatten
  exact
    P2Winner9NumericalPage0688.checked.flatten_cons <|
    P2Winner9NumericalPage0689.checked.flatten_single

end ImbalancedChen.P2Winner9NumericalCheck43
