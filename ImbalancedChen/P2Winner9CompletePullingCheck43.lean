import ImbalancedChen.P2Winner9CompleteSeedBlock43
import ImbalancedChen.P2Winner9CompletePullingFlags

namespace ImbalancedChen.P2Winner9CompletePullingCheck43
open P2Winner9CompletePullingFlags (witnesses checkedRow orderStep)
open P2Winner9PullingOrderChecks (Consecutive)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem orderPage00 : Consecutive orderStep 11008 16 := by
  decide +kernel

private theorem orderPage01 : Consecutive orderStep 11024 1 := by
  decide +kernel

theorem order_checked : Consecutive orderStep 11008 17 := by
  exact
    orderPage00.append <|
    orderPage01

private theorem page00 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 11008 16 (P2Winner9CompleteSeedBlock43.pages[0]!) := by
  decide +kernel

private theorem page01 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 11024 2 (P2Winner9CompleteSeedBlock43.pages[1]!) := by
  decide +kernel

theorem checked : Checked (fun ordinal row => checkedRow ordinal row = true) 11008 18 P2Winner9CompleteSeedBlock43.rows := by
  change Checked (fun ordinal row => checkedRow ordinal row = true) 11008 18 ([
    P2Winner9CompleteSeedBlock43.pages[0]!,
    P2Winner9CompleteSeedBlock43.pages[1]!
  ].toArray.flatten)
  exact
    page00.flatten_cons <|
    page01.flatten_single

end ImbalancedChen.P2Winner9CompletePullingCheck43
