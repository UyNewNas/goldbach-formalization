import ImbalancedChen.P2Winner9CompleteSeedBlock43
import ImbalancedChen.P2Winner9SeedArchiveChecks

namespace ImbalancedChen.P2Winner9SeedArchiveCheck43
open P2Winner9SeedArchiveChecks

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem page00 :
    Checked ArchiveRowCheck 11008 16 (P2Winner9CompleteSeedBlock43.pages[0]!) := by
  decide +kernel

private theorem page01 :
    Checked ArchiveRowCheck 11024 2 (P2Winner9CompleteSeedBlock43.pages[1]!) := by
  decide +kernel

theorem checked : Checked ArchiveRowCheck 11008 18 P2Winner9CompleteSeedBlock43.rows := by
  change Checked ArchiveRowCheck 11008 18 ([
    P2Winner9CompleteSeedBlock43.pages[0]!,
    P2Winner9CompleteSeedBlock43.pages[1]!]).toArray.flatten
  exact
    page00.flatten_cons <|
    page01.flatten_single

end ImbalancedChen.P2Winner9SeedArchiveCheck43
