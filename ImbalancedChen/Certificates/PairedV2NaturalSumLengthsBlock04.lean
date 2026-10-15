import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock04

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block04_lengths :
    block04.map List.length = [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80] := by
  change [approximations390.length, approximations391.length, approximations392.length, approximations393.length, approximations394.length, approximations395.length, approximations396.length, approximations397.length, approximations398.length, approximations399.length, approximations400.length, approximations401.length, approximations402.length, approximations403.length, approximations404.length, approximations405.length] = _
  rw [strip390_length, strip391_length, strip392_length, strip393_length, strip394_length, strip395_length, strip396_length, strip397_length, strip398_length, strip399_length, strip400_length, strip401_length, strip402_length, strip403_length, strip404_length, strip405_length] <;> rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
