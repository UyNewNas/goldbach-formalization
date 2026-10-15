import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock00

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block00_lengths :
    block00.map List.length = [1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 10, 11, 12, 13, 14, 15] := by
  change [approximations326.length, approximations327.length, approximations328.length, approximations329.length, approximations330.length, approximations331.length, approximations332.length, approximations333.length, approximations334.length, approximations335.length, approximations336.length, approximations337.length, approximations338.length, approximations339.length, approximations340.length, approximations341.length] = _
  (rw [strip326_length, strip327_length, strip328_length, strip329_length, strip330_length, strip331_length, strip332_length, strip333_length, strip334_length, strip335_length, strip336_length, strip337_length, strip338_length, strip339_length, strip340_length, strip341_length]; rfl)

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
