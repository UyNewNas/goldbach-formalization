import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock10

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block10_lengths :
    block10.map List.length = [164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180] := by
  change [approximations486.length, approximations487.length, approximations488.length, approximations489.length, approximations490.length, approximations491.length, approximations492.length, approximations493.length, approximations494.length, approximations495.length, approximations496.length, approximations497.length, approximations498.length, approximations499.length, approximations500.length, approximations501.length] = _
  rw [strip486_length, strip487_length, strip488_length, strip489_length, strip490_length, strip491_length, strip492_length, strip493_length, strip494_length, strip495_length, strip496_length, strip497_length, strip498_length, strip499_length, strip500_length, strip501_length]

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
