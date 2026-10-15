import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock06

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block06_lengths :
    block06.map List.length = [97, 98, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113] := by
  change [approximations422.length, approximations423.length, approximations424.length, approximations425.length, approximations426.length, approximations427.length, approximations428.length, approximations429.length, approximations430.length, approximations431.length, approximations432.length, approximations433.length, approximations434.length, approximations435.length, approximations436.length, approximations437.length] = _
  rw [strip422_length, strip423_length, strip424_length, strip425_length, strip426_length, strip427_length, strip428_length, strip429_length, strip430_length, strip431_length, strip432_length, strip433_length, strip434_length, strip435_length, strip436_length, strip437_length] <;> rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
