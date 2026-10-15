import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock07

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block07_lengths :
    block07.map List.length = [114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 129, 130] := by
  change [approximations438.length, approximations439.length, approximations440.length, approximations441.length, approximations442.length, approximations443.length, approximations444.length, approximations445.length, approximations446.length, approximations447.length, approximations448.length, approximations449.length, approximations450.length, approximations451.length, approximations452.length, approximations453.length] = _
  rw [strip438_length, strip439_length, strip440_length, strip441_length, strip442_length, strip443_length, strip444_length, strip445_length, strip446_length, strip447_length, strip448_length, strip449_length, strip450_length, strip451_length, strip452_length, strip453_length] <;> rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
