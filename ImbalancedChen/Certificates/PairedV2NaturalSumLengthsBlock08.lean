import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock08

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block08_lengths :
    block08.map List.length = [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 147] := by
  change [approximations454.length, approximations455.length, approximations456.length, approximations457.length, approximations458.length, approximations459.length, approximations460.length, approximations461.length, approximations462.length, approximations463.length, approximations464.length, approximations465.length, approximations466.length, approximations467.length, approximations468.length, approximations469.length] = _
  rw [strip454_length, strip455_length, strip456_length, strip457_length, strip458_length, strip459_length, strip460_length, strip461_length, strip462_length, strip463_length, strip464_length, strip465_length, strip466_length, strip467_length, strip468_length, strip469_length] <;> rfl

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
