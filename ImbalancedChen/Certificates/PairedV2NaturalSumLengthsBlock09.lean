import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock09

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block09_lengths :
    block09.map List.length = [147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163] := by
  change [approximations470.length, approximations471.length, approximations472.length, approximations473.length, approximations474.length, approximations475.length, approximations476.length, approximations477.length, approximations478.length, approximations479.length, approximations480.length, approximations481.length, approximations482.length, approximations483.length, approximations484.length, approximations485.length] = _
  (rw [strip470_length, strip471_length, strip472_length, strip473_length, strip474_length, strip475_length, strip476_length, strip477_length, strip478_length, strip479_length, strip480_length, strip481_length, strip482_length, strip483_length, strip484_length, strip485_length]; rfl)

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
