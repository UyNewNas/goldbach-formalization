import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock03

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block03_lengths :
    block03.map List.length = [49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64] := by
  change [approximations374.length, approximations375.length, approximations376.length, approximations377.length, approximations378.length, approximations379.length, approximations380.length, approximations381.length, approximations382.length, approximations383.length, approximations384.length, approximations385.length, approximations386.length, approximations387.length, approximations388.length, approximations389.length] = _
  rw [strip374_length, strip375_length, strip376_length, strip377_length, strip378_length, strip379_length, strip380_length, strip381_length, strip382_length, strip383_length, strip384_length, strip385_length, strip386_length, strip387_length, strip388_length, strip389_length]

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
