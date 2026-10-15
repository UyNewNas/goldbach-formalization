import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock11

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block11_lengths :
    block11.map List.length = [181, 182, 183, 184, 185, 187, 188, 189, 190, 191] := by
  change [approximations502.length, approximations503.length, approximations504.length, approximations505.length, approximations506.length, approximations507.length, approximations508.length, approximations509.length, approximations510.length, approximations511.length] = _
  rw [strip502_length, strip503_length, strip504_length, strip505_length, strip506_length, strip507_length, strip508_length, strip509_length, strip510_length, strip511_length]

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
