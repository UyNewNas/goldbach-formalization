import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock02

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block02_lengths :
    block02.map List.length = [33, 34, 35, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48] := by
  change [approximations358.length, approximations359.length, approximations360.length, approximations361.length, approximations362.length, approximations363.length, approximations364.length, approximations365.length, approximations366.length, approximations367.length, approximations368.length, approximations369.length, approximations370.length, approximations371.length, approximations372.length, approximations373.length] = _
  rw [strip358_length, strip359_length, strip360_length, strip361_length, strip362_length, strip363_length, strip364_length, strip365_length, strip366_length, strip367_length, strip368_length, strip369_length, strip370_length, strip371_length, strip372_length, strip373_length]

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
