import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock01

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block01_lengths :
    block01.map List.length = [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32] := by
  change [approximations342.length, approximations343.length, approximations344.length, approximations345.length, approximations346.length, approximations347.length, approximations348.length, approximations349.length, approximations350.length, approximations351.length, approximations352.length, approximations353.length, approximations354.length, approximations355.length, approximations356.length, approximations357.length] = _
  (rw [strip342_length, strip343_length, strip344_length, strip345_length, strip346_length, strip347_length, strip348_length, strip349_length, strip350_length, strip351_length, strip352_length, strip353_length, strip354_length, strip355_length, strip356_length, strip357_length]; rfl)

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
