import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock05

/-! Reuse the accepted strip length facts, at most sixteen per module. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block05_lengths :
    block05.map List.length = [81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96] := by
  change [approximations406.length, approximations407.length, approximations408.length, approximations409.length, approximations410.length, approximations411.length, approximations412.length, approximations413.length, approximations414.length, approximations415.length, approximations416.length, approximations417.length, approximations418.length, approximations419.length, approximations420.length, approximations421.length] = _
  (rw [strip406_length, strip407_length, strip408_length, strip409_length, strip410_length, strip411_length, strip412_length, strip413_length, strip414_length, strip415_length, strip416_length, strip417_length, strip418_length, strip419_length, strip420_length, strip421_length]; rfl)

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
