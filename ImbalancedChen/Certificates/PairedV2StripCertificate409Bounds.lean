import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip409_firstU : firstU (⟨83, by decide⟩ : Fin 186) = 428 := by
  rfl

theorem strip409_row_count : 512 - firstU (⟨83, by decide⟩ : Fin 186) = 84 := by
  rw [strip409_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
