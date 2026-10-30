import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip413_firstU : firstU (⟨87, by decide⟩ : Fin 186) = 424 := by
  rfl

theorem strip413_row_count : 512 - firstU (⟨87, by decide⟩ : Fin 186) = 88 := by
  rw [strip413_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
