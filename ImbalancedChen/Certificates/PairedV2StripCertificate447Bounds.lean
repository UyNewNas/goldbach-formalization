import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip447_firstU : firstU (⟨121, by decide⟩ : Fin 186) = 389 := by
  rfl

theorem strip447_row_count : 512 - firstU (⟨121, by decide⟩ : Fin 186) = 123 := by
  rw [strip447_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
