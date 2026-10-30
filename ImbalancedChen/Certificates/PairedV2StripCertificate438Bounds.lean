import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip438_firstU : firstU (⟨112, by decide⟩ : Fin 186) = 398 := by
  rfl

theorem strip438_row_count : 512 - firstU (⟨112, by decide⟩ : Fin 186) = 114 := by
  rw [strip438_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
