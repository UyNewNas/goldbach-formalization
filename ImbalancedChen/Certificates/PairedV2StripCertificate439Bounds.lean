import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip439_firstU : firstU (⟨113, by decide⟩ : Fin 186) = 397 := by
  rfl

theorem strip439_row_count : 512 - firstU (⟨113, by decide⟩ : Fin 186) = 115 := by
  rw [strip439_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
