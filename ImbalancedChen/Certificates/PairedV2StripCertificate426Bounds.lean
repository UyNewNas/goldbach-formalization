import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip426_firstU : firstU (⟨100, by decide⟩ : Fin 186) = 410 := by
  rfl

theorem strip426_row_count : 512 - firstU (⟨100, by decide⟩ : Fin 186) = 102 := by
  rw [strip426_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
