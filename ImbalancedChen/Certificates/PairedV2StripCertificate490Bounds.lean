import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip490_firstU : firstU (⟨164, by decide⟩ : Fin 186) = 343 := by
  rfl

theorem strip490_row_count : 512 - firstU (⟨164, by decide⟩ : Fin 186) = 169 := by
  rw [strip490_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
