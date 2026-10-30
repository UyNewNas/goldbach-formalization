import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip485_firstU : firstU (⟨159, by decide⟩ : Fin 186) = 349 := by
  rfl

theorem strip485_row_count : 512 - firstU (⟨159, by decide⟩ : Fin 186) = 163 := by
  rw [strip485_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
