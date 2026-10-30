import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip411_firstU : firstU (⟨85, by decide⟩ : Fin 186) = 426 := by
  rfl

theorem strip411_row_count : 512 - firstU (⟨85, by decide⟩ : Fin 186) = 86 := by
  rw [strip411_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
