import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip451_firstU : firstU (⟨125, by decide⟩ : Fin 186) = 385 := by
  rfl

theorem strip451_row_count : 512 - firstU (⟨125, by decide⟩ : Fin 186) = 127 := by
  rw [strip451_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
