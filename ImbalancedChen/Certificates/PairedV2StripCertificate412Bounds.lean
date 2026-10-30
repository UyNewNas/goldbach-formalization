import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip412_firstU : firstU (⟨86, by decide⟩ : Fin 186) = 425 := by
  rfl

theorem strip412_row_count : 512 - firstU (⟨86, by decide⟩ : Fin 186) = 87 := by
  rw [strip412_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
