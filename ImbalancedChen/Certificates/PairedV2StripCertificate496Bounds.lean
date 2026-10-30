import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip496_firstU : firstU (⟨170, by decide⟩ : Fin 186) = 337 := by
  rfl

theorem strip496_row_count : 512 - firstU (⟨170, by decide⟩ : Fin 186) = 175 := by
  rw [strip496_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
