import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip443_firstU : firstU (⟨117, by decide⟩ : Fin 186) = 393 := by
  rfl

theorem strip443_row_count : 512 - firstU (⟨117, by decide⟩ : Fin 186) = 119 := by
  rw [strip443_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
