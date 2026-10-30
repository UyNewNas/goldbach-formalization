import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip435_firstU : firstU (⟨109, by decide⟩ : Fin 186) = 401 := by
  rfl

theorem strip435_row_count : 512 - firstU (⟨109, by decide⟩ : Fin 186) = 111 := by
  rw [strip435_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
