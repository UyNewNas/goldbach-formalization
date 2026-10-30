import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip436_firstU : firstU (⟨110, by decide⟩ : Fin 186) = 400 := by
  rfl

theorem strip436_row_count : 512 - firstU (⟨110, by decide⟩ : Fin 186) = 112 := by
  rw [strip436_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
