import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip494_firstU : firstU (⟨168, by decide⟩ : Fin 186) = 339 := by
  rfl

theorem strip494_row_count : 512 - firstU (⟨168, by decide⟩ : Fin 186) = 173 := by
  rw [strip494_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
