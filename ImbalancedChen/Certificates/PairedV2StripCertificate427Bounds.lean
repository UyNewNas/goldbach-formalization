import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip427_firstU : firstU (⟨101, by decide⟩ : Fin 186) = 409 := by
  rfl

theorem strip427_row_count : 512 - firstU (⟨101, by decide⟩ : Fin 186) = 103 := by
  rw [strip427_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
