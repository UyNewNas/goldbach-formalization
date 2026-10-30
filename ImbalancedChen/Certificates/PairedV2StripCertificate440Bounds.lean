import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip440_firstU : firstU (⟨114, by decide⟩ : Fin 186) = 396 := by
  rfl

theorem strip440_row_count : 512 - firstU (⟨114, by decide⟩ : Fin 186) = 116 := by
  rw [strip440_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
