import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip444_firstU : firstU (⟨118, by decide⟩ : Fin 186) = 392 := by
  rfl

theorem strip444_row_count : 512 - firstU (⟨118, by decide⟩ : Fin 186) = 120 := by
  rw [strip444_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
