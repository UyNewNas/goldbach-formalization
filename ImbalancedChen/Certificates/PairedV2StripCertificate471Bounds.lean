import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip471_firstU : firstU (⟨145, by decide⟩ : Fin 186) = 364 := by
  rfl

theorem strip471_row_count : 512 - firstU (⟨145, by decide⟩ : Fin 186) = 148 := by
  rw [strip471_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
