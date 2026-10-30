import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip410_firstU : firstU (⟨84, by decide⟩ : Fin 186) = 427 := by
  rfl

theorem strip410_row_count : 512 - firstU (⟨84, by decide⟩ : Fin 186) = 85 := by
  rw [strip410_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
