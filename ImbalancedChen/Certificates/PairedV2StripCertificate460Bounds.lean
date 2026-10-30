import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip460_firstU : firstU (⟨134, by decide⟩ : Fin 186) = 375 := by
  rfl

theorem strip460_row_count : 512 - firstU (⟨134, by decide⟩ : Fin 186) = 137 := by
  rw [strip460_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
