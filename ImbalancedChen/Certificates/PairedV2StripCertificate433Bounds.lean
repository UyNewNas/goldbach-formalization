import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip433_firstU : firstU (⟨107, by decide⟩ : Fin 186) = 403 := by
  rfl

theorem strip433_row_count : 512 - firstU (⟨107, by decide⟩ : Fin 186) = 109 := by
  rw [strip433_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
