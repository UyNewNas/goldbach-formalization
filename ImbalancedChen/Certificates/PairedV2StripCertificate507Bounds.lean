import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip507_firstU : firstU (⟨181, by decide⟩ : Fin 186) = 325 := by
  rfl

theorem strip507_row_count : 512 - firstU (⟨181, by decide⟩ : Fin 186) = 187 := by
  rw [strip507_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
