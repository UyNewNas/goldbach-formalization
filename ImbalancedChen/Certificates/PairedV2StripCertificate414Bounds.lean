import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip414_firstU : firstU (⟨88, by decide⟩ : Fin 186) = 423 := by
  rfl

theorem strip414_row_count : 512 - firstU (⟨88, by decide⟩ : Fin 186) = 89 := by
  rw [strip414_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
