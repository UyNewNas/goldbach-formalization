import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip442_firstU : firstU (⟨116, by decide⟩ : Fin 186) = 394 := by
  rfl

theorem strip442_row_count : 512 - firstU (⟨116, by decide⟩ : Fin 186) = 118 := by
  rw [strip442_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
