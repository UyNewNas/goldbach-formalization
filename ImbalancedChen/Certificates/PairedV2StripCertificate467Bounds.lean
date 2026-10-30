import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip467_firstU : firstU (⟨141, by decide⟩ : Fin 186) = 368 := by
  rfl

theorem strip467_row_count : 512 - firstU (⟨141, by decide⟩ : Fin 186) = 144 := by
  rw [strip467_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
