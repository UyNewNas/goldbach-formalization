import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip476_firstU : firstU (⟨150, by decide⟩ : Fin 186) = 358 := by
  rfl

theorem strip476_row_count : 512 - firstU (⟨150, by decide⟩ : Fin 186) = 154 := by
  rw [strip476_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
