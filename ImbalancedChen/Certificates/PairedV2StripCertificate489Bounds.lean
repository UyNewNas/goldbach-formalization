import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip489_firstU : firstU (⟨163, by decide⟩ : Fin 186) = 344 := by
  rfl

theorem strip489_row_count : 512 - firstU (⟨163, by decide⟩ : Fin 186) = 168 := by
  rw [strip489_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
