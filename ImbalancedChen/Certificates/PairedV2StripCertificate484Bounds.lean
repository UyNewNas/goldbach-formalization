import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip484_firstU : firstU (⟨158, by decide⟩ : Fin 186) = 350 := by
  rfl

theorem strip484_row_count : 512 - firstU (⟨158, by decide⟩ : Fin 186) = 162 := by
  rw [strip484_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
