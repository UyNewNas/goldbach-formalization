import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip446_firstU : firstU (⟨120, by decide⟩ : Fin 186) = 390 := by
  rfl

theorem strip446_row_count : 512 - firstU (⟨120, by decide⟩ : Fin 186) = 122 := by
  rw [strip446_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
