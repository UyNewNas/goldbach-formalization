import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip508_firstU : firstU (⟨182, by decide⟩ : Fin 186) = 324 := by
  rfl

theorem strip508_row_count : 512 - firstU (⟨182, by decide⟩ : Fin 186) = 188 := by
  rw [strip508_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
