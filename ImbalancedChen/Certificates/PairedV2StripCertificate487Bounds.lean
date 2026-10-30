import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip487_firstU : firstU (⟨161, by decide⟩ : Fin 186) = 347 := by
  rfl

theorem strip487_row_count : 512 - firstU (⟨161, by decide⟩ : Fin 186) = 165 := by
  rw [strip487_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
