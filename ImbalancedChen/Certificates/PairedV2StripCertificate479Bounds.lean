import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip479_firstU : firstU (⟨153, by decide⟩ : Fin 186) = 355 := by
  rfl

theorem strip479_row_count : 512 - firstU (⟨153, by decide⟩ : Fin 186) = 157 := by
  rw [strip479_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
