import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip472_firstU : firstU (⟨146, by decide⟩ : Fin 186) = 363 := by
  rfl

theorem strip472_row_count : 512 - firstU (⟨146, by decide⟩ : Fin 186) = 149 := by
  rw [strip472_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
