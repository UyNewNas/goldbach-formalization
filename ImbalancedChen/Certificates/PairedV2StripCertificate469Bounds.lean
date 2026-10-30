import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip469_firstU : firstU (⟨143, by decide⟩ : Fin 186) = 365 := by
  rfl

theorem strip469_row_count : 512 - firstU (⟨143, by decide⟩ : Fin 186) = 147 := by
  rw [strip469_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
