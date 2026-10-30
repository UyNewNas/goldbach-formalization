import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip432_firstU : firstU (⟨106, by decide⟩ : Fin 186) = 404 := by
  rfl

theorem strip432_row_count : 512 - firstU (⟨106, by decide⟩ : Fin 186) = 108 := by
  rw [strip432_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
