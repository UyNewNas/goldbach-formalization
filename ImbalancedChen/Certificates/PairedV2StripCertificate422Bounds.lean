import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip422_firstU : firstU (⟨96, by decide⟩ : Fin 186) = 415 := by
  rfl

theorem strip422_row_count : 512 - firstU (⟨96, by decide⟩ : Fin 186) = 97 := by
  rw [strip422_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
