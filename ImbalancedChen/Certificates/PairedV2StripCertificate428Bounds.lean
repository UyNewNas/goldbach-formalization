import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip428_firstU : firstU (⟨102, by decide⟩ : Fin 186) = 408 := by
  rfl

theorem strip428_row_count : 512 - firstU (⟨102, by decide⟩ : Fin 186) = 104 := by
  rw [strip428_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
