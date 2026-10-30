import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip407_firstU : firstU (⟨81, by decide⟩ : Fin 186) = 430 := by
  rfl

theorem strip407_row_count : 512 - firstU (⟨81, by decide⟩ : Fin 186) = 82 := by
  rw [strip407_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
