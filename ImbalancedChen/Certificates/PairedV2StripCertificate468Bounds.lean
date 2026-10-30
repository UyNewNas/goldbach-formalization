import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip468_firstU : firstU (⟨142, by decide⟩ : Fin 186) = 367 := by
  rfl

theorem strip468_row_count : 512 - firstU (⟨142, by decide⟩ : Fin 186) = 145 := by
  rw [strip468_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
