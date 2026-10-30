import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip424_firstU : firstU (⟨98, by decide⟩ : Fin 186) = 412 := by
  rfl

theorem strip424_row_count : 512 - firstU (⟨98, by decide⟩ : Fin 186) = 100 := by
  rw [strip424_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
