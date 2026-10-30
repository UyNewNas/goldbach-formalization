import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip497_firstU : firstU (⟨171, by decide⟩ : Fin 186) = 336 := by
  rfl

theorem strip497_row_count : 512 - firstU (⟨171, by decide⟩ : Fin 186) = 176 := by
  rw [strip497_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
