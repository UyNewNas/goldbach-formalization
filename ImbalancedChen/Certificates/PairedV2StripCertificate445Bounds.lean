import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip445_firstU : firstU (⟨119, by decide⟩ : Fin 186) = 391 := by
  rfl

theorem strip445_row_count : 512 - firstU (⟨119, by decide⟩ : Fin 186) = 121 := by
  rw [strip445_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
