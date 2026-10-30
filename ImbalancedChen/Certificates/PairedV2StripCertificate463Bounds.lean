import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip463_firstU : firstU (⟨137, by decide⟩ : Fin 186) = 372 := by
  rfl

theorem strip463_row_count : 512 - firstU (⟨137, by decide⟩ : Fin 186) = 140 := by
  rw [strip463_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
