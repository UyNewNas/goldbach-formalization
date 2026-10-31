import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip510_firstU : firstU (⟨184, by decide⟩ : Fin 186) = 322 := by
  rfl

theorem strip510_row_count : 512 - firstU (⟨184, by decide⟩ : Fin 186) = 190 := by
  rw [strip510_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
