import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip504_firstU : firstU (⟨178, by decide⟩ : Fin 186) = 329 := by
  rfl

theorem strip504_row_count : 512 - firstU (⟨178, by decide⟩ : Fin 186) = 183 := by
  rw [strip504_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
