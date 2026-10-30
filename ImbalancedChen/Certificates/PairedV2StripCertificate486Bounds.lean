import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip486_firstU : firstU (⟨160, by decide⟩ : Fin 186) = 348 := by
  rfl

theorem strip486_row_count : 512 - firstU (⟨160, by decide⟩ : Fin 186) = 164 := by
  rw [strip486_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
