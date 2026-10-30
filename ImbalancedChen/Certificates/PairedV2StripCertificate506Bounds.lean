import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip506_firstU : firstU (⟨180, by decide⟩ : Fin 186) = 327 := by
  rfl

theorem strip506_row_count : 512 - firstU (⟨180, by decide⟩ : Fin 186) = 185 := by
  rw [strip506_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
