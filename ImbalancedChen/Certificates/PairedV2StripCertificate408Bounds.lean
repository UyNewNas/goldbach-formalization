import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip408_firstU : firstU (⟨82, by decide⟩ : Fin 186) = 429 := by
  rfl

theorem strip408_row_count : 512 - firstU (⟨82, by decide⟩ : Fin 186) = 83 := by
  rw [strip408_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
