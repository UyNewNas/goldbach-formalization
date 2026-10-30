import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip415_firstU : firstU (⟨89, by decide⟩ : Fin 186) = 422 := by
  rfl

theorem strip415_row_count : 512 - firstU (⟨89, by decide⟩ : Fin 186) = 90 := by
  rw [strip415_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
