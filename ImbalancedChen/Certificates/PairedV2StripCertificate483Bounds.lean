import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip483_firstU : firstU (⟨157, by decide⟩ : Fin 186) = 351 := by
  rfl

theorem strip483_row_count : 512 - firstU (⟨157, by decide⟩ : Fin 186) = 161 := by
  rw [strip483_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
