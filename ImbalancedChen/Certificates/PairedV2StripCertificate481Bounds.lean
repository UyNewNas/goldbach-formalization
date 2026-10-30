import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip481_firstU : firstU (⟨155, by decide⟩ : Fin 186) = 353 := by
  rfl

theorem strip481_row_count : 512 - firstU (⟨155, by decide⟩ : Fin 186) = 159 := by
  rw [strip481_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
