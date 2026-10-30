import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip434_firstU : firstU (⟨108, by decide⟩ : Fin 186) = 402 := by
  rfl

theorem strip434_row_count : 512 - firstU (⟨108, by decide⟩ : Fin 186) = 110 := by
  rw [strip434_firstU]

end ImbalancedChen.Certificates.PairedV2.FullMask
