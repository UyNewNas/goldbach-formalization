import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip397_checked : ∀ j : Fin (512 - firstU (⟨71, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨71, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨71, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel


end ImbalancedChen.Certificates.PairedV2.FullMask
