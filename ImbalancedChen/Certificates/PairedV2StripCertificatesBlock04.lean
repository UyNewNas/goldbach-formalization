import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip390_checked : ∀ j : Fin (512 - firstU (⟨64, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨64, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨64, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip391_checked : ∀ j : Fin (512 - firstU (⟨65, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨65, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨65, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip392_checked : ∀ j : Fin (512 - firstU (⟨66, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨66, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨66, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip393_checked : ∀ j : Fin (512 - firstU (⟨67, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨67, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨67, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip394_checked : ∀ j : Fin (512 - firstU (⟨68, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨68, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨68, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip395_checked : ∀ j : Fin (512 - firstU (⟨69, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨69, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨69, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip396_checked : ∀ j : Fin (512 - firstU (⟨70, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨70, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨70, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip397_checked : ∀ j : Fin (512 - firstU (⟨71, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨71, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨71, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip398_checked : ∀ j : Fin (512 - firstU (⟨72, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨72, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨72, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip399_checked : ∀ j : Fin (512 - firstU (⟨73, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨73, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨73, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip400_checked : ∀ j : Fin (512 - firstU (⟨74, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨74, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨74, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip401_checked : ∀ j : Fin (512 - firstU (⟨75, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨75, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨75, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip402_checked : ∀ j : Fin (512 - firstU (⟨76, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨76, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨76, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip403_checked : ∀ j : Fin (512 - firstU (⟨77, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨77, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨77, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip404_checked : ∀ j : Fin (512 - firstU (⟨78, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨78, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨78, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip405_checked : ∀ j : Fin (512 - firstU (⟨79, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨79, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨79, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock04_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock04 k) := by
  fin_cases k
  · exact strip390_checked
  · exact strip391_checked
  · exact strip392_checked
  · exact strip393_checked
  · exact strip394_checked
  · exact strip395_checked
  · exact strip396_checked
  · exact strip397_checked
  · exact strip398_checked
  · exact strip399_checked
  · exact strip400_checked
  · exact strip401_checked
  · exact strip402_checked
  · exact strip403_checked
  · exact strip404_checked
  · exact strip405_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
