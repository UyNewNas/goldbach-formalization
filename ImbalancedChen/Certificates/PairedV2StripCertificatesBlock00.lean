import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip326_checked : ∀ j : Fin (512 - firstU (⟨0, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨0, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨0, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip327_checked : ∀ j : Fin (512 - firstU (⟨1, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨1, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨1, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip328_checked : ∀ j : Fin (512 - firstU (⟨2, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨2, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨2, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip329_checked : ∀ j : Fin (512 - firstU (⟨3, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨3, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨3, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip330_checked : ∀ j : Fin (512 - firstU (⟨4, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨4, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨4, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip331_checked : ∀ j : Fin (512 - firstU (⟨5, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨5, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨5, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip332_checked : ∀ j : Fin (512 - firstU (⟨6, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨6, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨6, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip333_checked : ∀ j : Fin (512 - firstU (⟨7, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨7, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨7, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip334_checked : ∀ j : Fin (512 - firstU (⟨8, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨8, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨8, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip335_checked : ∀ j : Fin (512 - firstU (⟨9, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨9, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨9, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip336_checked : ∀ j : Fin (512 - firstU (⟨10, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨10, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨10, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip337_checked : ∀ j : Fin (512 - firstU (⟨11, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨11, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨11, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip338_checked : ∀ j : Fin (512 - firstU (⟨12, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨12, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨12, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip339_checked : ∀ j : Fin (512 - firstU (⟨13, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨13, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨13, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip340_checked : ∀ j : Fin (512 - firstU (⟨14, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨14, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨14, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip341_checked : ∀ j : Fin (512 - firstU (⟨15, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨15, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨15, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock00_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock00 k) := by
  fin_cases k
  · exact strip326_checked
  · exact strip327_checked
  · exact strip328_checked
  · exact strip329_checked
  · exact strip330_checked
  · exact strip331_checked
  · exact strip332_checked
  · exact strip333_checked
  · exact strip334_checked
  · exact strip335_checked
  · exact strip336_checked
  · exact strip337_checked
  · exact strip338_checked
  · exact strip339_checked
  · exact strip340_checked
  · exact strip341_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
