import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip454_checked : ∀ j : Fin (512 - firstU (⟨128, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨128, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨128, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip455_checked : ∀ j : Fin (512 - firstU (⟨129, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨129, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨129, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip456_checked : ∀ j : Fin (512 - firstU (⟨130, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨130, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨130, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip457_checked : ∀ j : Fin (512 - firstU (⟨131, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨131, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨131, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip458_checked : ∀ j : Fin (512 - firstU (⟨132, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨132, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨132, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip459_checked : ∀ j : Fin (512 - firstU (⟨133, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip460_checked : ∀ j : Fin (512 - firstU (⟨134, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨134, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨134, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip461_checked : ∀ j : Fin (512 - firstU (⟨135, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨135, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨135, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip462_checked : ∀ j : Fin (512 - firstU (⟨136, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨136, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨136, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip463_checked : ∀ j : Fin (512 - firstU (⟨137, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨137, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨137, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip464_checked : ∀ j : Fin (512 - firstU (⟨138, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨138, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨138, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip465_checked : ∀ j : Fin (512 - firstU (⟨139, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨139, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨139, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip466_checked : ∀ j : Fin (512 - firstU (⟨140, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨140, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨140, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip467_checked : ∀ j : Fin (512 - firstU (⟨141, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨141, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨141, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip468_checked : ∀ j : Fin (512 - firstU (⟨142, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨142, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨142, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip469_checked : ∀ j : Fin (512 - firstU (⟨143, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨143, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨143, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock08_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock08 k) := by
  fin_cases k
  · exact strip454_checked
  · exact strip455_checked
  · exact strip456_checked
  · exact strip457_checked
  · exact strip458_checked
  · exact strip459_checked
  · exact strip460_checked
  · exact strip461_checked
  · exact strip462_checked
  · exact strip463_checked
  · exact strip464_checked
  · exact strip465_checked
  · exact strip466_checked
  · exact strip467_checked
  · exact strip468_checked
  · exact strip469_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
