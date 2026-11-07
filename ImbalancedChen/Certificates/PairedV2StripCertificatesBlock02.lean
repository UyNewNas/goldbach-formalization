import ImbalancedChen.Certificates.PairedV2StripCertificatesAssemblyCore

/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.
No row is sampled or dropped, and no native numerical evaluator is used. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem strip358_checked : ∀ j : Fin (512 - firstU (⟨32, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨32, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨32, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip359_checked : ∀ j : Fin (512 - firstU (⟨33, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨33, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨33, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip360_checked : ∀ j : Fin (512 - firstU (⟨34, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨34, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨34, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip361_checked : ∀ j : Fin (512 - firstU (⟨35, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨35, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨35, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip362_checked : ∀ j : Fin (512 - firstU (⟨36, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨36, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨36, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip363_checked : ∀ j : Fin (512 - firstU (⟨37, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨37, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨37, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip364_checked : ∀ j : Fin (512 - firstU (⟨38, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨38, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨38, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip365_checked : ∀ j : Fin (512 - firstU (⟨39, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨39, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨39, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip366_checked : ∀ j : Fin (512 - firstU (⟨40, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨40, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨40, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip367_checked : ∀ j : Fin (512 - firstU (⟨41, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨41, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨41, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip368_checked : ∀ j : Fin (512 - firstU (⟨42, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨42, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨42, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip369_checked : ∀ j : Fin (512 - firstU (⟨43, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨43, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨43, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip370_checked : ∀ j : Fin (512 - firstU (⟨44, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨44, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨44, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip371_checked : ∀ j : Fin (512 - firstU (⟨45, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨45, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨45, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip372_checked : ∀ j : Fin (512 - firstU (⟨46, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨46, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨46, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip373_checked : ∀ j : Fin (512 - firstU (⟨47, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨47, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨47, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

/-- Bounded composition of the original strip checks, with no new check assumption. -/
theorem stripBlock02_checked (k : Fin 16) :
    StripAssembly.StripChecked (StripAssembly.indexBlock02 k) := by
  fin_cases k
  · exact strip358_checked
  · exact strip359_checked
  · exact strip360_checked
  · exact strip361_checked
  · exact strip362_checked
  · exact strip363_checked
  · exact strip364_checked
  · exact strip365_checked
  · exact strip366_checked
  · exact strip367_checked
  · exact strip368_checked
  · exact strip369_checked
  · exact strip370_checked
  · exact strip371_checked
  · exact strip372_checked
  · exact strip373_checked

end ImbalancedChen.Certificates.PairedV2.FullMask
