import ImbalancedChen.Certificates.PairedV2FullCertificateData

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

theorem strip342_checked : ∀ j : Fin (512 - firstU (⟨16, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨16, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨16, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip343_checked : ∀ j : Fin (512 - firstU (⟨17, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨17, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨17, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip344_checked : ∀ j : Fin (512 - firstU (⟨18, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨18, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨18, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip345_checked : ∀ j : Fin (512 - firstU (⟨19, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨19, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨19, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip346_checked : ∀ j : Fin (512 - firstU (⟨20, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨20, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨20, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip347_checked : ∀ j : Fin (512 - firstU (⟨21, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨21, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨21, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip348_checked : ∀ j : Fin (512 - firstU (⟨22, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨22, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨22, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip349_checked : ∀ j : Fin (512 - firstU (⟨23, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨23, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨23, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip350_checked : ∀ j : Fin (512 - firstU (⟨24, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨24, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨24, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip351_checked : ∀ j : Fin (512 - firstU (⟨25, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨25, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨25, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip352_checked : ∀ j : Fin (512 - firstU (⟨26, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨26, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨26, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip353_checked : ∀ j : Fin (512 - firstU (⟨27, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨27, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨27, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip354_checked : ∀ j : Fin (512 - firstU (⟨28, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨28, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨28, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip355_checked : ∀ j : Fin (512 - firstU (⟨29, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨29, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨29, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip356_checked : ∀ j : Fin (512 - firstU (⟨30, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨30, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨30, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip357_checked : ∀ j : Fin (512 - firstU (⟨31, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨31, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨31, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

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

theorem strip374_checked : ∀ j : Fin (512 - firstU (⟨48, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨48, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨48, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip375_checked : ∀ j : Fin (512 - firstU (⟨49, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨49, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨49, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip376_checked : ∀ j : Fin (512 - firstU (⟨50, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨50, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨50, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip377_checked : ∀ j : Fin (512 - firstU (⟨51, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨51, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨51, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip378_checked : ∀ j : Fin (512 - firstU (⟨52, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨52, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨52, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip379_checked : ∀ j : Fin (512 - firstU (⟨53, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨53, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨53, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip380_checked : ∀ j : Fin (512 - firstU (⟨54, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨54, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨54, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip381_checked : ∀ j : Fin (512 - firstU (⟨55, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨55, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨55, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip382_checked : ∀ j : Fin (512 - firstU (⟨56, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨56, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨56, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip383_checked : ∀ j : Fin (512 - firstU (⟨57, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨57, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨57, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip384_checked : ∀ j : Fin (512 - firstU (⟨58, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨58, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨58, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip385_checked : ∀ j : Fin (512 - firstU (⟨59, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨59, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨59, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip386_checked : ∀ j : Fin (512 - firstU (⟨60, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨60, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨60, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip387_checked : ∀ j : Fin (512 - firstU (⟨61, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨61, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨61, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip388_checked : ∀ j : Fin (512 - firstU (⟨62, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨62, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨62, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip389_checked : ∀ j : Fin (512 - firstU (⟨63, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨63, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨63, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

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

theorem strip406_checked : ∀ j : Fin (512 - firstU (⟨80, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨80, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨80, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip407_checked : ∀ j : Fin (512 - firstU (⟨81, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨81, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip408_checked : ∀ j : Fin (512 - firstU (⟨82, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨82, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip409_checked : ∀ j : Fin (512 - firstU (⟨83, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨83, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip410_checked : ∀ j : Fin (512 - firstU (⟨84, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨84, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip411_checked : ∀ j : Fin (512 - firstU (⟨85, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨85, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip412_checked : ∀ j : Fin (512 - firstU (⟨86, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨86, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨86, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip413_checked : ∀ j : Fin (512 - firstU (⟨87, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨87, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip414_checked : ∀ j : Fin (512 - firstU (⟨88, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨88, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip415_checked : ∀ j : Fin (512 - firstU (⟨89, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨89, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨89, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip416_checked : ∀ j : Fin (512 - firstU (⟨90, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨90, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip417_checked : ∀ j : Fin (512 - firstU (⟨91, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨91, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip418_checked : ∀ j : Fin (512 - firstU (⟨92, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨92, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip419_checked : ∀ j : Fin (512 - firstU (⟨93, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨93, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨93, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip420_checked : ∀ j : Fin (512 - firstU (⟨94, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨94, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip421_checked : ∀ j : Fin (512 - firstU (⟨95, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨95, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip422_checked : ∀ j : Fin (512 - firstU (⟨96, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨96, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip423_checked : ∀ j : Fin (512 - firstU (⟨97, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨97, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip424_checked : ∀ j : Fin (512 - firstU (⟨98, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨98, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip425_checked : ∀ j : Fin (512 - firstU (⟨99, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨99, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip426_checked : ∀ j : Fin (512 - firstU (⟨100, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨100, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip427_checked : ∀ j : Fin (512 - firstU (⟨101, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨101, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip428_checked : ∀ j : Fin (512 - firstU (⟨102, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨102, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨102, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip429_checked : ∀ j : Fin (512 - firstU (⟨103, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨103, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip430_checked : ∀ j : Fin (512 - firstU (⟨104, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨104, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip431_checked : ∀ j : Fin (512 - firstU (⟨105, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨105, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip432_checked : ∀ j : Fin (512 - firstU (⟨106, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨106, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip433_checked : ∀ j : Fin (512 - firstU (⟨107, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨107, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip434_checked : ∀ j : Fin (512 - firstU (⟨108, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨108, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip435_checked : ∀ j : Fin (512 - firstU (⟨109, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨109, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip436_checked : ∀ j : Fin (512 - firstU (⟨110, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨110, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip437_checked : ∀ j : Fin (512 - firstU (⟨111, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨111, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip438_checked : ∀ j : Fin (512 - firstU (⟨112, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨112, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨112, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip439_checked : ∀ j : Fin (512 - firstU (⟨113, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨113, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip440_checked : ∀ j : Fin (512 - firstU (⟨114, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨114, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip441_checked : ∀ j : Fin (512 - firstU (⟨115, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨115, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip442_checked : ∀ j : Fin (512 - firstU (⟨116, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip443_checked : ∀ j : Fin (512 - firstU (⟨117, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨117, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip444_checked : ∀ j : Fin (512 - firstU (⟨118, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨118, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip445_checked : ∀ j : Fin (512 - firstU (⟨119, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨119, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip446_checked : ∀ j : Fin (512 - firstU (⟨120, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨120, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip447_checked : ∀ j : Fin (512 - firstU (⟨121, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨121, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨121, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip448_checked : ∀ j : Fin (512 - firstU (⟨122, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨122, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨122, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip449_checked : ∀ j : Fin (512 - firstU (⟨123, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨123, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip450_checked : ∀ j : Fin (512 - firstU (⟨124, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨124, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip451_checked : ∀ j : Fin (512 - firstU (⟨125, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨125, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨125, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip452_checked : ∀ j : Fin (512 - firstU (⟨126, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨126, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip453_checked : ∀ j : Fin (512 - firstU (⟨127, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨127, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

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

theorem strip470_checked : ∀ j : Fin (512 - firstU (⟨144, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨144, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip471_checked : ∀ j : Fin (512 - firstU (⟨145, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨145, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip472_checked : ∀ j : Fin (512 - firstU (⟨146, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨146, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip473_checked : ∀ j : Fin (512 - firstU (⟨147, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨147, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip474_checked : ∀ j : Fin (512 - firstU (⟨148, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨148, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip475_checked : ∀ j : Fin (512 - firstU (⟨149, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨149, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip476_checked : ∀ j : Fin (512 - firstU (⟨150, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨150, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip477_checked : ∀ j : Fin (512 - firstU (⟨151, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨151, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip478_checked : ∀ j : Fin (512 - firstU (⟨152, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨152, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip479_checked : ∀ j : Fin (512 - firstU (⟨153, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨153, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip480_checked : ∀ j : Fin (512 - firstU (⟨154, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨154, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip481_checked : ∀ j : Fin (512 - firstU (⟨155, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨155, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip482_checked : ∀ j : Fin (512 - firstU (⟨156, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨156, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip483_checked : ∀ j : Fin (512 - firstU (⟨157, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨157, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip484_checked : ∀ j : Fin (512 - firstU (⟨158, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨158, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip485_checked : ∀ j : Fin (512 - firstU (⟨159, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨159, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip486_checked : ∀ j : Fin (512 - firstU (⟨160, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨160, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip487_checked : ∀ j : Fin (512 - firstU (⟨161, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨161, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip488_checked : ∀ j : Fin (512 - firstU (⟨162, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨162, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip489_checked : ∀ j : Fin (512 - firstU (⟨163, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨163, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip490_checked : ∀ j : Fin (512 - firstU (⟨164, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨164, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip491_checked : ∀ j : Fin (512 - firstU (⟨165, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨165, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip492_checked : ∀ j : Fin (512 - firstU (⟨166, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨166, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip493_checked : ∀ j : Fin (512 - firstU (⟨167, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨167, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨167, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip494_checked : ∀ j : Fin (512 - firstU (⟨168, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨168, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip495_checked : ∀ j : Fin (512 - firstU (⟨169, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨169, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip496_checked : ∀ j : Fin (512 - firstU (⟨170, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨170, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨170, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip497_checked : ∀ j : Fin (512 - firstU (⟨171, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨171, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip498_checked : ∀ j : Fin (512 - firstU (⟨172, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨172, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip499_checked : ∀ j : Fin (512 - firstU (⟨173, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨173, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip500_checked : ∀ j : Fin (512 - firstU (⟨174, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨174, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip501_checked : ∀ j : Fin (512 - firstU (⟨175, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨175, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip502_checked : ∀ j : Fin (512 - firstU (⟨176, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨176, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip503_checked : ∀ j : Fin (512 - firstU (⟨177, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨177, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip504_checked : ∀ j : Fin (512 - firstU (⟨178, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨178, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip505_checked : ∀ j : Fin (512 - firstU (⟨179, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨179, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip506_checked : ∀ j : Fin (512 - firstU (⟨180, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨180, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip507_checked : ∀ j : Fin (512 - firstU (⟨181, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨181, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip508_checked : ∀ j : Fin (512 - firstU (⟨182, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨182, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip509_checked : ∀ j : Fin (512 - firstU (⟨183, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨183, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip510_checked : ∀ j : Fin (512 - firstU (⟨184, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨184, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip511_checked : ∀ j : Fin (512 - firstU (⟨185, by decide⟩ : Fin 186)),
    (makeCertificate (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row) (approximation (⟨(⟨185, by decide⟩ : Fin 186), j⟩ : Row))).check = true := by
  decide +kernel

theorem strip_certificates_checked (i : Fin 186) (j : Fin (512 - firstU i)) :
    (makeCertificate ⟨i,j⟩ (approximation ⟨i,j⟩)).check = true := by
  fin_cases i
  · exact strip326_checked j
  · exact strip327_checked j
  · exact strip328_checked j
  · exact strip329_checked j
  · exact strip330_checked j
  · exact strip331_checked j
  · exact strip332_checked j
  · exact strip333_checked j
  · exact strip334_checked j
  · exact strip335_checked j
  · exact strip336_checked j
  · exact strip337_checked j
  · exact strip338_checked j
  · exact strip339_checked j
  · exact strip340_checked j
  · exact strip341_checked j
  · exact strip342_checked j
  · exact strip343_checked j
  · exact strip344_checked j
  · exact strip345_checked j
  · exact strip346_checked j
  · exact strip347_checked j
  · exact strip348_checked j
  · exact strip349_checked j
  · exact strip350_checked j
  · exact strip351_checked j
  · exact strip352_checked j
  · exact strip353_checked j
  · exact strip354_checked j
  · exact strip355_checked j
  · exact strip356_checked j
  · exact strip357_checked j
  · exact strip358_checked j
  · exact strip359_checked j
  · exact strip360_checked j
  · exact strip361_checked j
  · exact strip362_checked j
  · exact strip363_checked j
  · exact strip364_checked j
  · exact strip365_checked j
  · exact strip366_checked j
  · exact strip367_checked j
  · exact strip368_checked j
  · exact strip369_checked j
  · exact strip370_checked j
  · exact strip371_checked j
  · exact strip372_checked j
  · exact strip373_checked j
  · exact strip374_checked j
  · exact strip375_checked j
  · exact strip376_checked j
  · exact strip377_checked j
  · exact strip378_checked j
  · exact strip379_checked j
  · exact strip380_checked j
  · exact strip381_checked j
  · exact strip382_checked j
  · exact strip383_checked j
  · exact strip384_checked j
  · exact strip385_checked j
  · exact strip386_checked j
  · exact strip387_checked j
  · exact strip388_checked j
  · exact strip389_checked j
  · exact strip390_checked j
  · exact strip391_checked j
  · exact strip392_checked j
  · exact strip393_checked j
  · exact strip394_checked j
  · exact strip395_checked j
  · exact strip396_checked j
  · exact strip397_checked j
  · exact strip398_checked j
  · exact strip399_checked j
  · exact strip400_checked j
  · exact strip401_checked j
  · exact strip402_checked j
  · exact strip403_checked j
  · exact strip404_checked j
  · exact strip405_checked j
  · exact strip406_checked j
  · exact strip407_checked j
  · exact strip408_checked j
  · exact strip409_checked j
  · exact strip410_checked j
  · exact strip411_checked j
  · exact strip412_checked j
  · exact strip413_checked j
  · exact strip414_checked j
  · exact strip415_checked j
  · exact strip416_checked j
  · exact strip417_checked j
  · exact strip418_checked j
  · exact strip419_checked j
  · exact strip420_checked j
  · exact strip421_checked j
  · exact strip422_checked j
  · exact strip423_checked j
  · exact strip424_checked j
  · exact strip425_checked j
  · exact strip426_checked j
  · exact strip427_checked j
  · exact strip428_checked j
  · exact strip429_checked j
  · exact strip430_checked j
  · exact strip431_checked j
  · exact strip432_checked j
  · exact strip433_checked j
  · exact strip434_checked j
  · exact strip435_checked j
  · exact strip436_checked j
  · exact strip437_checked j
  · exact strip438_checked j
  · exact strip439_checked j
  · exact strip440_checked j
  · exact strip441_checked j
  · exact strip442_checked j
  · exact strip443_checked j
  · exact strip444_checked j
  · exact strip445_checked j
  · exact strip446_checked j
  · exact strip447_checked j
  · exact strip448_checked j
  · exact strip449_checked j
  · exact strip450_checked j
  · exact strip451_checked j
  · exact strip452_checked j
  · exact strip453_checked j
  · exact strip454_checked j
  · exact strip455_checked j
  · exact strip456_checked j
  · exact strip457_checked j
  · exact strip458_checked j
  · exact strip459_checked j
  · exact strip460_checked j
  · exact strip461_checked j
  · exact strip462_checked j
  · exact strip463_checked j
  · exact strip464_checked j
  · exact strip465_checked j
  · exact strip466_checked j
  · exact strip467_checked j
  · exact strip468_checked j
  · exact strip469_checked j
  · exact strip470_checked j
  · exact strip471_checked j
  · exact strip472_checked j
  · exact strip473_checked j
  · exact strip474_checked j
  · exact strip475_checked j
  · exact strip476_checked j
  · exact strip477_checked j
  · exact strip478_checked j
  · exact strip479_checked j
  · exact strip480_checked j
  · exact strip481_checked j
  · exact strip482_checked j
  · exact strip483_checked j
  · exact strip484_checked j
  · exact strip485_checked j
  · exact strip486_checked j
  · exact strip487_checked j
  · exact strip488_checked j
  · exact strip489_checked j
  · exact strip490_checked j
  · exact strip491_checked j
  · exact strip492_checked j
  · exact strip493_checked j
  · exact strip494_checked j
  · exact strip495_checked j
  · exact strip496_checked j
  · exact strip497_checked j
  · exact strip498_checked j
  · exact strip499_checked j
  · exact strip500_checked j
  · exact strip501_checked j
  · exact strip502_checked j
  · exact strip503_checked j
  · exact strip504_checked j
  · exact strip505_checked j
  · exact strip506_checked j
  · exact strip507_checked j
  · exact strip508_checked j
  · exact strip509_checked j
  · exact strip510_checked j
  · exact strip511_checked j

end ImbalancedChen.Certificates.PairedV2.FullMask
