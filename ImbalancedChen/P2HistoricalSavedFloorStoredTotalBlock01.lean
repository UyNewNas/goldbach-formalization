import ImbalancedChen.P2HistoricalSavedFloorStoredTotalCore
import ImbalancedChen.P2HistoricalSavedFloorStripData374
import ImbalancedChen.P2HistoricalSavedFloorStripData375
import ImbalancedChen.P2HistoricalSavedFloorStripData376
import ImbalancedChen.P2HistoricalSavedFloorStripData377
import ImbalancedChen.P2HistoricalSavedFloorStripData378
import ImbalancedChen.P2HistoricalSavedFloorStripData379
import ImbalancedChen.P2HistoricalSavedFloorStripData380
import ImbalancedChen.P2HistoricalSavedFloorStripData381
import ImbalancedChen.P2HistoricalSavedFloorStripData382
import ImbalancedChen.P2HistoricalSavedFloorStripData383
import ImbalancedChen.P2HistoricalSavedFloorStripData384
import ImbalancedChen.P2HistoricalSavedFloorStripData385
import ImbalancedChen.P2HistoricalSavedFloorStripData386
import ImbalancedChen.P2HistoricalSavedFloorStripData387
import ImbalancedChen.P2HistoricalSavedFloorStripData388
import ImbalancedChen.P2HistoricalSavedFloorStripData389
import ImbalancedChen.P2HistoricalSavedFloorStripData390
import ImbalancedChen.P2HistoricalSavedFloorStripData391
import ImbalancedChen.P2HistoricalSavedFloorStripData392
import ImbalancedChen.P2HistoricalSavedFloorStripData393
import ImbalancedChen.P2HistoricalSavedFloorStripData394
import ImbalancedChen.P2HistoricalSavedFloorStripData395
import ImbalancedChen.P2HistoricalSavedFloorStripData396
import ImbalancedChen.P2HistoricalSavedFloorStripData397
import ImbalancedChen.P2HistoricalSavedFloorStripData398
import ImbalancedChen.P2HistoricalSavedFloorStripData399
import ImbalancedChen.P2HistoricalSavedFloorStripData400
import ImbalancedChen.P2HistoricalSavedFloorStripData401
import ImbalancedChen.P2HistoricalSavedFloorStripData402
import ImbalancedChen.P2HistoricalSavedFloorStripData403
import ImbalancedChen.P2HistoricalSavedFloorStripData404
import ImbalancedChen.P2HistoricalSavedFloorStripData405
import ImbalancedChen.P2HistoricalSavedFloorStripData406
import ImbalancedChen.P2HistoricalSavedFloorStripData407
import ImbalancedChen.P2HistoricalSavedFloorStripData408
import ImbalancedChen.P2HistoricalSavedFloorStripData409
import ImbalancedChen.P2HistoricalSavedFloorStripData410
import ImbalancedChen.P2HistoricalSavedFloorStripData411
import ImbalancedChen.P2HistoricalSavedFloorStripData412
import ImbalancedChen.P2HistoricalSavedFloorStripData413
import ImbalancedChen.P2HistoricalSavedFloorStripData414
import ImbalancedChen.P2HistoricalSavedFloorStripData415
import ImbalancedChen.P2HistoricalSavedFloorStripData416
import ImbalancedChen.P2HistoricalSavedFloorStripData417
import ImbalancedChen.P2HistoricalSavedFloorStripData418
import ImbalancedChen.P2HistoricalSavedFloorStripData419
import ImbalancedChen.P2HistoricalSavedFloorStripData420
import ImbalancedChen.P2HistoricalSavedFloorStripData421

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotal
open P2HistoricalSavedFloorRowsBinder
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip374_data_checked :
    (frozenSavedStrip374.map FrozenSavedRow.savedQ80).sum = (69659549808423965617 : ℤ) ∧
      frozenSavedStrip374.length = 512 - firstU (⟨48, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip374_sum :
    (∑ j : Fin (512 - firstU (⟨48, by decide⟩ : Fin 186)),
      (frozenSavedStrip374.getD j.val default).savedQ80) = (69659549808423965617 : ℤ) := by
  rw [← strip374_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip374_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip375_data_checked :
    (frozenSavedStrip375.map FrozenSavedRow.savedQ80).sum = (70565650980692376976 : ℤ) ∧
      frozenSavedStrip375.length = 512 - firstU (⟨49, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip375_sum :
    (∑ j : Fin (512 - firstU (⟨49, by decide⟩ : Fin 186)),
      (frozenSavedStrip375.getD j.val default).savedQ80) = (70565650980692376976 : ℤ) := by
  rw [← strip375_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip375_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip376_data_checked :
    (frozenSavedStrip376.map FrozenSavedRow.savedQ80).sum = (71448485752176949282 : ℤ) ∧
      frozenSavedStrip376.length = 512 - firstU (⟨50, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip376_sum :
    (∑ j : Fin (512 - firstU (⟨50, by decide⟩ : Fin 186)),
      (frozenSavedStrip376.getD j.val default).savedQ80) = (71448485752176949282 : ℤ) := by
  rw [← strip376_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip376_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip377_data_checked :
    (frozenSavedStrip377.map FrozenSavedRow.savedQ80).sum = (72308218203010437747 : ℤ) ∧
      frozenSavedStrip377.length = 512 - firstU (⟨51, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip377_sum :
    (∑ j : Fin (512 - firstU (⟨51, by decide⟩ : Fin 186)),
      (frozenSavedStrip377.getD j.val default).savedQ80) = (72308218203010437747 : ℤ) := by
  rw [← strip377_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip377_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip378_data_checked :
    (frozenSavedStrip378.map FrozenSavedRow.savedQ80).sum = (73144455565645040761 : ℤ) ∧
      frozenSavedStrip378.length = 512 - firstU (⟨52, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip378_sum :
    (∑ j : Fin (512 - firstU (⟨52, by decide⟩ : Fin 186)),
      (frozenSavedStrip378.getD j.val default).savedQ80) = (73144455565645040761 : ℤ) := by
  rw [← strip378_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip378_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip379_data_checked :
    (frozenSavedStrip379.map FrozenSavedRow.savedQ80).sum = (73957360544996248851 : ℤ) ∧
      frozenSavedStrip379.length = 512 - firstU (⟨53, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip379_sum :
    (∑ j : Fin (512 - firstU (⟨53, by decide⟩ : Fin 186)),
      (frozenSavedStrip379.getD j.val default).savedQ80) = (73957360544996248851 : ℤ) := by
  rw [← strip379_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip379_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip380_data_checked :
    (frozenSavedStrip380.map FrozenSavedRow.savedQ80).sum = (74751565813110637222 : ℤ) ∧
      frozenSavedStrip380.length = 512 - firstU (⟨54, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip380_sum :
    (∑ j : Fin (512 - firstU (⟨54, by decide⟩ : Fin 186)),
      (frozenSavedStrip380.getD j.val default).savedQ80) = (74751565813110637222 : ℤ) := by
  rw [← strip380_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip380_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip381_data_checked :
    (frozenSavedStrip381.map FrozenSavedRow.savedQ80).sum = (75521862352182654260 : ℤ) ∧
      frozenSavedStrip381.length = 512 - firstU (⟨55, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip381_sum :
    (∑ j : Fin (512 - firstU (⟨55, by decide⟩ : Fin 186)),
      (frozenSavedStrip381.getD j.val default).savedQ80) = (75521862352182654260 : ℤ) := by
  rw [← strip381_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip381_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip382_data_checked :
    (frozenSavedStrip382.map FrozenSavedRow.savedQ80).sum = (76273089807235061936 : ℤ) ∧
      frozenSavedStrip382.length = 512 - firstU (⟨56, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip382_sum :
    (∑ j : Fin (512 - firstU (⟨56, by decide⟩ : Fin 186)),
      (frozenSavedStrip382.getD j.val default).savedQ80) = (76273089807235061936 : ℤ) := by
  rw [← strip382_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip382_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip383_data_checked :
    (frozenSavedStrip383.map FrozenSavedRow.savedQ80).sum = (76995645160058408767 : ℤ) ∧
      frozenSavedStrip383.length = 512 - firstU (⟨57, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip383_sum :
    (∑ j : Fin (512 - firstU (⟨57, by decide⟩ : Fin 186)),
      (frozenSavedStrip383.getD j.val default).savedQ80) = (76995645160058408767 : ℤ) := by
  rw [← strip383_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip383_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip384_data_checked :
    (frozenSavedStrip384.map FrozenSavedRow.savedQ80).sum = (77694292635095144023 : ℤ) ∧
      frozenSavedStrip384.length = 512 - firstU (⟨58, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip384_sum :
    (∑ j : Fin (512 - firstU (⟨58, by decide⟩ : Fin 186)),
      (frozenSavedStrip384.getD j.val default).savedQ80) = (77694292635095144023 : ℤ) := by
  rw [← strip384_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip384_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip385_data_checked :
    (frozenSavedStrip385.map FrozenSavedRow.savedQ80).sum = (78373242476110739512 : ℤ) ∧
      frozenSavedStrip385.length = 512 - firstU (⟨59, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip385_sum :
    (∑ j : Fin (512 - firstU (⟨59, by decide⟩ : Fin 186)),
      (frozenSavedStrip385.getD j.val default).savedQ80) = (78373242476110739512 : ℤ) := by
  rw [← strip385_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip385_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip386_data_checked :
    (frozenSavedStrip386.map FrozenSavedRow.savedQ80).sum = (79023433627580878777 : ℤ) ∧
      frozenSavedStrip386.length = 512 - firstU (⟨60, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip386_sum :
    (∑ j : Fin (512 - firstU (⟨60, by decide⟩ : Fin 186)),
      (frozenSavedStrip386.getD j.val default).savedQ80) = (79023433627580878777 : ℤ) := by
  rw [← strip386_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip386_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip387_data_checked :
    (frozenSavedStrip387.map FrozenSavedRow.savedQ80).sum = (79648997356112387936 : ℤ) ∧
      frozenSavedStrip387.length = 512 - firstU (⟨61, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip387_sum :
    (∑ j : Fin (512 - firstU (⟨61, by decide⟩ : Fin 186)),
      (frozenSavedStrip387.getD j.val default).savedQ80) = (79648997356112387936 : ℤ) := by
  rw [← strip387_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip387_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip388_data_checked :
    (frozenSavedStrip388.map FrozenSavedRow.savedQ80).sum = (80259805286508210672 : ℤ) ∧
      frozenSavedStrip388.length = 512 - firstU (⟨62, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip388_sum :
    (∑ j : Fin (512 - firstU (⟨62, by decide⟩ : Fin 186)),
      (frozenSavedStrip388.getD j.val default).savedQ80) = (80259805286508210672 : ℤ) := by
  rw [← strip388_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip388_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip389_data_checked :
    (frozenSavedStrip389.map FrozenSavedRow.savedQ80).sum = (80841418120587397881 : ℤ) ∧
      frozenSavedStrip389.length = 512 - firstU (⟨63, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip389_sum :
    (∑ j : Fin (512 - firstU (⟨63, by decide⟩ : Fin 186)),
      (frozenSavedStrip389.getD j.val default).savedQ80) = (80841418120587397881 : ℤ) := by
  rw [← strip389_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip389_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip390_data_checked :
    (frozenSavedStrip390.map FrozenSavedRow.savedQ80).sum = (81398033645934297398 : ℤ) ∧
      frozenSavedStrip390.length = 512 - firstU (⟨64, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip390_sum :
    (∑ j : Fin (512 - firstU (⟨64, by decide⟩ : Fin 186)),
      (frozenSavedStrip390.getD j.val default).savedQ80) = (81398033645934297398 : ℤ) := by
  rw [← strip390_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip390_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip391_data_checked :
    (frozenSavedStrip391.map FrozenSavedRow.savedQ80).sum = (81934774451880662403 : ℤ) ∧
      frozenSavedStrip391.length = 512 - firstU (⟨65, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip391_sum :
    (∑ j : Fin (512 - firstU (⟨65, by decide⟩ : Fin 186)),
      (frozenSavedStrip391.getD j.val default).savedQ80) = (81934774451880662403 : ℤ) := by
  rw [← strip391_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip391_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip392_data_checked :
    (frozenSavedStrip392.map FrozenSavedRow.savedQ80).sum = (82441480990650898779 : ℤ) ∧
      frozenSavedStrip392.length = 512 - firstU (⟨66, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip392_sum :
    (∑ j : Fin (512 - firstU (⟨66, by decide⟩ : Fin 186)),
      (frozenSavedStrip392.getD j.val default).savedQ80) = (82441480990650898779 : ℤ) := by
  rw [← strip392_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip392_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip393_data_checked :
    (frozenSavedStrip393.map FrozenSavedRow.savedQ80).sum = (82923189166009281916 : ℤ) ∧
      frozenSavedStrip393.length = 512 - firstU (⟨67, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip393_sum :
    (∑ j : Fin (512 - firstU (⟨67, by decide⟩ : Fin 186)),
      (frozenSavedStrip393.getD j.val default).savedQ80) = (82923189166009281916 : ℤ) := by
  rw [← strip393_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip393_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip394_data_checked :
    (frozenSavedStrip394.map FrozenSavedRow.savedQ80).sum = (83384368079924327771 : ℤ) ∧
      frozenSavedStrip394.length = 512 - firstU (⟨68, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip394_sum :
    (∑ j : Fin (512 - firstU (⟨68, by decide⟩ : Fin 186)),
      (frozenSavedStrip394.getD j.val default).savedQ80) = (83384368079924327771 : ℤ) := by
  rw [← strip394_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip394_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip395_data_checked :
    (frozenSavedStrip395.map FrozenSavedRow.savedQ80).sum = (83815412517903779375 : ℤ) ∧
      frozenSavedStrip395.length = 512 - firstU (⟨69, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip395_sum :
    (∑ j : Fin (512 - firstU (⟨69, by decide⟩ : Fin 186)),
      (frozenSavedStrip395.getD j.val default).savedQ80) = (83815412517903779375 : ℤ) := by
  rw [← strip395_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip395_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip396_data_checked :
    (frozenSavedStrip396.map FrozenSavedRow.savedQ80).sum = (84225682550264878197 : ℤ) ∧
      frozenSavedStrip396.length = 512 - firstU (⟨70, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip396_sum :
    (∑ j : Fin (512 - firstU (⟨70, by decide⟩ : Fin 186)),
      (frozenSavedStrip396.getD j.val default).savedQ80) = (84225682550264878197 : ℤ) := by
  rw [← strip396_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip396_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip397_data_checked :
    (frozenSavedStrip397.map FrozenSavedRow.savedQ80).sum = (84615524751946324938 : ℤ) ∧
      frozenSavedStrip397.length = 512 - firstU (⟨71, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip397_sum :
    (∑ j : Fin (512 - firstU (⟨71, by decide⟩ : Fin 186)),
      (frozenSavedStrip397.getD j.val default).savedQ80) = (84615524751946324938 : ℤ) := by
  rw [← strip397_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip397_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip398_data_checked :
    (frozenSavedStrip398.map FrozenSavedRow.savedQ80).sum = (84979371042398021998 : ℤ) ∧
      frozenSavedStrip398.length = 512 - firstU (⟨72, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip398_sum :
    (∑ j : Fin (512 - firstU (⟨72, by decide⟩ : Fin 186)),
      (frozenSavedStrip398.getD j.val default).savedQ80) = (84979371042398021998 : ℤ) := by
  rw [← strip398_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip398_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip399_data_checked :
    (frozenSavedStrip399.map FrozenSavedRow.savedQ80).sum = (85317552928184889405 : ℤ) ∧
      frozenSavedStrip399.length = 512 - firstU (⟨73, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip399_sum :
    (∑ j : Fin (512 - firstU (⟨73, by decide⟩ : Fin 186)),
      (frozenSavedStrip399.getD j.val default).savedQ80) = (85317552928184889405 : ℤ) := by
  rw [← strip399_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip399_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip400_data_checked :
    (frozenSavedStrip400.map FrozenSavedRow.savedQ80).sum = (85629478096626639455 : ℤ) ∧
      frozenSavedStrip400.length = 512 - firstU (⟨74, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip400_sum :
    (∑ j : Fin (512 - firstU (⟨74, by decide⟩ : Fin 186)),
      (frozenSavedStrip400.getD j.val default).savedQ80) = (85629478096626639455 : ℤ) := by
  rw [← strip400_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip400_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip401_data_checked :
    (frozenSavedStrip401.map FrozenSavedRow.savedQ80).sum = (85915476485964730747 : ℤ) ∧
      frozenSavedStrip401.length = 512 - firstU (⟨75, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip401_sum :
    (∑ j : Fin (512 - firstU (⟨75, by decide⟩ : Fin 186)),
      (frozenSavedStrip401.getD j.val default).savedQ80) = (85915476485964730747 : ℤ) := by
  rw [← strip401_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip401_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip402_data_checked :
    (frozenSavedStrip402.map FrozenSavedRow.savedQ80).sum = (86174954156819379282 : ℤ) ∧
      frozenSavedStrip402.length = 512 - firstU (⟨76, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip402_sum :
    (∑ j : Fin (512 - firstU (⟨76, by decide⟩ : Fin 186)),
      (frozenSavedStrip402.getD j.val default).savedQ80) = (86174954156819379282 : ℤ) := by
  rw [← strip402_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip402_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip403_data_checked :
    (frozenSavedStrip403.map FrozenSavedRow.savedQ80).sum = (86408239450934727921 : ℤ) ∧
      frozenSavedStrip403.length = 512 - firstU (⟨77, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip403_sum :
    (∑ j : Fin (512 - firstU (⟨77, by decide⟩ : Fin 186)),
      (frozenSavedStrip403.getD j.val default).savedQ80) = (86408239450934727921 : ℤ) := by
  rw [← strip403_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip403_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip404_data_checked :
    (frozenSavedStrip404.map FrozenSavedRow.savedQ80).sum = (86614736786390058099 : ℤ) ∧
      frozenSavedStrip404.length = 512 - firstU (⟨78, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip404_sum :
    (∑ j : Fin (512 - firstU (⟨78, by decide⟩ : Fin 186)),
      (frozenSavedStrip404.getD j.val default).savedQ80) = (86614736786390058099 : ℤ) := by
  rw [← strip404_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip404_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip405_data_checked :
    (frozenSavedStrip405.map FrozenSavedRow.savedQ80).sum = (86799886935136325727 : ℤ) ∧
      frozenSavedStrip405.length = 512 - firstU (⟨79, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip405_sum :
    (∑ j : Fin (512 - firstU (⟨79, by decide⟩ : Fin 186)),
      (frozenSavedStrip405.getD j.val default).savedQ80) = (86799886935136325727 : ℤ) := by
  rw [← strip405_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip405_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip406_data_checked :
    (frozenSavedStrip406.map FrozenSavedRow.savedQ80).sum = (86963106676582954897 : ℤ) ∧
      frozenSavedStrip406.length = 512 - firstU (⟨80, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip406_sum :
    (∑ j : Fin (512 - firstU (⟨80, by decide⟩ : Fin 186)),
      (frozenSavedStrip406.getD j.val default).savedQ80) = (86963106676582954897 : ℤ) := by
  rw [← strip406_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip406_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip407_data_checked :
    (frozenSavedStrip407.map FrozenSavedRow.savedQ80).sum = (87094487367845978527 : ℤ) ∧
      frozenSavedStrip407.length = 512 - firstU (⟨81, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip407_sum :
    (∑ j : Fin (512 - firstU (⟨81, by decide⟩ : Fin 186)),
      (frozenSavedStrip407.getD j.val default).savedQ80) = (87094487367845978527 : ℤ) := by
  rw [← strip407_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip407_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip408_data_checked :
    (frozenSavedStrip408.map FrozenSavedRow.savedQ80).sum = (87203673733768362643 : ℤ) ∧
      frozenSavedStrip408.length = 512 - firstU (⟨82, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip408_sum :
    (∑ j : Fin (512 - firstU (⟨82, by decide⟩ : Fin 186)),
      (frozenSavedStrip408.getD j.val default).savedQ80) = (87203673733768362643 : ℤ) := by
  rw [← strip408_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip408_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip409_data_checked :
    (frozenSavedStrip409.map FrozenSavedRow.savedQ80).sum = (87280735709297080998 : ℤ) ∧
      frozenSavedStrip409.length = 512 - firstU (⟨83, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip409_sum :
    (∑ j : Fin (512 - firstU (⟨83, by decide⟩ : Fin 186)),
      (frozenSavedStrip409.getD j.val default).savedQ80) = (87280735709297080998 : ℤ) := by
  rw [← strip409_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip409_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip410_data_checked :
    (frozenSavedStrip410.map FrozenSavedRow.savedQ80).sum = (87335336112464155650 : ℤ) ∧
      frozenSavedStrip410.length = 512 - firstU (⟨84, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip410_sum :
    (∑ j : Fin (512 - firstU (⟨84, by decide⟩ : Fin 186)),
      (frozenSavedStrip410.getD j.val default).savedQ80) = (87335336112464155650 : ℤ) := by
  rw [← strip410_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip410_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip411_data_checked :
    (frozenSavedStrip411.map FrozenSavedRow.savedQ80).sum = (87357523317076893350 : ℤ) ∧
      frozenSavedStrip411.length = 512 - firstU (⟨85, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip411_sum :
    (∑ j : Fin (512 - firstU (⟨85, by decide⟩ : Fin 186)),
      (frozenSavedStrip411.getD j.val default).savedQ80) = (87357523317076893350 : ℤ) := by
  rw [← strip411_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip411_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip412_data_checked :
    (frozenSavedStrip412.map FrozenSavedRow.savedQ80).sum = (87352302922039050555 : ℤ) ∧
      frozenSavedStrip412.length = 512 - firstU (⟨86, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip412_sum :
    (∑ j : Fin (512 - firstU (⟨86, by decide⟩ : Fin 186)),
      (frozenSavedStrip412.getD j.val default).savedQ80) = (87352302922039050555 : ℤ) := by
  rw [← strip412_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip412_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip413_data_checked :
    (frozenSavedStrip413.map FrozenSavedRow.savedQ80).sum = (87324225932716724075 : ℤ) ∧
      frozenSavedStrip413.length = 512 - firstU (⟨87, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip413_sum :
    (∑ j : Fin (512 - firstU (⟨87, by decide⟩ : Fin 186)),
      (frozenSavedStrip413.getD j.val default).savedQ80) = (87324225932716724075 : ℤ) := by
  rw [← strip413_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip413_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip414_data_checked :
    (frozenSavedStrip414.map FrozenSavedRow.savedQ80).sum = (87273290574748870723 : ℤ) ∧
      frozenSavedStrip414.length = 512 - firstU (⟨88, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip414_sum :
    (∑ j : Fin (512 - firstU (⟨88, by decide⟩ : Fin 186)),
      (frozenSavedStrip414.getD j.val default).savedQ80) = (87273290574748870723 : ℤ) := by
  rw [← strip414_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip414_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip415_data_checked :
    (frozenSavedStrip415.map FrozenSavedRow.savedQ80).sum = (87189792320441915685 : ℤ) ∧
      frozenSavedStrip415.length = 512 - firstU (⟨89, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip415_sum :
    (∑ j : Fin (512 - firstU (⟨89, by decide⟩ : Fin 186)),
      (frozenSavedStrip415.getD j.val default).savedQ80) = (87189792320441915685 : ℤ) := by
  rw [← strip415_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip415_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip416_data_checked :
    (frozenSavedStrip416.map FrozenSavedRow.savedQ80).sum = (87077752669674695507 : ℤ) ∧
      frozenSavedStrip416.length = 512 - firstU (⟨90, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip416_sum :
    (∑ j : Fin (512 - firstU (⟨90, by decide⟩ : Fin 186)),
      (frozenSavedStrip416.getD j.val default).savedQ80) = (87077752669674695507 : ℤ) := by
  rw [← strip416_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip416_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip417_data_checked :
    (frozenSavedStrip417.map FrozenSavedRow.savedQ80).sum = (86942526320012469073 : ℤ) ∧
      frozenSavedStrip417.length = 512 - firstU (⟨91, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip417_sum :
    (∑ j : Fin (512 - firstU (⟨91, by decide⟩ : Fin 186)),
      (frozenSavedStrip417.getD j.val default).savedQ80) = (86942526320012469073 : ℤ) := by
  rw [← strip417_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip417_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip418_data_checked :
    (frozenSavedStrip418.map FrozenSavedRow.savedQ80).sum = (86773629558689131546 : ℤ) ∧
      frozenSavedStrip418.length = 512 - firstU (⟨92, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip418_sum :
    (∑ j : Fin (512 - firstU (⟨92, by decide⟩ : Fin 186)),
      (frozenSavedStrip418.getD j.val default).savedQ80) = (86773629558689131546 : ℤ) := by
  rw [← strip418_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip418_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip419_data_checked :
    (frozenSavedStrip419.map FrozenSavedRow.savedQ80).sum = (86576333578048587719 : ℤ) ∧
      frozenSavedStrip419.length = 512 - firstU (⟨93, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip419_sum :
    (∑ j : Fin (512 - firstU (⟨93, by decide⟩ : Fin 186)),
      (frozenSavedStrip419.getD j.val default).savedQ80) = (86576333578048587719 : ℤ) := by
  rw [← strip419_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip419_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip420_data_checked :
    (frozenSavedStrip420.map FrozenSavedRow.savedQ80).sum = (86073549771707232374 : ℤ) ∧
      frozenSavedStrip420.length = 512 - firstU (⟨94, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip420_sum :
    (∑ j : Fin (512 - firstU (⟨94, by decide⟩ : Fin 186)),
      (frozenSavedStrip420.getD j.val default).savedQ80) = (86073549771707232374 : ℤ) := by
  rw [← strip420_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip420_data_checked.1

/-- Exact savedQ80 projection and exact full-mask length of the unchanged literal strip. -/
theorem strip421_data_checked :
    (frozenSavedStrip421.map FrozenSavedRow.savedQ80).sum = (85275678961314589222 : ℤ) ∧
      frozenSavedStrip421.length = 512 - firstU (⟨95, by decide⟩ : Fin 186) := by
  decide +kernel

/-- The exact dependent finite sum, including the original getD default. -/
theorem strip421_sum :
    (∑ j : Fin (512 - firstU (⟨95, by decide⟩ : Fin 186)),
      (frozenSavedStrip421.getD j.val default).savedQ80) = (85275678961314589222 : ℤ) := by
  rw [← strip421_data_checked.2]
  rw [sum_getD_eq_map]
  exact strip421_data_checked.1

end ImbalancedChen.P2HistoricalSavedFloorStoredTotal
