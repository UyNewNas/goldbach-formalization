import ImbalancedChen.P2Winner9CompleteSeedBlock03
import ImbalancedChen.P2Winner9SeedArchiveChecks

namespace ImbalancedChen.P2Winner9SeedArchiveCheck03
open P2Winner9SeedArchiveChecks

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem page00 :
    Checked ArchiveRowCheck 768 16 (P2Winner9CompleteSeedBlock03.pages[0]!) := by
  decide +kernel

private theorem page01 :
    Checked ArchiveRowCheck 784 16 (P2Winner9CompleteSeedBlock03.pages[1]!) := by
  decide +kernel

private theorem page02 :
    Checked ArchiveRowCheck 800 16 (P2Winner9CompleteSeedBlock03.pages[2]!) := by
  decide +kernel

private theorem page03 :
    Checked ArchiveRowCheck 816 16 (P2Winner9CompleteSeedBlock03.pages[3]!) := by
  decide +kernel

private theorem page04 :
    Checked ArchiveRowCheck 832 16 (P2Winner9CompleteSeedBlock03.pages[4]!) := by
  decide +kernel

private theorem page05 :
    Checked ArchiveRowCheck 848 16 (P2Winner9CompleteSeedBlock03.pages[5]!) := by
  decide +kernel

private theorem page06 :
    Checked ArchiveRowCheck 864 16 (P2Winner9CompleteSeedBlock03.pages[6]!) := by
  decide +kernel

private theorem page07 :
    Checked ArchiveRowCheck 880 16 (P2Winner9CompleteSeedBlock03.pages[7]!) := by
  decide +kernel

private theorem page08 :
    Checked ArchiveRowCheck 896 16 (P2Winner9CompleteSeedBlock03.pages[8]!) := by
  decide +kernel

private theorem page09 :
    Checked ArchiveRowCheck 912 16 (P2Winner9CompleteSeedBlock03.pages[9]!) := by
  decide +kernel

private theorem page10 :
    Checked ArchiveRowCheck 928 16 (P2Winner9CompleteSeedBlock03.pages[10]!) := by
  decide +kernel

private theorem page11 :
    Checked ArchiveRowCheck 944 16 (P2Winner9CompleteSeedBlock03.pages[11]!) := by
  decide +kernel

private theorem page12 :
    Checked ArchiveRowCheck 960 16 (P2Winner9CompleteSeedBlock03.pages[12]!) := by
  decide +kernel

private theorem page13 :
    Checked ArchiveRowCheck 976 16 (P2Winner9CompleteSeedBlock03.pages[13]!) := by
  decide +kernel

private theorem page14 :
    Checked ArchiveRowCheck 992 16 (P2Winner9CompleteSeedBlock03.pages[14]!) := by
  decide +kernel

private theorem page15 :
    Checked ArchiveRowCheck 1008 16 (P2Winner9CompleteSeedBlock03.pages[15]!) := by
  decide +kernel

theorem checked : Checked ArchiveRowCheck 768 256 P2Winner9CompleteSeedBlock03.rows := by
  change Checked ArchiveRowCheck 768 256 ([
    P2Winner9CompleteSeedBlock03.pages[0]!,
    P2Winner9CompleteSeedBlock03.pages[1]!,
    P2Winner9CompleteSeedBlock03.pages[2]!,
    P2Winner9CompleteSeedBlock03.pages[3]!,
    P2Winner9CompleteSeedBlock03.pages[4]!,
    P2Winner9CompleteSeedBlock03.pages[5]!,
    P2Winner9CompleteSeedBlock03.pages[6]!,
    P2Winner9CompleteSeedBlock03.pages[7]!,
    P2Winner9CompleteSeedBlock03.pages[8]!,
    P2Winner9CompleteSeedBlock03.pages[9]!,
    P2Winner9CompleteSeedBlock03.pages[10]!,
    P2Winner9CompleteSeedBlock03.pages[11]!,
    P2Winner9CompleteSeedBlock03.pages[12]!,
    P2Winner9CompleteSeedBlock03.pages[13]!,
    P2Winner9CompleteSeedBlock03.pages[14]!,
    P2Winner9CompleteSeedBlock03.pages[15]!]).toArray.flatten
  exact
    page00.flatten_cons <|
    page01.flatten_cons <|
    page02.flatten_cons <|
    page03.flatten_cons <|
    page04.flatten_cons <|
    page05.flatten_cons <|
    page06.flatten_cons <|
    page07.flatten_cons <|
    page08.flatten_cons <|
    page09.flatten_cons <|
    page10.flatten_cons <|
    page11.flatten_cons <|
    page12.flatten_cons <|
    page13.flatten_cons <|
    page14.flatten_cons <|
    page15.flatten_single

end ImbalancedChen.P2Winner9SeedArchiveCheck03
