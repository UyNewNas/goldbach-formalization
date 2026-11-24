import ImbalancedChen.P2Winner9CompleteSeedBlock21
import ImbalancedChen.P2Winner9SeedArchiveChecks

namespace ImbalancedChen.P2Winner9SeedArchiveCheck21
open P2Winner9SeedArchiveChecks

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem page00 :
    Checked ArchiveRowCheck 5376 16 (P2Winner9CompleteSeedBlock21.pages[0]!) := by
  decide +kernel

private theorem page01 :
    Checked ArchiveRowCheck 5392 16 (P2Winner9CompleteSeedBlock21.pages[1]!) := by
  decide +kernel

private theorem page02 :
    Checked ArchiveRowCheck 5408 16 (P2Winner9CompleteSeedBlock21.pages[2]!) := by
  decide +kernel

private theorem page03 :
    Checked ArchiveRowCheck 5424 16 (P2Winner9CompleteSeedBlock21.pages[3]!) := by
  decide +kernel

private theorem page04 :
    Checked ArchiveRowCheck 5440 16 (P2Winner9CompleteSeedBlock21.pages[4]!) := by
  decide +kernel

private theorem page05 :
    Checked ArchiveRowCheck 5456 16 (P2Winner9CompleteSeedBlock21.pages[5]!) := by
  decide +kernel

private theorem page06 :
    Checked ArchiveRowCheck 5472 16 (P2Winner9CompleteSeedBlock21.pages[6]!) := by
  decide +kernel

private theorem page07 :
    Checked ArchiveRowCheck 5488 16 (P2Winner9CompleteSeedBlock21.pages[7]!) := by
  decide +kernel

private theorem page08 :
    Checked ArchiveRowCheck 5504 16 (P2Winner9CompleteSeedBlock21.pages[8]!) := by
  decide +kernel

private theorem page09 :
    Checked ArchiveRowCheck 5520 16 (P2Winner9CompleteSeedBlock21.pages[9]!) := by
  decide +kernel

private theorem page10 :
    Checked ArchiveRowCheck 5536 16 (P2Winner9CompleteSeedBlock21.pages[10]!) := by
  decide +kernel

private theorem page11 :
    Checked ArchiveRowCheck 5552 16 (P2Winner9CompleteSeedBlock21.pages[11]!) := by
  decide +kernel

private theorem page12 :
    Checked ArchiveRowCheck 5568 16 (P2Winner9CompleteSeedBlock21.pages[12]!) := by
  decide +kernel

private theorem page13 :
    Checked ArchiveRowCheck 5584 16 (P2Winner9CompleteSeedBlock21.pages[13]!) := by
  decide +kernel

private theorem page14 :
    Checked ArchiveRowCheck 5600 16 (P2Winner9CompleteSeedBlock21.pages[14]!) := by
  decide +kernel

private theorem page15 :
    Checked ArchiveRowCheck 5616 16 (P2Winner9CompleteSeedBlock21.pages[15]!) := by
  decide +kernel

theorem checked : Checked ArchiveRowCheck 5376 256 P2Winner9CompleteSeedBlock21.rows := by
  change Checked ArchiveRowCheck 5376 256 ([
    P2Winner9CompleteSeedBlock21.pages[0]!,
    P2Winner9CompleteSeedBlock21.pages[1]!,
    P2Winner9CompleteSeedBlock21.pages[2]!,
    P2Winner9CompleteSeedBlock21.pages[3]!,
    P2Winner9CompleteSeedBlock21.pages[4]!,
    P2Winner9CompleteSeedBlock21.pages[5]!,
    P2Winner9CompleteSeedBlock21.pages[6]!,
    P2Winner9CompleteSeedBlock21.pages[7]!,
    P2Winner9CompleteSeedBlock21.pages[8]!,
    P2Winner9CompleteSeedBlock21.pages[9]!,
    P2Winner9CompleteSeedBlock21.pages[10]!,
    P2Winner9CompleteSeedBlock21.pages[11]!,
    P2Winner9CompleteSeedBlock21.pages[12]!,
    P2Winner9CompleteSeedBlock21.pages[13]!,
    P2Winner9CompleteSeedBlock21.pages[14]!,
    P2Winner9CompleteSeedBlock21.pages[15]!]).toArray.flatten
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

end ImbalancedChen.P2Winner9SeedArchiveCheck21
