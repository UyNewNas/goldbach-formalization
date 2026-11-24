import ImbalancedChen.P2Winner9CompleteSeedBlock42
import ImbalancedChen.P2Winner9CompletePullingFlags

namespace ImbalancedChen.P2Winner9CompletePullingCheck42
open P2Winner9CompletePullingFlags (witnesses checkedRow orderStep)
open P2Winner9PullingOrderChecks (Consecutive)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem orderPage00 : Consecutive orderStep 10752 16 := by
  decide +kernel

private theorem orderPage01 : Consecutive orderStep 10768 16 := by
  decide +kernel

private theorem orderPage02 : Consecutive orderStep 10784 16 := by
  decide +kernel

private theorem orderPage03 : Consecutive orderStep 10800 16 := by
  decide +kernel

private theorem orderPage04 : Consecutive orderStep 10816 16 := by
  decide +kernel

private theorem orderPage05 : Consecutive orderStep 10832 16 := by
  decide +kernel

private theorem orderPage06 : Consecutive orderStep 10848 16 := by
  decide +kernel

private theorem orderPage07 : Consecutive orderStep 10864 16 := by
  decide +kernel

private theorem orderPage08 : Consecutive orderStep 10880 16 := by
  decide +kernel

private theorem orderPage09 : Consecutive orderStep 10896 16 := by
  decide +kernel

private theorem orderPage10 : Consecutive orderStep 10912 16 := by
  decide +kernel

private theorem orderPage11 : Consecutive orderStep 10928 16 := by
  decide +kernel

private theorem orderPage12 : Consecutive orderStep 10944 16 := by
  decide +kernel

private theorem orderPage13 : Consecutive orderStep 10960 16 := by
  decide +kernel

private theorem orderPage14 : Consecutive orderStep 10976 16 := by
  decide +kernel

private theorem orderPage15 : Consecutive orderStep 10992 16 := by
  decide +kernel

theorem order_checked : Consecutive orderStep 10752 256 := by
  exact
    orderPage00.append <|
    orderPage01.append <|
    orderPage02.append <|
    orderPage03.append <|
    orderPage04.append <|
    orderPage05.append <|
    orderPage06.append <|
    orderPage07.append <|
    orderPage08.append <|
    orderPage09.append <|
    orderPage10.append <|
    orderPage11.append <|
    orderPage12.append <|
    orderPage13.append <|
    orderPage14.append <|
    orderPage15

private theorem page00 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10752 16 (P2Winner9CompleteSeedBlock42.pages[0]!) := by
  decide +kernel

private theorem page01 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10768 16 (P2Winner9CompleteSeedBlock42.pages[1]!) := by
  decide +kernel

private theorem page02 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10784 16 (P2Winner9CompleteSeedBlock42.pages[2]!) := by
  decide +kernel

private theorem page03 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10800 16 (P2Winner9CompleteSeedBlock42.pages[3]!) := by
  decide +kernel

private theorem page04 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10816 16 (P2Winner9CompleteSeedBlock42.pages[4]!) := by
  decide +kernel

private theorem page05 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10832 16 (P2Winner9CompleteSeedBlock42.pages[5]!) := by
  decide +kernel

private theorem page06 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10848 16 (P2Winner9CompleteSeedBlock42.pages[6]!) := by
  decide +kernel

private theorem page07 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10864 16 (P2Winner9CompleteSeedBlock42.pages[7]!) := by
  decide +kernel

private theorem page08 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10880 16 (P2Winner9CompleteSeedBlock42.pages[8]!) := by
  decide +kernel

private theorem page09 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10896 16 (P2Winner9CompleteSeedBlock42.pages[9]!) := by
  decide +kernel

private theorem page10 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10912 16 (P2Winner9CompleteSeedBlock42.pages[10]!) := by
  decide +kernel

private theorem page11 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10928 16 (P2Winner9CompleteSeedBlock42.pages[11]!) := by
  decide +kernel

private theorem page12 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10944 16 (P2Winner9CompleteSeedBlock42.pages[12]!) := by
  decide +kernel

private theorem page13 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10960 16 (P2Winner9CompleteSeedBlock42.pages[13]!) := by
  decide +kernel

private theorem page14 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10976 16 (P2Winner9CompleteSeedBlock42.pages[14]!) := by
  decide +kernel

private theorem page15 :
    Checked (fun ordinal row => checkedRow ordinal row = true) 10992 16 (P2Winner9CompleteSeedBlock42.pages[15]!) := by
  decide +kernel

theorem checked : Checked (fun ordinal row => checkedRow ordinal row = true) 10752 256 P2Winner9CompleteSeedBlock42.rows := by
  change Checked (fun ordinal row => checkedRow ordinal row = true) 10752 256 ([
    P2Winner9CompleteSeedBlock42.pages[0]!,
    P2Winner9CompleteSeedBlock42.pages[1]!,
    P2Winner9CompleteSeedBlock42.pages[2]!,
    P2Winner9CompleteSeedBlock42.pages[3]!,
    P2Winner9CompleteSeedBlock42.pages[4]!,
    P2Winner9CompleteSeedBlock42.pages[5]!,
    P2Winner9CompleteSeedBlock42.pages[6]!,
    P2Winner9CompleteSeedBlock42.pages[7]!,
    P2Winner9CompleteSeedBlock42.pages[8]!,
    P2Winner9CompleteSeedBlock42.pages[9]!,
    P2Winner9CompleteSeedBlock42.pages[10]!,
    P2Winner9CompleteSeedBlock42.pages[11]!,
    P2Winner9CompleteSeedBlock42.pages[12]!,
    P2Winner9CompleteSeedBlock42.pages[13]!,
    P2Winner9CompleteSeedBlock42.pages[14]!,
    P2Winner9CompleteSeedBlock42.pages[15]!
  ].toArray.flatten)
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

end ImbalancedChen.P2Winner9CompletePullingCheck42
