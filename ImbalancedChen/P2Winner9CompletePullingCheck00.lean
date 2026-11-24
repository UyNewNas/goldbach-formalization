import ImbalancedChen.P2Winner9CompleteSeedBlock00
import ImbalancedChen.P2Winner9CompletePullingFlags

namespace ImbalancedChen.P2Winner9CompletePullingCheck00
open P2Winner9CompletePullingFlags (witnesses checkedRow orderStep)
open P2Winner9PullingOrderChecks (Consecutive)
open P2Winner9SeedArchiveChecks (Checked)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem orderPage00 : Consecutive orderStep 0 16 := by
  decide +kernel

private theorem orderPage01 : Consecutive orderStep 16 16 := by
  decide +kernel

private theorem orderPage02 : Consecutive orderStep 32 16 := by
  decide +kernel

private theorem orderPage03 : Consecutive orderStep 48 16 := by
  decide +kernel

private theorem orderPage04 : Consecutive orderStep 64 16 := by
  decide +kernel

private theorem orderPage05 : Consecutive orderStep 80 16 := by
  decide +kernel

private theorem orderPage06 : Consecutive orderStep 96 16 := by
  decide +kernel

private theorem orderPage07 : Consecutive orderStep 112 16 := by
  decide +kernel

private theorem orderPage08 : Consecutive orderStep 128 16 := by
  decide +kernel

private theorem orderPage09 : Consecutive orderStep 144 16 := by
  decide +kernel

private theorem orderPage10 : Consecutive orderStep 160 16 := by
  decide +kernel

private theorem orderPage11 : Consecutive orderStep 176 16 := by
  decide +kernel

private theorem orderPage12 : Consecutive orderStep 192 16 := by
  decide +kernel

private theorem orderPage13 : Consecutive orderStep 208 16 := by
  decide +kernel

private theorem orderPage14 : Consecutive orderStep 224 16 := by
  decide +kernel

private theorem orderPage15 : Consecutive orderStep 240 16 := by
  decide +kernel

theorem order_checked : Consecutive orderStep 0 256 := by
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

private theorem prefixPage00 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 0 16 := by
  decide +kernel

private theorem prefixPage01 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 16 16 := by
  decide +kernel

private theorem prefixPage02 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 32 16 := by
  decide +kernel

private theorem prefixPage03 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 48 16 := by
  decide +kernel

private theorem prefixPage04 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 64 16 := by
  decide +kernel

private theorem prefixPage05 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 80 16 := by
  decide +kernel

private theorem prefixPage06 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 96 16 := by
  decide +kernel

private theorem prefixPage07 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 112 16 := by
  decide +kernel

private theorem prefixPage08 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 128 16 := by
  decide +kernel

private theorem prefixPage09 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 144 16 := by
  decide +kernel

private theorem prefixPage10 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 160 16 := by
  decide +kernel

private theorem prefixPage11 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 176 16 := by
  decide +kernel

private theorem prefixPage12 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 192 16 := by
  decide +kernel

private theorem prefixPage13 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 208 16 := by
  decide +kernel

private theorem prefixPage14 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 224 16 := by
  decide +kernel

private theorem prefixPage15 : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 240 16 := by
  decide +kernel

private theorem prefix_bindings : Consecutive
    (fun ordinal => witnesses.prefixCompatible ordinal = true) 0 256 := by
  exact
    prefixPage00.append <|
    prefixPage01.append <|
    prefixPage02.append <|
    prefixPage03.append <|
    prefixPage04.append <|
    prefixPage05.append <|
    prefixPage06.append <|
    prefixPage07.append <|
    prefixPage08.append <|
    prefixPage09.append <|
    prefixPage10.append <|
    prefixPage11.append <|
    prefixPage12.append <|
    prefixPage13.append <|
    prefixPage14.append <|
    prefixPage15

theorem checked : Checked (fun ordinal row => checkedRow ordinal row = true) 0 256 P2Winner9CompleteSeedBlock00.rows := by
  apply witnesses.prefix_checked
  intro i
  simpa only [Nat.zero_add] using prefix_bindings i

end ImbalancedChen.P2Winner9CompletePullingCheck00
