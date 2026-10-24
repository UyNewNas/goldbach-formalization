-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*16 + 64*p; the full block ends at 102400.
-- Block11Data.lean is an expected source dependency; its reviewed contract is def block11 : NodeTree 12.
-- Block12Data.lean is an expected source dependency; its reviewed contract is def block12 : NodeTree 12.
-- Block15Data.lean is an expected source dependency; its reviewed contract is def block15 : NodeTree 12.
-- Block16Data.lean is an expected source dependency; its reviewed contract is def block16 : NodeTree 12.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block11Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block12Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block15Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block16Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer


namespace ImbalancedChen.OriginalU2StoredNodeBlock16FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block16_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*0) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 0 (by omega) (by decide +kernel))
theorem block16_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*1) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 1 (by omega) (by decide +kernel))
theorem block16_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*2) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 2 (by omega) (by decide +kernel))
theorem block16_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*3) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 3 (by omega) (by decide +kernel))
theorem block16_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*4) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 4 (by omega) (by decide +kernel))
theorem block16_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*5) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 5 (by omega) (by decide +kernel))
theorem block16_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*6) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 6 (by omega) (by decide +kernel))
theorem block16_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*7) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 7 (by omega) (by decide +kernel))
theorem block16_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*8) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 8 (by omega) (by decide +kernel))
theorem block16_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*9) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 9 (by omega) (by decide +kernel))
theorem block16_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*10) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 10 (by omega) (by decide +kernel))
theorem block16_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*11) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 11 (by omega) (by decide +kernel))
theorem block16_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*12) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 12 (by omega) (by decide +kernel))
theorem block16_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*13) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 13 (by omega) (by decide +kernel))
theorem block16_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*14) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 14 (by omega) (by decide +kernel))
theorem block16_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*15) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 15 (by omega) (by decide +kernel))
theorem block16_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*16) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 16 (by omega) (by decide +kernel))
theorem block16_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*17) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 17 (by omega) (by decide +kernel))
theorem block16_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*18) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 18 (by omega) (by decide +kernel))
theorem block16_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*19) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 19 (by omega) (by decide +kernel))
theorem block16_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*20) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 20 (by omega) (by decide +kernel))
theorem block16_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*21) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 21 (by omega) (by decide +kernel))
theorem block16_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*22) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 22 (by omega) (by decide +kernel))
theorem block16_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*23) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 23 (by omega) (by decide +kernel))
theorem block16_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*24) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 24 (by omega) (by decide +kernel))
theorem block16_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*25) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 25 (by omega) (by decide +kernel))
theorem block16_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*26) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 26 (by omega) (by decide +kernel))
theorem block16_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*27) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 27 (by omega) (by decide +kernel))
theorem block16_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*28) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 28 (by omega) (by decide +kernel))
theorem block16_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*29) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 29 (by omega) (by decide +kernel))
theorem block16_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*30) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 30 (by omega) (by decide +kernel))
theorem block16_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*31) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 31 (by omega) (by decide +kernel))
theorem block16_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*32) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 32 (by omega) (by decide +kernel))
theorem block16_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*33) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 33 (by omega) (by decide +kernel))
theorem block16_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*34) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 34 (by omega) (by decide +kernel))
theorem block16_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*35) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 35 (by omega) (by decide +kernel))
theorem block16_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*36) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 36 (by omega) (by decide +kernel))
theorem block16_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*37) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 37 (by omega) (by decide +kernel))
theorem block16_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*38) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 38 (by omega) (by decide +kernel))
theorem block16_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*39) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 39 (by omega) (by decide +kernel))
theorem block16_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*40) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 40 (by omega) (by decide +kernel))
theorem block16_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*41) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 41 (by omega) (by decide +kernel))
theorem block16_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*42) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 42 (by omega) (by decide +kernel))
theorem block16_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*43) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 43 (by omega) (by decide +kernel))
theorem block16_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*44) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 44 (by omega) (by decide +kernel))
theorem block16_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*45) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 45 (by omega) (by decide +kernel))
theorem block16_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*46) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 46 (by omega) (by decide +kernel))
theorem block16_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*47) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 47 (by omega) (by decide +kernel))
theorem block16_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*48) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 48 (by omega) (by decide +kernel))
theorem block16_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*49) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 49 (by omega) (by decide +kernel))
theorem block16_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*50) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 50 (by omega) (by decide +kernel))
theorem block16_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*51) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 51 (by omega) (by decide +kernel))
theorem block16_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*52) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 52 (by omega) (by decide +kernel))
theorem block16_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*53) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 53 (by omega) (by decide +kernel))
theorem block16_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*54) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 54 (by omega) (by decide +kernel))
theorem block16_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*55) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 55 (by omega) (by decide +kernel))
theorem block16_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*56) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 56 (by omega) (by decide +kernel))
theorem block16_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*57) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 57 (by omega) (by decide +kernel))
theorem block16_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*58) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 58 (by omega) (by decide +kernel))
theorem block16_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*59) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 59 (by omega) (by decide +kernel))
theorem block16_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*60) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 60 (by omega) (by decide +kernel))
theorem block16_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*61) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 61 (by omega) (by decide +kernel))
theorem block16_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*62) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 62 (by omega) (by decide +kernel))
theorem block16_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*63) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 16 (by omega) (by omega)
      block11 block12 block15 block16 tail 63 (by omega) (by decide +kernel))
theorem readCheckBlock_of_64_page_count
    (read : Nat → ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly.OriginalNode) (lo pages : Nat)
    (hpages : ∀ p : Nat, p < pages →
      readCheckBlock read (lo + 64*p) 64 = true) :
    readCheckBlock read lo (64*pages) = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 64*pages := List.mem_range.mp hk
  let p := k/64
  let r := k%64
  have hp : p < pages := by dsimp [p]; omega
  have hr : r < 64 := by dsimp [r]; omega
  have he : 64*p+r=k := by dsimp [p,r]; omega
  have hs : readCheckStep read (lo + 64*p + r) = true :=
    readCheckBlock_step (hpages p hp) hr
  have hindex : lo + 64*p + r = lo+k := by omega
  simpa only [hindex] using hs
theorem block16_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) 98305 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) (98305 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block16_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 16 block11 block12 block15 block16 tail)) 98305 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock16FullSourceOnly
