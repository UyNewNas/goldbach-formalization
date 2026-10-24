-- SOURCEONLY candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, replay, and any admission.
-- Pages cover indices 192513..196608. Physical delayed-read window: slots 34,35,38,39.
-- Raw four-column bytes and source dependencies are recorded in Block39CP.json.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block34Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block35Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block38Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block39Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

-- Serialize the independent kernel checks to stay within the compiler memory budget.
set_option Elab.async false

namespace ImbalancedChen.OriginalU2StoredNodeBlock39FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block39_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 0 (by omega) (by decide +kernel))

theorem block39_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 1 (by omega) (by decide +kernel))

theorem block39_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 2 (by omega) (by decide +kernel))

theorem block39_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 3 (by omega) (by decide +kernel))

theorem block39_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 4 (by omega) (by decide +kernel))

theorem block39_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 5 (by omega) (by decide +kernel))

theorem block39_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 6 (by omega) (by decide +kernel))

theorem block39_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 7 (by omega) (by decide +kernel))

theorem block39_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 8 (by omega) (by decide +kernel))

theorem block39_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 9 (by omega) (by decide +kernel))

theorem block39_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 10 (by omega) (by decide +kernel))

theorem block39_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 11 (by omega) (by decide +kernel))

theorem block39_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 12 (by omega) (by decide +kernel))

theorem block39_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 13 (by omega) (by decide +kernel))

theorem block39_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 14 (by omega) (by decide +kernel))

theorem block39_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 15 (by omega) (by decide +kernel))

theorem block39_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 16 (by omega) (by decide +kernel))

theorem block39_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 17 (by omega) (by decide +kernel))

theorem block39_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 18 (by omega) (by decide +kernel))

theorem block39_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 19 (by omega) (by decide +kernel))

theorem block39_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 20 (by omega) (by decide +kernel))

theorem block39_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 21 (by omega) (by decide +kernel))

theorem block39_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 22 (by omega) (by decide +kernel))

theorem block39_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 193985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 23 (by omega) (by decide +kernel))

theorem block39_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 24 (by omega) (by decide +kernel))

theorem block39_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 25 (by omega) (by decide +kernel))

theorem block39_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 26 (by omega) (by decide +kernel))

theorem block39_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 27 (by omega) (by decide +kernel))

theorem block39_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 28 (by omega) (by decide +kernel))

theorem block39_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 29 (by omega) (by decide +kernel))

theorem block39_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 30 (by omega) (by decide +kernel))

theorem block39_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 31 (by omega) (by decide +kernel))

theorem block39_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 32 (by omega) (by decide +kernel))

theorem block39_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 33 (by omega) (by decide +kernel))

theorem block39_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 34 (by omega) (by decide +kernel))

theorem block39_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 35 (by omega) (by decide +kernel))

theorem block39_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 36 (by omega) (by decide +kernel))

theorem block39_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 37 (by omega) (by decide +kernel))

theorem block39_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 194945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 38 (by omega) (by decide +kernel))

theorem block39_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 39 (by omega) (by decide +kernel))

theorem block39_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 40 (by omega) (by decide +kernel))

theorem block39_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 41 (by omega) (by decide +kernel))

theorem block39_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 42 (by omega) (by decide +kernel))

theorem block39_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 43 (by omega) (by decide +kernel))

theorem block39_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 44 (by omega) (by decide +kernel))

theorem block39_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 45 (by omega) (by decide +kernel))

theorem block39_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 46 (by omega) (by decide +kernel))

theorem block39_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 47 (by omega) (by decide +kernel))

theorem block39_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 48 (by omega) (by decide +kernel))

theorem block39_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 49 (by omega) (by decide +kernel))

theorem block39_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 50 (by omega) (by decide +kernel))

theorem block39_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 51 (by omega) (by decide +kernel))

theorem block39_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 52 (by omega) (by decide +kernel))

theorem block39_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 53 (by omega) (by decide +kernel))

theorem block39_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 195969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 54 (by omega) (by decide +kernel))

theorem block39_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 55 (by omega) (by decide +kernel))

theorem block39_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 56 (by omega) (by decide +kernel))

theorem block39_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 57 (by omega) (by decide +kernel))

theorem block39_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 58 (by omega) (by decide +kernel))

theorem block39_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 59 (by omega) (by decide +kernel))

theorem block39_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 60 (by omega) (by decide +kernel))

theorem block39_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 61 (by omega) (by decide +kernel))

theorem block39_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 62 (by omega) (by decide +kernel))

theorem block39_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 196545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 39 (by omega) (by omega)
      block34 block35 block38 block39 tail 63 (by omega) (by decide +kernel))

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

theorem block39_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192513 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) (192513 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block39_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 39 block34 block35 block38 block39 tail)) 192513 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock39FullSourceOnly
