-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*22 + 64*p; the full block ends at 126976.
-- block-22.Llo.dec SHA256 44ef65cb88f33de788cd54414238d698ec56de131fddd4d4bd4c69e102dd6e59 (147456 bytes; 4096 canonical lines)
-- block-22.Lhi.dec SHA256 1a5cb3694d5cfab8273db0ae5cfc6bc98d57686d77a15857fc38c030d7e53f60 (147456 bytes; 4096 canonical lines)
-- block-22.Hlo.dec SHA256 19fe6b7e0c123926e4c00d89bc037421bc40b7e29773f7a57f46f26b738242f5 (147456 bytes; 4096 canonical lines)
-- block-22.Hhi.dec SHA256 8168acc61f1cca7dba0d037067b6364672602a265b77eb7e6cb3969581e43540 (147456 bytes; 4096 canonical lines)
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block17Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block18Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block21Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block22Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock22FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

theorem block22_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 122881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 0 (by omega) (by decide +kernel))

theorem block22_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 122945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 1 (by omega) (by decide +kernel))

theorem block22_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 2 (by omega) (by decide +kernel))

theorem block22_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 3 (by omega) (by decide +kernel))

theorem block22_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 4 (by omega) (by decide +kernel))

theorem block22_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 5 (by omega) (by decide +kernel))

theorem block22_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 6 (by omega) (by decide +kernel))

theorem block22_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 7 (by omega) (by decide +kernel))

theorem block22_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 8 (by omega) (by decide +kernel))

theorem block22_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 9 (by omega) (by decide +kernel))

theorem block22_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 10 (by omega) (by decide +kernel))

theorem block22_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 11 (by omega) (by decide +kernel))

theorem block22_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 12 (by omega) (by decide +kernel))

theorem block22_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 13 (by omega) (by decide +kernel))

theorem block22_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 14 (by omega) (by decide +kernel))

theorem block22_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 15 (by omega) (by decide +kernel))

theorem block22_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 16 (by omega) (by decide +kernel))

theorem block22_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 123969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 17 (by omega) (by decide +kernel))

theorem block22_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 18 (by omega) (by decide +kernel))

theorem block22_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 19 (by omega) (by decide +kernel))

theorem block22_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 20 (by omega) (by decide +kernel))

theorem block22_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 21 (by omega) (by decide +kernel))

theorem block22_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 22 (by omega) (by decide +kernel))

theorem block22_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 23 (by omega) (by decide +kernel))

theorem block22_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 24 (by omega) (by decide +kernel))

theorem block22_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 25 (by omega) (by decide +kernel))

theorem block22_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 26 (by omega) (by decide +kernel))

theorem block22_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 27 (by omega) (by decide +kernel))

theorem block22_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 28 (by omega) (by decide +kernel))

theorem block22_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 29 (by omega) (by decide +kernel))

theorem block22_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 30 (by omega) (by decide +kernel))

theorem block22_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 31 (by omega) (by decide +kernel))

theorem block22_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 32 (by omega) (by decide +kernel))

theorem block22_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 124993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 33 (by omega) (by decide +kernel))

theorem block22_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 34 (by omega) (by decide +kernel))

theorem block22_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 35 (by omega) (by decide +kernel))

theorem block22_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 36 (by omega) (by decide +kernel))

theorem block22_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 37 (by omega) (by decide +kernel))

theorem block22_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 38 (by omega) (by decide +kernel))

theorem block22_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 39 (by omega) (by decide +kernel))

theorem block22_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 40 (by omega) (by decide +kernel))

theorem block22_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 41 (by omega) (by decide +kernel))

theorem block22_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 42 (by omega) (by decide +kernel))

theorem block22_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 43 (by omega) (by decide +kernel))

theorem block22_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 44 (by omega) (by decide +kernel))

theorem block22_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 45 (by omega) (by decide +kernel))

theorem block22_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 46 (by omega) (by decide +kernel))

theorem block22_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 47 (by omega) (by decide +kernel))

theorem block22_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 125953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 48 (by omega) (by decide +kernel))

theorem block22_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 49 (by omega) (by decide +kernel))

theorem block22_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 50 (by omega) (by decide +kernel))

theorem block22_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 51 (by omega) (by decide +kernel))

theorem block22_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 52 (by omega) (by decide +kernel))

theorem block22_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 53 (by omega) (by decide +kernel))

theorem block22_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 54 (by omega) (by decide +kernel))

theorem block22_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 55 (by omega) (by decide +kernel))

theorem block22_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 56 (by omega) (by decide +kernel))

theorem block22_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 57 (by omega) (by decide +kernel))

theorem block22_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 58 (by omega) (by decide +kernel))

theorem block22_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 59 (by omega) (by decide +kernel))

theorem block22_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 60 (by omega) (by decide +kernel))

theorem block22_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 61 (by omega) (by decide +kernel))

theorem block22_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 62 (by omega) (by decide +kernel))

theorem block22_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 126913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 22 (by omega) (by omega) block17 block18 block21 block22 tail 63 (by omega) (by decide +kernel))

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

theorem block22_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 122881 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) (122881 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block22_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 22 block17 block18 block21 block22 tail)) 122881 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock22FullSourceOnly
