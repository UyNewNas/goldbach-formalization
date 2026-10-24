-- SOURCEONLY generated complete candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- Page starts are 110593 + 64*p; the full Block19 range ends at 114688.
-- Block19 raw array-file hashes are recorded in the paired CP file.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block14Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block15Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block18Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block19Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock19FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

-- The four physical slots encode boundary b-5, delayed b-4, previous b-1, current b.
-- All lemmas retain one universally quantified arbitrary tail : Nat → Block.
theorem block19_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 0 (by omega) (by decide +kernel))

theorem block19_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 1 (by omega) (by decide +kernel))

theorem block19_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 2 (by omega) (by decide +kernel))

theorem block19_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 3 (by omega) (by decide +kernel))

theorem block19_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 4 (by omega) (by decide +kernel))

theorem block19_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 5 (by omega) (by decide +kernel))

theorem block19_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 6 (by omega) (by decide +kernel))

theorem block19_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 7 (by omega) (by decide +kernel))

theorem block19_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 8 (by omega) (by decide +kernel))

theorem block19_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 9 (by omega) (by decide +kernel))

theorem block19_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 10 (by omega) (by decide +kernel))

theorem block19_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 11 (by omega) (by decide +kernel))

theorem block19_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 12 (by omega) (by decide +kernel))

theorem block19_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 13 (by omega) (by decide +kernel))

theorem block19_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 14 (by omega) (by decide +kernel))

theorem block19_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 15 (by omega) (by decide +kernel))

theorem block19_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 16 (by omega) (by decide +kernel))

theorem block19_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 17 (by omega) (by decide +kernel))

theorem block19_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 18 (by omega) (by decide +kernel))

theorem block19_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 19 (by omega) (by decide +kernel))

theorem block19_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 20 (by omega) (by decide +kernel))

theorem block19_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 111937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 21 (by omega) (by decide +kernel))

theorem block19_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 22 (by omega) (by decide +kernel))

theorem block19_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 23 (by omega) (by decide +kernel))

theorem block19_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 24 (by omega) (by decide +kernel))

theorem block19_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 25 (by omega) (by decide +kernel))

theorem block19_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 26 (by omega) (by decide +kernel))

theorem block19_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 27 (by omega) (by decide +kernel))

theorem block19_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 28 (by omega) (by decide +kernel))

theorem block19_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 29 (by omega) (by decide +kernel))

theorem block19_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 30 (by omega) (by decide +kernel))

theorem block19_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 31 (by omega) (by decide +kernel))

theorem block19_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 32 (by omega) (by decide +kernel))

theorem block19_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 33 (by omega) (by decide +kernel))

theorem block19_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 34 (by omega) (by decide +kernel))

theorem block19_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 35 (by omega) (by decide +kernel))

theorem block19_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 36 (by omega) (by decide +kernel))

theorem block19_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 112961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 37 (by omega) (by decide +kernel))

theorem block19_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 38 (by omega) (by decide +kernel))

theorem block19_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 39 (by omega) (by decide +kernel))

theorem block19_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 40 (by omega) (by decide +kernel))

theorem block19_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 41 (by omega) (by decide +kernel))

theorem block19_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 42 (by omega) (by decide +kernel))

theorem block19_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 43 (by omega) (by decide +kernel))

theorem block19_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 44 (by omega) (by decide +kernel))

theorem block19_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 45 (by omega) (by decide +kernel))

theorem block19_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 46 (by omega) (by decide +kernel))

theorem block19_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 47 (by omega) (by decide +kernel))

theorem block19_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 48 (by omega) (by decide +kernel))

theorem block19_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 49 (by omega) (by decide +kernel))

theorem block19_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 50 (by omega) (by decide +kernel))

theorem block19_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 51 (by omega) (by decide +kernel))

theorem block19_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 52 (by omega) (by decide +kernel))

theorem block19_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 113985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 53 (by omega) (by decide +kernel))

theorem block19_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 54 (by omega) (by decide +kernel))

theorem block19_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 55 (by omega) (by decide +kernel))

theorem block19_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 56 (by omega) (by decide +kernel))

theorem block19_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 57 (by omega) (by decide +kernel))

theorem block19_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 58 (by omega) (by decide +kernel))

theorem block19_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 59 (by omega) (by decide +kernel))

theorem block19_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 60 (by omega) (by decide +kernel))

theorem block19_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 61 (by omega) (by decide +kernel))

theorem block19_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 62 (by omega) (by decide +kernel))

theorem block19_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 114625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 19 (by omega) (by omega)
      block14 block15 block18 block19 tail 63 (by omega) (by decide +kernel))

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

theorem block19_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110593 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) (110593 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block19_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowBlocks 19 block14 block15 block18 block19 tail)) 110593 64 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock19FullSourceOnly
