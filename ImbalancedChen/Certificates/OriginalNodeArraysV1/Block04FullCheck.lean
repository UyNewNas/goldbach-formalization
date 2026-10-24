-- SOURCEONLY candidate. UNCOMPILED / NOT PASS.
-- 64 exact kernel `decide +kernel` page checks over the frozen Block04 literals.
-- Block04 page starts are 49153 + 64*p; final row is 53248.
-- Frozen raw Block04 values are carried by Block04Data.lean.txt; its installation name is Block04Data.lean.
-- Block00Data SHA256 078a7959c4aa7d162efbd66bd83d025ae10d5599b7c9490ac8df165f4774904c
-- Block03Data is an adjacent source-only dependency; contract: export `block03 : Block` in `ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly`.
-- Block04Data must export `block04 : Block` in the same namespace.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block03Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block04Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.DelayedPageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock04FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

/-- At Block04's first step, the delayed input row is 32768, so the
    physical slot is discarded by the actual initialized-prefix reader. -/
theorem block04_first_delayed_read_is_prefix (tail : Nat → Block) :
    (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) (32769+4096*4-16385) =
      ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.integerInitial := by
  exact (block04_first_delayed_is_prefix block00 block00 block03 block04 tail).1

-- Check the full type: the initial node is the fixed imported constant,
-- not an accidentally auto-implicit arbitrary node parameter.
#check (@block04_first_delayed_read_is_prefix : ∀ tail : Nat → Block,
  (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail))
    (32769+4096*4-16385) =
      ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly.integerInitial)

theorem block04_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49153 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 0 (by omega) (by decide +kernel))

theorem block04_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49217 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 1 (by omega) (by decide +kernel))

theorem block04_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49281 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 2 (by omega) (by decide +kernel))

theorem block04_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49345 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 3 (by omega) (by decide +kernel))

theorem block04_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49409 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 4 (by omega) (by decide +kernel))

theorem block04_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49473 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 5 (by omega) (by decide +kernel))

theorem block04_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49537 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 6 (by omega) (by decide +kernel))

theorem block04_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49601 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 7 (by omega) (by decide +kernel))

theorem block04_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49665 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 8 (by omega) (by decide +kernel))

theorem block04_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49729 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 9 (by omega) (by decide +kernel))

theorem block04_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49793 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 10 (by omega) (by decide +kernel))

theorem block04_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49857 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 11 (by omega) (by decide +kernel))

theorem block04_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49921 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 12 (by omega) (by decide +kernel))

theorem block04_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49985 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 13 (by omega) (by decide +kernel))

theorem block04_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50049 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 14 (by omega) (by decide +kernel))

theorem block04_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50113 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 15 (by omega) (by decide +kernel))

theorem block04_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50177 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 16 (by omega) (by decide +kernel))

theorem block04_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50241 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 17 (by omega) (by decide +kernel))

theorem block04_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50305 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 18 (by omega) (by decide +kernel))

theorem block04_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50369 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 19 (by omega) (by decide +kernel))

theorem block04_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50433 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 20 (by omega) (by decide +kernel))

theorem block04_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50497 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 21 (by omega) (by decide +kernel))

theorem block04_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50561 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 22 (by omega) (by decide +kernel))

theorem block04_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50625 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 23 (by omega) (by decide +kernel))

theorem block04_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50689 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 24 (by omega) (by decide +kernel))

theorem block04_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50753 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 25 (by omega) (by decide +kernel))

theorem block04_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50817 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 26 (by omega) (by decide +kernel))

theorem block04_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50881 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 27 (by omega) (by decide +kernel))

theorem block04_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 50945 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 28 (by omega) (by decide +kernel))

theorem block04_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51009 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 29 (by omega) (by decide +kernel))

theorem block04_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51073 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 30 (by omega) (by decide +kernel))

theorem block04_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51137 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 31 (by omega) (by decide +kernel))

theorem block04_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51201 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 32 (by omega) (by decide +kernel))

theorem block04_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51265 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 33 (by omega) (by decide +kernel))

theorem block04_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51329 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 34 (by omega) (by decide +kernel))

theorem block04_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51393 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 35 (by omega) (by decide +kernel))

theorem block04_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51457 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 36 (by omega) (by decide +kernel))

theorem block04_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51521 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 37 (by omega) (by decide +kernel))

theorem block04_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51585 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 38 (by omega) (by decide +kernel))

theorem block04_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51649 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 39 (by omega) (by decide +kernel))

theorem block04_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51713 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 40 (by omega) (by decide +kernel))

theorem block04_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51777 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 41 (by omega) (by decide +kernel))

theorem block04_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51841 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 42 (by omega) (by decide +kernel))

theorem block04_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51905 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 43 (by omega) (by decide +kernel))

theorem block04_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 51969 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 44 (by omega) (by decide +kernel))

theorem block04_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52033 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 45 (by omega) (by decide +kernel))

theorem block04_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52097 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 46 (by omega) (by decide +kernel))

theorem block04_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52161 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 47 (by omega) (by decide +kernel))

theorem block04_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52225 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 48 (by omega) (by decide +kernel))

theorem block04_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52289 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 49 (by omega) (by decide +kernel))

theorem block04_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52353 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 50 (by omega) (by decide +kernel))

theorem block04_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52417 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 51 (by omega) (by decide +kernel))

theorem block04_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52481 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 52 (by omega) (by decide +kernel))

theorem block04_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52545 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 53 (by omega) (by decide +kernel))

theorem block04_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52609 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 54 (by omega) (by decide +kernel))

theorem block04_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52673 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 55 (by omega) (by decide +kernel))

theorem block04_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52737 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 56 (by omega) (by decide +kernel))

theorem block04_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52801 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 57 (by omega) (by decide +kernel))

theorem block04_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 58 (by omega) (by decide +kernel))

theorem block04_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 59 (by omega) (by decide +kernel))

theorem block04_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 52993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 60 (by omega) (by decide +kernel))

theorem block04_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 53057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 61 (by omega) (by decide +kernel))

theorem block04_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 53121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 62 (by omega) (by decide +kernel))

theorem block04_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 53185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (window_page_transfer_blocks04to39 4 (by omega) (by omega)
      block00 block00 block03 block04 tail 63 (by omega) (by decide +kernel))

theorem block04_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49153 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) (49153 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block04_page63_checked tail
  exact readCheckBlock_of_64_pages (assembledRead (windowBlocks 4 block00 block00 block03 block04 tail)) 49153 hpages

/-- Specialize the frozen slots to one immutable block table. This is the
    same reader used by assembledRawRead, so the current, previous, delayed,
    and delayed-successor reads all refer to this one table. -/
theorem block04_all_pages_checked_same_table (blocks : Nat → Block)
    (h0 : blocks 0 = block00) (h3 : blocks 3 = block03)
    (h4 : blocks 4 = block04) :
    readCheckBlock (assembledRead blocks) 49153 4096 = true := by
  have hslots : windowBlocks 4 block00 block00 block03 block04 blocks =
      windowBlocks 4 (blocks (4-5)) (blocks (4-4))
        (blocks (4-1)) (blocks 4) blocks := by
    simp only [Nat.reduceSub]
    rw [← h0, ← h3, ← h4]
  have hwindow : windowBlocks 4 block00 block00 block03 block04 blocks = blocks := by
    rw [hslots]
    exact windowBlocks_eq_original 4 blocks
  rw [← hwindow]
  exact block04_all_pages_checked blocks

end ImbalancedChen.OriginalU2StoredNodeBlock04FullSourceOnly
