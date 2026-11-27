-- SOURCEONLY generated candidate. UNCOMPILED / NOT PASS / no admission asserted.
-- ROOT owns installation, strict checking, stock replay, and any admission.
-- Page starts: 32769 + 4096*3 + 64*p; full block ends at49152.
-- Llo: block-03.Llo.dec SHA256 027f29119680a156b756a9b7f2c565303e8a1e2d83e83595c742347e211d1609
-- Lhi: block-03.Lhi.dec SHA256 88ba48cf6eaa587df738cc8ba6036500c0b67eedbdaa2da8e6c2609989c587b5
-- Hlo: block-03.Hlo.dec SHA256 6e65648eb7fea7361633a6812598947c25af573f7041e12bca37598f27e470e2
-- Hhi: block-03.Hhi.dec SHA256 6e65648eb7fea7361633a6812598947c25af573f7041e12bca37598f27e470e2
import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block02Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block03Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.PageTransfer

namespace ImbalancedChen.OriginalU2StoredNodeBlock03FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredPageTransferSourceOnly

theorem block03_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 0 (by omega) (by decide +kernel))

theorem block03_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 1 (by omega) (by decide +kernel))

theorem block03_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 2 (by omega) (by decide +kernel))

theorem block03_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 3 (by omega) (by decide +kernel))

theorem block03_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 4 (by omega) (by decide +kernel))

theorem block03_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 5 (by omega) (by decide +kernel))

theorem block03_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 6 (by omega) (by decide +kernel))

theorem block03_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 7 (by omega) (by decide +kernel))

theorem block03_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 8 (by omega) (by decide +kernel))

theorem block03_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 9 (by omega) (by decide +kernel))

theorem block03_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 10 (by omega) (by decide +kernel))

theorem block03_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 11 (by omega) (by decide +kernel))

theorem block03_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 12 (by omega) (by decide +kernel))

theorem block03_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45889 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 13 (by omega) (by decide +kernel))

theorem block03_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45953 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 14 (by omega) (by decide +kernel))

theorem block03_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46017 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 15 (by omega) (by decide +kernel))

theorem block03_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46081 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 16 (by omega) (by decide +kernel))

theorem block03_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46145 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 17 (by omega) (by decide +kernel))

theorem block03_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46209 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 18 (by omega) (by decide +kernel))

theorem block03_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46273 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 19 (by omega) (by decide +kernel))

theorem block03_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46337 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 20 (by omega) (by decide +kernel))

theorem block03_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 21 (by omega) (by decide +kernel))

theorem block03_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 22 (by omega) (by decide +kernel))

theorem block03_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 23 (by omega) (by decide +kernel))

theorem block03_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 24 (by omega) (by decide +kernel))

theorem block03_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 25 (by omega) (by decide +kernel))

theorem block03_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 26 (by omega) (by decide +kernel))

theorem block03_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 27 (by omega) (by decide +kernel))

theorem block03_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 28 (by omega) (by decide +kernel))

theorem block03_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46913 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 29 (by omega) (by decide +kernel))

theorem block03_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 46977 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 30 (by omega) (by decide +kernel))

theorem block03_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47041 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 31 (by omega) (by decide +kernel))

theorem block03_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47105 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 32 (by omega) (by decide +kernel))

theorem block03_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47169 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 33 (by omega) (by decide +kernel))

theorem block03_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47233 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 34 (by omega) (by decide +kernel))

theorem block03_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47297 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 35 (by omega) (by decide +kernel))

theorem block03_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47361 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 36 (by omega) (by decide +kernel))

theorem block03_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 37 (by omega) (by decide +kernel))

theorem block03_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 38 (by omega) (by decide +kernel))

theorem block03_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 39 (by omega) (by decide +kernel))

theorem block03_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 40 (by omega) (by decide +kernel))

theorem block03_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 41 (by omega) (by decide +kernel))

theorem block03_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 42 (by omega) (by decide +kernel))

theorem block03_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 43 (by omega) (by decide +kernel))

theorem block03_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 44 (by omega) (by decide +kernel))

theorem block03_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 47937 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 45 (by omega) (by decide +kernel))

theorem block03_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48001 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 46 (by omega) (by decide +kernel))

theorem block03_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48065 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 47 (by omega) (by decide +kernel))

theorem block03_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48129 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 48 (by omega) (by decide +kernel))

theorem block03_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48193 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 49 (by omega) (by decide +kernel))

theorem block03_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48257 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 50 (by omega) (by decide +kernel))

theorem block03_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48321 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 51 (by omega) (by decide +kernel))

theorem block03_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48385 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 52 (by omega) (by decide +kernel))

theorem block03_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 53 (by omega) (by decide +kernel))

theorem block03_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 54 (by omega) (by decide +kernel))

theorem block03_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 55 (by omega) (by decide +kernel))

theorem block03_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 56 (by omega) (by decide +kernel))

theorem block03_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 57 (by omega) (by decide +kernel))

theorem block03_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 58 (by omega) (by decide +kernel))

theorem block03_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 59 (by omega) (by decide +kernel))

theorem block03_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 60 (by omega) (by decide +kernel))

theorem block03_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 48961 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 61 (by omega) (by decide +kernel))

theorem block03_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 49025 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 62 (by omega) (by decide +kernel))

theorem block03_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 49089 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      3 (by omega) (by omega) block02 block03 tail 63 (by omega) (by decide +kernel))

theorem block03_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45057 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowPrevCurrent 3 block02 block03 tail)) (45057 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block03_page63_checked tail
  exact readCheckBlock_of_64_pages
    (assembledRead (windowPrevCurrent 3 block02 block03 tail)) 45057 hpages

end ImbalancedChen.OriginalU2StoredNodeBlock03FullSourceOnly
