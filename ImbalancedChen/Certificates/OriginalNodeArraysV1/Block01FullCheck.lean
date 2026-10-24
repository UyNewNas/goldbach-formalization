import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block01Data
import ImbalancedChen.Certificates.OriginalNodeArraysV1.PageTransfer

/- All4096 original Block01 updates retain the universally quantified same tail.
Each64row reference check is a kernel proof, not a premise. -/

namespace ImbalancedChen.OriginalU2StoredNodeBlock01FullSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalStoredPageTransferSourceOnly

theorem block01_page00_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      36865 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 0 (by omega) (by decide +kernel))

theorem block01_page01_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      36929 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 1 (by omega) (by decide +kernel))

theorem block01_page02_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      36993 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 2 (by omega) (by decide +kernel))

theorem block01_page03_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      37057 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 3 (by omega) (by decide +kernel))

theorem block01_page04_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      37121 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 4 (by omega) (by decide +kernel))

theorem block01_page05_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      37185 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 5 (by omega) (by decide +kernel))

theorem block01_page06_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      37249 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 6 (by omega) (by decide +kernel))

theorem block01_page07_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      37313 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 7 (by omega) (by decide +kernel))

theorem block01_page08_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37377 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega) block00 block01 tail 8 (by omega) (by decide +kernel))

theorem block01_page09_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37441 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega) block00 block01 tail 9 (by omega) (by decide +kernel))

theorem block01_page10_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37505 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega) block00 block01 tail 10 (by omega) (by decide +kernel))

theorem block01_page11_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37569 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega) block00 block01 tail 11 (by omega) (by decide +kernel))

theorem block01_page12_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37633 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega) block00 block01 tail 12 (by omega) (by decide +kernel))

theorem block01_page13_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37697 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega) block00 block01 tail 13 (by omega) (by decide +kernel))

theorem block01_page14_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37761 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega) block00 block01 tail 14 (by omega) (by decide +kernel))

theorem block01_page15_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37825 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega) block00 block01 tail 15 (by omega) (by decide +kernel))

theorem block01_page16_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37889 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 16 (by omega) (by decide +kernel))

theorem block01_page17_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 37953 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 17 (by omega) (by decide +kernel))

theorem block01_page18_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38017 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 18 (by omega) (by decide +kernel))

theorem block01_page19_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38081 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 19 (by omega) (by decide +kernel))

theorem block01_page20_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38145 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 20 (by omega) (by decide +kernel))

theorem block01_page21_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38209 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 21 (by omega) (by decide +kernel))

theorem block01_page22_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38273 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 22 (by omega) (by decide +kernel))

theorem block01_page23_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38337 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 23 (by omega) (by decide +kernel))

theorem block01_page24_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38401 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 24 (by omega)
      (by decide +kernel))

theorem block01_page25_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38465 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 25 (by omega)
      (by decide +kernel))

theorem block01_page26_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38529 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 26 (by omega)
      (by decide +kernel))

theorem block01_page27_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38593 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 27 (by omega)
      (by decide +kernel))

theorem block01_page28_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38657 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 28 (by omega)
      (by decide +kernel))

theorem block01_page29_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38721 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 29 (by omega)
      (by decide +kernel))

theorem block01_page30_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38785 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 30 (by omega)
      (by decide +kernel))

theorem block01_page31_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38849 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 31 (by omega)
      (by decide +kernel))

theorem block01_page32_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38913 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 32 (by omega) (by decide +kernel))
theorem block01_page33_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 38977 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 33 (by omega) (by decide +kernel))
theorem block01_page34_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39041 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 34 (by omega) (by decide +kernel))
theorem block01_page35_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39105 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 35 (by omega) (by decide +kernel))
theorem block01_page36_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39169 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 36 (by omega) (by decide +kernel))
theorem block01_page37_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39233 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 37 (by omega) (by decide +kernel))
theorem block01_page38_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39297 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 38 (by omega) (by decide +kernel))
theorem block01_page39_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39361 64 = true := by
  simpa only [Nat.reduceAdd,Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 39 (by omega) (by decide +kernel))

theorem block01_page40_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39425 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 40 (by omega) (by decide +kernel))
theorem block01_page41_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39489 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 41 (by omega) (by decide +kernel))
theorem block01_page42_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39553 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 42 (by omega) (by decide +kernel))
theorem block01_page43_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39617 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 43 (by omega) (by decide +kernel))
theorem block01_page44_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39681 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 44 (by omega) (by decide +kernel))
theorem block01_page45_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39745 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 45 (by omega) (by decide +kernel))
theorem block01_page46_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39809 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 46 (by omega) (by decide +kernel))
theorem block01_page47_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 39873 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 47 (by omega) (by decide +kernel))

theorem block01_page48_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      (36865 + 64 * 48) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 48 (by omega)
      (by decide +kernel))

theorem block01_page49_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      (36865 + 64 * 49) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 49 (by omega)
      (by decide +kernel))

theorem block01_page50_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      (36865 + 64 * 50) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 50 (by omega)
      (by decide +kernel))

theorem block01_page51_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      (36865 + 64 * 51) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 51 (by omega)
      (by decide +kernel))

theorem block01_page52_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      (36865 + 64 * 52) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 52 (by omega)
      (by decide +kernel))

theorem block01_page53_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      (36865 + 64 * 53) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 53 (by omega)
      (by decide +kernel))

theorem block01_page54_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      (36865 + 64 * 54) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 54 (by omega)
      (by decide +kernel))

theorem block01_page55_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail))
      (36865 + 64 * 55) 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03
      1 (by omega) (by omega) block00 block01 tail 55 (by omega)
      (by decide +kernel))

theorem block01_page56_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 40449 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 56 (by omega) (by decide +kernel))

theorem block01_page57_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 40513 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 57 (by omega) (by decide +kernel))

theorem block01_page58_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 40577 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 58 (by omega) (by decide +kernel))

theorem block01_page59_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 40641 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 59 (by omega) (by decide +kernel))

theorem block01_page60_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 40705 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 60 (by omega) (by decide +kernel))

theorem block01_page61_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 40769 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 61 (by omega) (by decide +kernel))

theorem block01_page62_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 40833 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 62 (by omega) (by decide +kernel))

theorem block01_page63_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 40897 64 = true := by
  simpa only [Nat.reduceAdd, Nat.reduceMul] using
    (windowPrevCurrent_page_transfer_blocks01to03 1 (by omega) (by omega)
      block00 block01 tail 63 (by omega) (by decide +kernel))

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

theorem block01_all_pages_checked (tail : Nat → Block) :
    readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 36865 4096 = true := by
  have hpages : ∀ p : Nat, p < 64 →
      readCheckBlock (assembledRead (windowPrevCurrent 1 block00 block01 tail)) (36865 + 64*p) 64 = true := by
    intro p hp
    interval_cases p
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page00_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page01_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page02_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page03_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page04_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page05_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page06_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page07_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page08_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page09_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page10_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page11_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page12_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page13_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page14_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page15_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page16_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page17_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page18_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page19_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page20_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page21_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page22_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page23_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page24_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page25_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page26_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page27_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page28_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page29_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page30_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page31_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page32_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page33_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page34_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page35_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page36_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page37_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page38_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page39_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page40_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page41_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page42_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page43_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page44_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page45_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page46_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page47_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page48_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page49_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page50_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page51_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page52_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page53_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page54_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page55_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page56_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page57_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page58_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page59_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page60_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page61_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page62_checked tail
    · simpa only [Nat.reduceAdd, Nat.reduceMul] using block01_page63_checked tail
  exact readCheckBlock_of_64_page_count
    (assembledRead (windowPrevCurrent 1 block00 block01 tail)) 36865 64 hpages


end ImbalancedChen.OriginalU2StoredNodeBlock01FullSourceOnly
