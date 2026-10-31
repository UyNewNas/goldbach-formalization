import ImbalancedChen.P2HistoricalLogCacheChecked

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
open P2HistoricalSavedFloorFullBinder

def applyBlockCache (blocks : List (ℚ × List (ℚ × I80)))
    (fallback : ℚ → I80) : ℚ → I80 :=
  blocks.foldr
    (fun b f q => if q ≤ b.1 then applyCache b.2 fallback q else f q) fallback

/-- Guards select already-correct blocks; no ordering or coverage assumption is needed. -/
theorem applyBlockCache_eq (fallback : ℚ → I80) :
    ∀ blocks : List (ℚ × List (ℚ × I80)),
      (∀ b ∈ blocks, ∀ p ∈ b.2, p.2 = fallback p.1) →
      applyBlockCache blocks fallback = fallback := by
  intro blocks
  induction blocks with
  | nil =>
      intro h
      rfl
  | cons b bs ih =>
      intro h
      have hb : ∀ p ∈ b.2, p.2 = fallback p.1 := h b (by simp)
      have ht : ∀ c ∈ bs, ∀ p ∈ c.2, p.2 = fallback p.1 := by
        intro c hc
        exact h c (by simp [hc])
      funext q
      change (if q ≤ b.1 then applyCache b.2 fallback q
        else applyBlockCache bs fallback q) = fallback q
      rw [applyCache_eq fallback b.2 hb, ih ht]
      split_ifs <;> rfl

def blocks : List (ℚ × List (ℚ × I80)) :=
  [((1923547 / 1922896 : ℚ), block00),
   ((1913131 / 1912480 : ℚ), block01),
   ((1902715 / 1902064 : ℚ), block02),
   ((1892299 / 1891648 : ℚ), block03),
   ((1881883 / 1881232 : ℚ), block04),
   ((1871467 / 1870816 : ℚ), block05),
   ((1861051 / 1860400 : ℚ), block06),
   ((1850635 / 1849984 : ℚ), block07),
   ((1840219 / 1839568 : ℚ), block08),
   ((1829803 / 1829152 : ℚ), block09),
   ((1819387 / 1818736 : ℚ), block10),
   ((387405 / 387062 : ℚ), block11),
   ((381917 / 381574 : ℚ), block12),
   ((376429 / 376086 : ℚ), block13),
   ((370941 / 370598 : ℚ), block14),
   ((365453 / 365110 : ℚ), block15),
   ((359965 / 359622 : ℚ), block16),
   ((354477 / 354134 : ℚ), block17),
   ((348989 / 348646 : ℚ), block18),
   ((343501 / 343158 : ℚ), block19),
   ((338013 / 337670 : ℚ), block20),
   ((332525 / 332182 : ℚ), block21),
   ((327037 / 326694 : ℚ), block22),
   ((323950 / 323607 : ℚ), block23)]

theorem blocks_checked : ∀ b ∈ blocks, ∀ p ∈ b.2, p.2 = logI p.1 := by
  intro b hb
  simp only [blocks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block00_checked
  · exact block01_checked
  · exact block02_checked
  · exact block03_checked
  · exact block04_checked
  · exact block05_checked
  · exact block06_checked
  · exact block07_checked
  · exact block08_checked
  · exact block09_checked
  · exact block10_checked
  · exact block11_checked
  · exact block12_checked
  · exact block13_checked
  · exact block14_checked
  · exact block15_checked
  · exact block16_checked
  · exact block17_checked
  · exact block18_checked
  · exact block19_checked
  · exact block20_checked
  · exact block21_checked
  · exact block22_checked
  · exact block23_checked

def fastLogBlocked : ℚ → I80 := applyBlockCache blocks logI

theorem fastLogBlocked_eq_actualLog : fastLogBlocked = actualLog :=
  applyBlockCache_eq logI blocks blocks_checked

end ImbalancedChen.P2HistoricalLogCache
