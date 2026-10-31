import ImbalancedChen.P2HistoricalLogCacheBlock00
import ImbalancedChen.P2HistoricalLogCacheBlock01
import ImbalancedChen.P2HistoricalLogCacheBlock02
import ImbalancedChen.P2HistoricalLogCacheBlock03
import ImbalancedChen.P2HistoricalLogCacheBlock04
import ImbalancedChen.P2HistoricalLogCacheBlock05
import ImbalancedChen.P2HistoricalLogCacheBlock06
import ImbalancedChen.P2HistoricalLogCacheBlock07
import ImbalancedChen.P2HistoricalLogCacheBlock08
import ImbalancedChen.P2HistoricalLogCacheBlock09
import ImbalancedChen.P2HistoricalLogCacheBlock10
import ImbalancedChen.P2HistoricalLogCacheBlock11
import ImbalancedChen.P2HistoricalLogCacheBlock12
import ImbalancedChen.P2HistoricalLogCacheBlock13
import ImbalancedChen.P2HistoricalLogCacheBlock14
import ImbalancedChen.P2HistoricalLogCacheBlock15
import ImbalancedChen.P2HistoricalLogCacheBlock16
import ImbalancedChen.P2HistoricalLogCacheBlock17
import ImbalancedChen.P2HistoricalLogCacheBlock18
import ImbalancedChen.P2HistoricalLogCacheBlock19
import ImbalancedChen.P2HistoricalLogCacheBlock20
import ImbalancedChen.P2HistoricalLogCacheBlock21
import ImbalancedChen.P2HistoricalLogCacheBlock22
import ImbalancedChen.P2HistoricalLogCacheBlock23
import ImbalancedChen.P2HistoricalSavedFloorFullSourceCore

namespace ImbalancedChen.P2HistoricalLogCache
open Certificates.P2HistoricQ80DefectLookup Certificates.P2HistoricLogPointInterpreter
open P2HistoricalSavedFloorFullBinder
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def cache : List (ℚ × I80) :=
  [block00, block01, block02, block03, block04, block05, block06, block07, block08, block09, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23].flatten

theorem cache_checked : ∀ p ∈ cache, p.2 = logI p.1 := by
  intro p hp
  simp only [cache, List.mem_flatten] at hp
  obtain ⟨l, hl, hp⟩ := hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block00_checked p hp
  · exact block01_checked p hp
  · exact block02_checked p hp
  · exact block03_checked p hp
  · exact block04_checked p hp
  · exact block05_checked p hp
  · exact block06_checked p hp
  · exact block07_checked p hp
  · exact block08_checked p hp
  · exact block09_checked p hp
  · exact block10_checked p hp
  · exact block11_checked p hp
  · exact block12_checked p hp
  · exact block13_checked p hp
  · exact block14_checked p hp
  · exact block15_checked p hp
  · exact block16_checked p hp
  · exact block17_checked p hp
  · exact block18_checked p hp
  · exact block19_checked p hp
  · exact block20_checked p hp
  · exact block21_checked p hp
  · exact block22_checked p hp
  · exact block23_checked p hp

def fastLog : ℚ → I80 := applyCache cache logI

/-- Unconditional equality to the original actualLog, with original fallback. -/
theorem fastLog_eq_actualLog : fastLog = actualLog :=
  applyCache_eq logI cache cache_checked

end ImbalancedChen.P2HistoricalLogCache
