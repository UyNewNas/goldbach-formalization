import ImbalancedChen.P2HistoricQ80ReplayCheck00
import ImbalancedChen.P2HistoricQ80ReplayCheck01
import ImbalancedChen.P2HistoricQ80ReplayCheck02
import ImbalancedChen.P2HistoricQ80ReplayCheck03
import ImbalancedChen.P2HistoricQ80ReplayCheck04
import ImbalancedChen.P2HistoricQ80ReplayCheck05
import ImbalancedChen.P2HistoricQ80ReplayCheck06
import ImbalancedChen.P2HistoricQ80ReplayCheck07
import ImbalancedChen.P2HistoricQ80ReplayCheck08
import ImbalancedChen.P2HistoricQ80ReplayCheck09
import ImbalancedChen.P2HistoricQ80ReplayCheck10
import ImbalancedChen.P2HistoricQ80ReplayCheck11
import ImbalancedChen.P2HistoricQ80ReplayCheck12
import ImbalancedChen.P2HistoricQ80ReplayCheck13
import ImbalancedChen.P2HistoricQ80ReplayCheck14
import ImbalancedChen.P2HistoricQ80ReplayCheck15
import ImbalancedChen.P2HistoricQ80ReplayCheck16
import ImbalancedChen.P2HistoricQ80ReplayCheck17
import ImbalancedChen.P2HistoricQ80ReplayCheck18
import ImbalancedChen.P2HistoricQ80ReplayCheck19
import ImbalancedChen.P2HistoricQ80ReplayCheck20
import ImbalancedChen.P2HistoricQ80ReplayCheck21
import ImbalancedChen.P2HistoricQ80ReplayCheck22
import ImbalancedChen.P2HistoricQ80ReplayCheck23
import ImbalancedChen.P2HistoricQ80ReplayCheck24
import ImbalancedChen.P2HistoricQ80ReplayCheck25
import ImbalancedChen.P2HistoricQ80ReplayCheck26
import ImbalancedChen.P2HistoricQ80ReplayCheck27
import ImbalancedChen.P2HistoricQ80ReplayCheck28
import ImbalancedChen.P2HistoricQ80ReplayCheck29
import ImbalancedChen.P2HistoricQ80ReplayCheck30
import ImbalancedChen.P2HistoricQ80ReplayCheck31
import ImbalancedChen.P2HistoricQ80ReplayCheck32
import ImbalancedChen.P2HistoricQ80ReplayCheck33
import ImbalancedChen.P2HistoricQ80ReplayCheck34
import ImbalancedChen.P2HistoricQ80ReplayCheck35
import ImbalancedChen.P2HistoricQ80ReplayCheck36
import ImbalancedChen.P2HistoricQ80ReplayCheck37
import ImbalancedChen.P2HistoricQ80ReplayCheck38
import ImbalancedChen.P2HistoricQ80ReplayCheck39
import ImbalancedChen.P2HistoricQ80ReplayCheck40
import ImbalancedChen.P2HistoricQ80ReplayCheck41
import ImbalancedChen.P2HistoricQ80ReplayCheck42
import ImbalancedChen.P2HistoricQ80ReplayCheck43
import ImbalancedChen.P2HistoricQ80ReplayCheck44
import ImbalancedChen.P2HistoricQ80ReplayCheck45
import ImbalancedChen.P2HistoricQ80ReplayCheck46
import ImbalancedChen.P2HistoricQ80ReplayCheck47
import ImbalancedChen.P2HistoricQ80ReplayCheck48
import ImbalancedChen.P2HistoricQ80ReplayCheck49
import ImbalancedChen.P2HistoricQ80ReplayCheck50
import ImbalancedChen.P2HistoricQ80ReplayCheck51
import ImbalancedChen.P2HistoricQ80ReplayCheck52
import ImbalancedChen.P2HistoricQ80ReplayCheck53
import ImbalancedChen.P2HistoricQ80ReplayCheck54
import ImbalancedChen.P2HistoricQ80ReplayCheck55
import ImbalancedChen.P2HistoricQ80ReplayCheck56
import ImbalancedChen.P2HistoricQ80ReplayCheck57
import ImbalancedChen.P2HistoricQ80ReplayCheck58
import ImbalancedChen.P2HistoricQ80ReplayCheck59
import ImbalancedChen.P2HistoricQ80ReplayCheck60
import ImbalancedChen.P2HistoricQ80ReplayCheck61
import ImbalancedChen.P2HistoricQ80ReplayCheck62
import ImbalancedChen.P2HistoricQ80ReplayCheck63

namespace ImbalancedChen.P2HistoricQ80ReplayData
open P2HistoricSieveTableSemantics
open P2HistoricSieveFiniteReplay

theorem all_chunks_checked : ∀ b : Fin 64, ChunkChecked b := by
  intro b
  fin_cases b
  · exact chunk00_checked
  · exact chunk01_checked
  · exact chunk02_checked
  · exact chunk03_checked
  · exact chunk04_checked
  · exact chunk05_checked
  · exact chunk06_checked
  · exact chunk07_checked
  · exact chunk08_checked
  · exact chunk09_checked
  · exact chunk10_checked
  · exact chunk11_checked
  · exact chunk12_checked
  · exact chunk13_checked
  · exact chunk14_checked
  · exact chunk15_checked
  · exact chunk16_checked
  · exact chunk17_checked
  · exact chunk18_checked
  · exact chunk19_checked
  · exact chunk20_checked
  · exact chunk21_checked
  · exact chunk22_checked
  · exact chunk23_checked
  · exact chunk24_checked
  · exact chunk25_checked
  · exact chunk26_checked
  · exact chunk27_checked
  · exact chunk28_checked
  · exact chunk29_checked
  · exact chunk30_checked
  · exact chunk31_checked
  · exact chunk32_checked
  · exact chunk33_checked
  · exact chunk34_checked
  · exact chunk35_checked
  · exact chunk36_checked
  · exact chunk37_checked
  · exact chunk38_checked
  · exact chunk39_checked
  · exact chunk40_checked
  · exact chunk41_checked
  · exact chunk42_checked
  · exact chunk43_checked
  · exact chunk44_checked
  · exact chunk45_checked
  · exact chunk46_checked
  · exact chunk47_checked
  · exact chunk48_checked
  · exact chunk49_checked
  · exact chunk50_checked
  · exact chunk51_checked
  · exact chunk52_checked
  · exact chunk53_checked
  · exact chunk54_checked
  · exact chunk55_checked
  · exact chunk56_checked
  · exact chunk57_checked
  · exact chunk58_checked
  · exact chunk59_checked
  · exact chunk60_checked
  · exact chunk61_checked
  · exact chunk62_checked
  · exact chunk63_checked

theorem nodes_zero : nodes 0 = initial := rfl

theorem nodes_step (i : ℕ) (hpos : 0 < i) (hi : i ≤ 36864) :
    nodes i = update 16384 i nodes := by
  by_cases hinit : i ≤ 32768
  · have hinit' : i ≤ 2 * 16384 := by omega
    simp only [nodes, if_pos hinit, update, if_pos hinit']
  · let b : Fin 64 := ⟨(i - 32769) / 64, by omega⟩
    let j : Fin 64 := ⟨(i - 32769) % 64, Nat.mod_lt _ (by decide)⟩
    have he : 32769 + 64 * b.val + j.val = i := by
      dsimp [b, j]
      omega
    have hc := all_chunks_checked b j
    rw [he] at hc
    exact hc

/-- Complete reader equality on all indices, not only adopted queries. -/
theorem reader_eq :
    prefixReader 16384 8 36864 nodes = table 16384 8 := by
  exact prefixReader_eq (g := 16384) (maximum := 8) (N := 36864) (by decide) (by decide) nodes nodes_zero nodes_step

end ImbalancedChen.P2HistoricQ80ReplayData
