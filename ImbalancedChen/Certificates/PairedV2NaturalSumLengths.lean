import ImbalancedChen.Certificates.PairedV2NaturalSumPartition
import ImbalancedChen.Certificates.PairedV2NaturalSumExpectedLengths
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock00
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock01
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock02
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock03
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock04
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock05
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock06
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock07
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock08
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock09
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock10
import ImbalancedChen.Certificates.PairedV2NaturalSumLengthsBlock11

/-! Layered length assembly over symbolic blocks and small Nat tables.
No monolithic dependent cases and no whole-data numerical decision. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem blocks_lengths : blocks.flatten.map List.length = expectedLengths := by
  calc
    blocks.flatten.map List.length = block00.map List.length ++ (block01.map List.length ++ (block02.map List.length ++ (block03.map List.length ++ (block04.map List.length ++ (block05.map List.length ++ (block06.map List.length ++ (block07.map List.length ++ (block08.map List.length ++ (block09.map List.length ++ (block10.map List.length ++ (block11.map List.length ++ []))))))))))) := by
      simp only [blocks, List.flatten_cons, List.flatten_nil,
        List.map_append, List.map_nil]
    _ = expectedLengths := by
      (rw [block00_lengths, block01_lengths, block02_lengths, block03_lengths, block04_lengths, block05_lengths, block06_lengths, block07_lengths, block08_lengths, block09_lengths, block10_lengths, block11_lengths]; rfl)

theorem approximation_lengths : ∀ i : Fin 186,
    (approximations i).length = 512 - firstU i := by
  have hlist :
      (List.ofFn approximations).map List.length =
        List.ofFn (fun i : Fin 186 => 512 - firstU i) :=
    (congrArg (List.map List.length) approximations_partition).trans
      (blocks_lengths.trans firstU_lengths_list.symm)
  have hfn : (fun i : Fin 186 => (approximations i).length) =
      (fun i : Fin 186 => 512 - firstU i) :=
    List.ofFn_injective
      ((List.ofFn_comp' approximations List.length).trans hlist)
  exact fun i => congrFun hfn i

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
