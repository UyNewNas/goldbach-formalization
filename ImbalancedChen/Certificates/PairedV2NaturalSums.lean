import ImbalancedChen.Certificates.PairedV2NaturalSumRowAssembly
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock00
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock01
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock02
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock03
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock04
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock05
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock06
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock07
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock08
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock09
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock10
import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock11

/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/


namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0


/-- Exact numerator sum over every `FullMask.Row`, at the unchanged 10^20 scale. -/
theorem lower_numerator_sum :
    (∑ r : Row, (approximation r).lower) = 55858378943374979 := by
  rw [sum_rows_eq_list, approximations_partition]
  simp only [blocks, List.flatten_cons, List.flatten_nil, List.map_append,
    List.map_nil, List.sum_append, List.sum_nil]
  (rw [block00_lower, block01_lower, block02_lower, block03_lower, block04_lower, block05_lower, block06_lower, block07_lower, block08_lower, block09_lower, block10_lower, block11_lower]; rfl)

/-- Exact numerator sum over every `FullMask.Row`, at the unchanged 10^20 scale. -/
theorem upper_numerator_sum :
    (∑ r : Row, (approximation r).upper) = 55858409959907296 := by
  rw [sum_rows_eq_list, approximations_partition]
  simp only [blocks, List.flatten_cons, List.flatten_nil, List.map_append,
    List.map_nil, List.sum_append, List.sum_nil]
  (rw [block00_upper, block01_upper, block02_upper, block03_upper, block04_upper, block05_upper, block06_upper, block07_upper, block08_upper, block09_upper, block10_upper, block11_upper]; rfl)


end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
