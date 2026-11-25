import ImbalancedChen.P4AOriginalCausalHistory

/-!
The unchanged finite archive schedule constructor, separated from the
fourteen-family analytic endpoint. The public namespace and definition
are preserved from the original source.

SOURCE CANDIDATE / NOT COMPILED.
-/
namespace ImbalancedChen.P4AOriginalCommonArchiveSchedule
noncomputable section
open P4AOriginalCausalHistory
open P2OriginalFourthCapProducerInterface

/-- No N occurs in these finite fields. All third decisions read the
original first-three label; fourth and fifth rows stay at their own ranks. -/
def fixedSchedule (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (omega : ℝ) : ArchiveSchedule :=
  ⟨rows4, licensed4, e, q, (e : ℝ) / 20, omega⟩

end
end ImbalancedChen.P4AOriginalCommonArchiveSchedule
