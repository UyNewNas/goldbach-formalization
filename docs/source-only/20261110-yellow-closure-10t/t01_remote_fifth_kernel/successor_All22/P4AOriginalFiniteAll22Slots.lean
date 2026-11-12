import ImbalancedChen.P4AOriginalFiniteAll22RawLedger
import ImbalancedChen.P4AOriginalFull87SavedGain
import ImbalancedChen.P4AAll22OriginalKLedger

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Closed finite slot accounting ONLY. The original constant arithmetic is
reused;this file does not assert the actual early scalar is paid. Its
partition follows CurrentUpperEighteenBudget literal indices throughout.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22Slots
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteAll22RawLedger (lowerEarlySlots upperFallbackSlots)
open P4AAll22OriginalKLedger20261024zSourceOnly
  (finalFourGains quotedAll22Raw densityReserve compilerReserve)

def laterSlots : ℝ := ∑ j : Fin 7,currentUpperEighteenGains ⟨7+j.val,by omega⟩
def eighthSlots : ℝ := (P4AOriginalFull87Saved86.savedGain:ℝ)

theorem original_G7_is_slot_six :
    P4AOriginalElevenOrderedPayment.originalFloor=currentUpperEighteenGains 6 := by rfl

/-- These are precisely the eight ORIGINAL saved87 slots,not eight new
increments. The original two winner9 refinements are already in savedGain. -/
theorem eighthSlots_exact : eighthSlots=
    (∑ j : Fin 4,currentUpperEighteenGains ⟨14+j.val,by omega⟩)+∑ j : Fin 4,finalFourGains j := by
  unfold eighthSlots
  rw [P4AOriginalFull87SavedGain.original_saved_gain_q96]
  norm_num [currentUpperEighteenGains,finalFourGains,Fin.sum_univ_succ]

theorem eighthSlots_le_original_integral : eighthSlots≤
    ∑ c : P4AOriginalFull87SourceDictionary.Cell,P4AOriginalFull87SourcePrimeTests.cellIntegral c :=
  P4AOriginalFull87SavedGain.original_saved_gain_le_integral

/-- Formal finite partition;the eighteen saving values remain opaque. -/
theorem first_eighteen_partition : (∑ i : Fin 18,currentUpperEighteenGains i)=
    lowerEarlySlots+upperFallbackSlots+currentUpperEighteenGains 3+currentUpperEighteenGains 6+
      laterSlots+(∑ j : Fin 4,currentUpperEighteenGains ⟨14+j.val,by omega⟩) := by
  unfold lowerEarlySlots upperFallbackSlots laterSlots
  simp only [Fin.sum_univ_succ]
  ring

def originalScalar : ℝ := (∑ i,currentUpperEighteenPositive i)-lowerEarlySlots-upperFallbackSlots-
  currentUpperEighteenGains 3-P4AOriginalElevenOrderedPayment.originalFloor-laterSlots-eighthSlots

theorem original_scalar_eq : originalScalar=quotedAll22Raw := by
  unfold originalScalar P4AAll22OriginalKLedger20261024zSourceOnly.quotedAll22Raw currentUpperEighteenRaw
  rw [original_G7_is_slot_six,eighthSlots_exact,first_eighteen_partition]
  ring

/-- This remains arithmetic only until every ACTUAL same-tree payment
has been joined. No analytic obligation is removed by this lemma. -/
theorem original_scalar_with_original_reserves_lt_K :
    originalScalar+densityReserve+compilerReserve<currentK := by
  rw [original_scalar_eq]
  exact P4AAll22OriginalKLedger20261024zSourceOnly.quotedAll22Raw_with_original_reserves_lt_K

end
end ImbalancedChen.P4AOriginalFiniteAll22Slots
