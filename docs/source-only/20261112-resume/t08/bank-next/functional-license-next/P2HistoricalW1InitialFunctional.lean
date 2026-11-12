import ImbalancedChen.P2HistoricalW1LastFunctional
import ImbalancedChen.P2WuUpperBuchstabEndpointBounds

namespace ImbalancedChen.P2HistoricalW1InitialFunctional

noncomputable section
open Wu2008DoubleSieve P2TableActionSourceOnly P2Historical248Authentication
open P2HistoricalScheduledPointReads P2HistoricalHighPointAncestry P2HistoricalLowerBankAncestry
open P2HistoricalW1LastFunctional P2HistoricalNativePointCounts P2HistoricalLowTargetEdges

private theorem seed_weights_zero (rs : List Weight) : sourceWeightSum (outputAt 0) false rs = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [sourceWeightSum,outputAt,iterate,originalSeed] at ih ⊢ <;> exact ih

private theorem high_seed_zero (i : Fin 200) (hi : 100 ≤ i.val) : outputAt 0 true i=0 := by
  simp [outputAt,iterate,originalSeed,show ¬i.val<60 by omega]

theorem initial_complete_value_eq_base {a : SourceW1} (ha : a∈sourceW1Schedule 0) :
    sourceW1Value (outputAt 0) a = a.effectiveBase := by
  rw [sourceW1Value,seed_weights_zero,high_seed_zero a.pointIndex (scheduled_w1_point 0 ha).1]
  simp

def firstPositive (a : SourceW1) : Bool := decide (a.s=5/2 ∧ a.s0=16/5)

/-- The original raw base and the range of its actual target indices.
There is no history replay in this check. -/
private theorem first_record :
    w1Original.any firstPositive = true ∧
    w1Original.all (fun a => !firstPositive a ||
      (decide (a.effectiveBase = 1161320826237498322233) &&
        a.targets.all (fun i => decide (i.val ≤ 74)))) = true := by decide

theorem initial_positive_present : ∃ a ∈ sourceW1Schedule 0, firstPositive a=true :=
  List.any_eq_true.mp first_record.1

/-- The actual positive historical first update is covered on every one
of its original target cells. Its untouched retained seed is separate. -/
theorem initial_positive_licensed {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/100)
    {a : SourceW1} (ha : a∈sourceW1Schedule 0) (hc : firstPositive a=true) :
    0 < sourceW1Value (outputAt 0) a ∧ ∀ i ∈ a.targets,
      (sourceW1Value (outputAt 0) a : ℝ)/tableQ ≤ H δ (tableGrid (i.val+1)) := by
  have hf := List.all_eq_true.mp first_record.2 a (show a∈w1Original from ha)
  simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hf
  rw [initial_complete_value_eq_base ha, hf.1]
  refine ⟨by norm_num, ?_⟩
  intro i hi
  have hstop : i.val ≤ 74 := of_decide_eq_true (List.all_eq_true.mp hf.2 i hi)
  have hs := tableGrid_mono (show i.val+1 ≤ 75 by omega)
  have hs' : tableGrid (i.val+1) ≤ 5/2 := hs.trans_eq (by norm_num [tableGrid])
  have hb := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
  have hmono := wuImprovementLimit_upper_antitone hd (by linarith : δ≤1/10)
    ⟨hb.1,hb.2.trans (by norm_num)⟩ ⟨by norm_num,by norm_num⟩ hs'
  exact (show (1161320826237498322233 : ℝ)/tableQ ≤ 1/300 by norm_num [tableQ]).trans
    ((P2WuUpperBuchstabEndpointBounds.upper_anchor_one_hundredth hd hd').le.trans hmono)

/-- First two predecessors for the terminal row. At g=0 all h entries vanish.
At g=1 the old h is paid by H0, and its H(5) anchor still vanishes. -/
theorem terminal_initial_steps {δ : ℝ} (hd : 0<δ) (hd' : δ≤1/10) :
    (∀ a ∈ sourceW1Schedule 0, lastRow a=true → sourceW1Value (outputAt 0) a ≤ 0) ∧
    ((∀ i : Fin 200, i.val ∈ edges → readGain 0 i ≤ H δ (tableGrid (i.val+1))) →
      ∀ a ∈ sourceW1Schedule 1, lastRow a=true → sourceW1Value (outputAt 1) a ≤ 0) := by
  constructor
  · intro a ha hl
    have hz := high_seed_zero a.pointIndex (scheduled_w1_point _ ha).1
    rw [← hz]
    apply complete_row_le_own_point 0 hd hd' ha hl
    intro i _
    have hb := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
    simpa [outputAt,iterate,originalSeed,h] using wuImprovementLimit_nonneg false hd
      (by linarith : δ<1/2) hb.1 (hb.2.trans (by norm_num))
  · intro he a ha hl
    have hp := upper_endpoints_from_low designatedW1 designatedW2 hd hd' designated_low_writes 0
      (low_of_edges 0 hd hd' he) 0 le_rfl
    have hr := complete_row_le_own_point 1 hd hd' ha hl (fun i _ =>
      iterate_lower_endpoints hd hd' designatedW1 designatedW2 0 hp i)
    have hz : outputAt 1 true a.pointIndex=0 := by
      rw [show outputAt 1 true a.pointIndex = _ from high_last_suffix _ _ designated_low_writes 0
        a.pointIndex (scheduled_w1_point 1 ha).1]
      simp [outputAt,iterate,P2SimultaneousTableSourceOnly.suffixNumerator,P2SimultaneousTableSourceOnly.read,originalSeed]
    simpa only [hz] using hr

end
end ImbalancedChen.P2HistoricalW1InitialFunctional
