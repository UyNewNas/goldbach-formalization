import ImbalancedChen.P2HistoricalArchivedActionFeedback
import ImbalancedChen.Part5OriginalH430W1TrueConvertedBase

/-! Real prices for both actual historical W1 phases via the independent
stronger enclosure of the corresponding 430 base. The comparison is on
base integers only; no improvement entry is imported from H430. -/
namespace ImbalancedChen.P2HistoricalW1RealBase

noncomputable section
open Set
open P2TableActionSourceOnly P2Historical248Authentication P2HistoricalScheduledPointReads
open P2HistoricalArchivedActionFeedback (w1Feedback w1_candidate_le_old_profile)
open P2Selected430LiteralActionData (rows)
open P5OriginalActionMassBound (W1Target W1Anchor)
open Part5OriginalH430BankSlotTargets (slotOfAction)
open Part5OriginalH430FixedReadDictionary (baseValue)
open Part5OriginalH430W1SignedOrdinaryBase (ordinaryBase switchedDebt)
open Part5OriginalH430W1SwitchedBuchstabIntegral (envelope switchedIntegral)
open Part5OriginalH430W1OriginalBaseEnclosure
  (tableK all70_archived_base_vs_envelope all70_archived_base_vs_true_integral)
open Part5OriginalH430W1TrueConvertedBase (primeDebt all70_true_converted_base)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift (thetaAtom_nonneg sameQ_residual_gt_one)
open P2AllW1FrozenReceiverFiniteAction (rawTripleCount)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedSwitchedTrueNormalization (trueAlpha)
open P5OriginalU5FrozenSource (receiver)

private def baseFits (a : SourceW1) (i : Fin 7) (j : Fin 10) : Bool := decide
  (a.s = 12/5 + (i.val : ℚ)/10 ∧ a.s0 = 16/5 + (j.val : ℚ)/5 ∧
    a.effectiveBase ≤ (rows (slotOfAction (.inl (i,j)))).base)

private def someBaseFits (a : SourceW1) : Bool :=
  (List.finRange 7).any fun i => (List.finRange 10).any fun j => baseFits a i j

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Exact coefficient comparisons only. These guards read the two actual
base phases and 70 comparison integers. They do not iterate any table. -/
private theorem both_phases_fitted :
    w1Original.all someBaseFits = true ∧ w1Retained.all someBaseFits = true := by decide

private theorem fits_unique {a : SourceW1} {i i' : Fin 7} {j j' : Fin 10}
    (hs : a.s = 12/5+(i.val:ℚ)/10) (hs' : a.s = 12/5+(i'.val:ℚ)/10)
    (hS : a.s0 = 16/5+(j.val:ℚ)/5) (hS' : a.s0 = 16/5+(j'.val:ℚ)/5) :
    i=i' ∧ j=j' := by
  constructor
  · apply Fin.ext
    exact_mod_cast (show (i.val:ℚ) = i'.val by linarith only [hs,hs'])
  · apply Fin.ext
    exact_mod_cast (show (j.val:ℚ) = j'.val by linarith only [hS,hS'])

theorem historical_base_le_bound (g : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule g)
    (i : Fin 7) (j : Fin 10) (hs : a.s = 12/5 + (i.val : ℚ)/10)
    (hS : a.s0 = 16/5 + (j.val : ℚ)/5) :
    (a.effectiveBase : ℝ)/tableQ ≤ baseValue (.inl (i,j)) := by
  have hh : (sourceW1Schedule g).all someBaseFits = true := by
    unfold sourceW1Schedule
    split <;> first | exact both_phases_fitted.1 | exact both_phases_fitted.2
  obtain ⟨i',_,hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp hh a ha)
  obtain ⟨j',_,hj⟩ := List.any_eq_true.mp hi
  obtain ⟨hs',hS',hb⟩ := of_decide_eq_true hj
  obtain ⟨rfl,rfl⟩ := fits_unique hs hs' hS hS'
  unfold baseValue
  rw [show (tableQ : ℝ) = (2^80 : ℝ) by norm_num [tableQ]]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hb) (by positivity)

/-- All 70 historical bases pay the actual W1 integral at the original
physical ratio, with the paper's safe upper constant K*. -/
theorem historical_base_true_integral (g : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule g)
    (i : Fin 7) (j : Fin 10) (hs : a.s = 12/5 + (i.val : ℚ)/10)
    (hS : a.s0 = 16/5 + (j.val : ℚ)/5) {α : ℝ} (hα : 2 ≤ α) :
    (a.effectiveBase : ℝ)/tableQ + (tableK : ℝ)*switchedIntegral i j α/8 ≤ ordinaryBase i j :=
  (add_le_add_right (historical_base_le_bound g ha i j hs hS) _).trans
    (all70_archived_base_vs_true_integral i j hα)

/-- Both rounds of W1 integer rounding, the literal historical point and
coefficients, and the true analytic integral occur in the same invoice. -/
theorem historical_w1_candidate_true_base (g : ℕ) {a : SourceW1} (ha : a ∈ sourceW1Schedule g)
    {α : ℝ} (hα : 2 ≤ α) :
    ∃ i : Fin 7, ∃ j : Fin 10,
      a.s = 12/5 + (i.val : ℚ)/10 ∧ a.s0 = 16/5 + (j.val : ℚ)/5 ∧
      (sourceW1Value (outputAt g) a : ℝ)/tableQ + (tableK : ℝ)*switchedIntegral i j α/8 ≤
        ordinaryBase i j + (outputAt g true a.pointIndex : ℝ)/tableQ +
          w1Feedback i j (outputAt g false) := by
  obtain ⟨i,j,hs,hS,hcandidate⟩ := w1_candidate_le_old_profile g ha
  have hbase := historical_base_true_integral g ha i j hs hS hα
  exact ⟨i,j,hs,hS,by linarith only [hcandidate,hbase]⟩

/-- Transfer the historical base to the actual same-Q rough product
count. The unchanged additive-prime discrepancy remains explicit. -/
theorem historical_w1_actual_switched_price {η A ε : ℝ} (hη : 0<η) (hA : η≤A) (he : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → ∀ (Q L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10),
      L∈Icc η A → 0<d → Q=(d:ℝ)*(N:ℝ)^L → 2≤trueAlpha N Q d →
      ∀ (g : ℕ) (a : SourceW1), a∈sourceW1Schedule g →
      a.s=12/5+(i.val:ℚ)/10 → a.s0=16/5+(j.val:ℚ)/5 →
      ((rawTripleCount N d (d*N) (receiver N) (cutoff Q d (W1Anchor j))
        (cutoff Q d (W1Target i)):ℝ)/2 -
        (ordinaryBase i j - (a.effectiveBase : ℝ)/tableQ)*thetaAtom N Q d ≤
        primeDebt N Q d i j + ε*thetaAtom N Q d := by
  obtain ⟨T,hT,h⟩ := all70_true_converted_base hη hA he
  refine ⟨T,hT,?_⟩
  intro N hN Q L d i j hL hd hQ hα g a ha hs hS
  have hθ := thetaAtom_nonneg (hT.trans hN) hd
    (sameQ_residual_gt_one (by omega : 2≤N) hd (hη.trans_le hL.1) hQ)
  have hm := mul_le_mul_of_nonneg_right (historical_base_le_bound g ha i j hs hS) hθ
  have hb := h N hN Q L d i j hL hd hQ hα
  unfold switchedDebt at hb
  linarith only [hm,hb]

end
end ImbalancedChen.P2HistoricalW1RealBase
