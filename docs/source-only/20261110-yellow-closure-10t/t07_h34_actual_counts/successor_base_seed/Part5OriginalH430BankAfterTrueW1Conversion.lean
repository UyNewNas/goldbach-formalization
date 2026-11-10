import ImbalancedChen.Part5OriginalH430AllBankSignedCounts
import ImbalancedChen.Part5OriginalH430W1TrueConvertedBase

/-! The same complete 106-row marked arithmetic count terminal after the
original 70 positive switched bases are charged to true integer families. -/
namespace ImbalancedChen.Part5OriginalH430BankAfterTrueW1Conversion
noncomputable section
open Finset
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2OriginalChildPhysicalNormalization (thetaAtom)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger (selectedBankRoundingLoss)
open Part5OriginalH430ActualSelectedRowBudget (actualBankTheta)
open Part5OriginalH430SeedHistoryMass Part5OriginalH430AllBankSignedCounts
open Part5OriginalH430W1TrueConvertedBase (primeDebt all70_true_converted_base)
open scoped Classical BigOperators

def remaining (N : ℕ) (Q L : ℝ) (d : ℕ) (g : Fin 430) : Original106Action → ℝ
  | .inl (i,j) => Part5OriginalH430W1SignedOrdinaryBase.fixedDebt N Q d i j g+
      Part5OriginalH430W1SignedOrdinaryBase.lowerDebt N Q L d i j g/2+primeDebt N Q d i j
  | .inr j => Part5OriginalH430W2SignedOrdinaryBase.rowDebt N Q L d j g

theorem full_bank_after_true_W1_conversion {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (root : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N root →
      ∀ g : Fin 430,
        (∑ a : Original106Action, ∑ l∈selectedLevel N n root t p g a,
          levelMark l*physicalDefect l)+selectedBankRoundingLoss N n root t p g ≤
        (∑ a : Original106Action, ∑ l∈selectedLevel N n root t p g a,
          levelMark l*remaining N (rootQ N n root t p) (wordLevel l) (wordProduct l) g a)+
          ε*actualBankTheta N n root t p g := by
  have hF : frozenResidualFloor≤1 := by
    unfold frozenResidualFloor
    have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])
  obtain ⟨Ta,hTa,ha⟩ := all_106_signed_count_bases (half_pos he)
  obtain ⟨Tb,hTb,hb⟩ := all70_true_converted_base frozenResidualFloor_pos hF (half_pos he)
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hN hEven n root t p ht ht' hn hp g
  have hNa := (le_max_left _ _).trans hN
  have hNb := (le_max_right _ _).trans hN
  have h4 := hTa.trans hNa
  let Q := rootQ N n root t p
  let S := selectedLevel N n root t p g
  have hu := ha N hNa hEven n root t p ht ht' hn hp g
  have hr : (∑ a : Original106Action,∑ l∈S a,levelMark l*debt N Q (wordLevel l) (wordProduct l) g a) ≤
      (∑ a : Original106Action,∑ l∈S a,levelMark l*remaining N Q (wordLevel l) (wordProduct l) g a)+
        ε/2*actualBankTheta N n root t p g := by
    unfold actualBankTheta
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro a _
    unfold levelTheta
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro l hl
    obtain ⟨hd,hL,hQ,_,hα⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
    have hmark := (mark_pos (levelOccurrence l)).le
    have hphys := P2OriginalPositiveSameQMassLift.thetaAtom_nonneg h4 hd
      (P2OriginalPositiveSameQMassLift.sameQ_residual_gt_one (by omega) hd
        (frozenResidualFloor_pos.trans_le hL.1) hQ)
    rcases a with ⟨i,j⟩ | j
    · have h := hb N hNb Q (wordLevel l) (wordProduct l) i j hL hd hQ hα
      dsimp only [debt,remaining]
      change levelMark l*(_+_+_)≤levelMark l*(_+_+_)+ε/2*(levelMark l*thetaAtom N Q (wordProduct l))
      linarith only [mul_le_mul_of_nonneg_left h hmark]
    · dsimp only [debt,remaining]
      exact le_add_of_nonneg_right (mul_nonneg (half_pos he).le (mul_nonneg hmark hphys))
  dsimp only [S,Q] at hr
  linarith only [hu,hr]

end
end ImbalancedChen.Part5OriginalH430BankAfterTrueW1Conversion
