import ImbalancedChen.Part5OriginalH430PairOrdinaryCountPayment
import ImbalancedChen.Part5OriginalH430BankAfterW1PrimeRestriction

/-! All 106 original winners after the 144 ordered pair baseline payments.
The positive excess of the actual upper polynomials accompanies the
original Q80 charge on the left of the signed inequality. -/
namespace ImbalancedChen.Part5OriginalH430BankAfterPairRosser
noncomputable section
open Finset
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift (sameQ_residual_gt_one thetaAtom_nonneg)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger (selectedBankRoundingLoss)
open Part5OriginalH430ActualSelectedRowBudget (actualBankTheta)
open Part5OriginalH430SeedHistoryMass Part5OriginalH430AllBankSignedCounts (physicalDefect)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430OrdinaryPairCounts (childDiscrepancy)
open Part5OriginalH430BankAfterW1PrimeRestriction (finalDebt full_bank_after_W1_prime_restriction)
open Part5OriginalH430PairOrdinaryCountPayment (laneExcess laneAP oldHMass all_good_pair_count_means)
open scoped Classical BigOperators

def afterPairs (N : ℕ) (Q L : ℝ) (d : ℕ) (g : Fin 430) : Original106Action → ℝ
  | .inl ij => finalDebt N Q L d g (.inl ij)
  | .inr j => Part5OriginalH430W2SignedOrdinaryBase.fixedDebt N Q d j g+
      (∑ k : Fin 3,Part5OriginalH430W2SignedSingletons.lowerDebt N Q L d j k g)/5+
      (∑ k : Fin 4,(laneAP N Q L d j k+oldHMass N Q L d j k g))/5+
        Part5OriginalH430W2SignedOrdinaryBase.switchedDebt N Q d j

def rowExcess (N : ℕ) (Q L : ℝ) (d : ℕ) : Original106Action → ℝ
  | .inl _ => 0
  | .inr j => (∑ k : Fin 4,laneExcess N Q L d j k)/5

def markedPairExcess (N n : ℕ) (r : Root) (t : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,∑ l∈selectedLevel N n r t p g a,
    levelMark l*rowExcess N (rootQ N n r t p) (wordLevel l) (wordProduct l) a

theorem all106_after_pair_Rosser {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (r : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N r → ∀ g : Fin 430,
      0≤markedPairExcess N n r t p g ∧
      (∑ a : Original106Action,∑ l∈selectedLevel N n r t p g a,levelMark l*physicalDefect l)+
          selectedBankRoundingLoss N n r t p g+markedPairExcess N n r t p g ≤
        (∑ a : Original106Action,∑ l∈selectedLevel N n r t p g a,levelMark l*
          afterPairs N (rootQ N n r t p) (wordLevel l) (wordProduct l) g a)+ε*actualBankTheta N n r t p g := by
  obtain ⟨Ta,h4,ha⟩ := full_bank_after_W1_prime_restriction (half_pos he)
  obtain ⟨Tb,_,hb⟩ := all_good_pair_count_means (half_pos he)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n r t p ht ht' hn hp g
  have hNa := (le_max_left Ta Tb).trans hN
  have hNb := (le_max_right Ta Tb).trans hN
  have hN4 := h4.trans hNa
  let S := selectedLevel N n r t p g
  let Q := rootQ N n r t p
  have hprior := ha N hNa hEven n r t p ht ht' hn hp g
  have hnew := hb N hNb hEven n r t p (g.val+1) ht ht' hn hp
  have point (a : Original106Action) (l : Index N n r t p g) :
      let d := wordProduct l; let L := wordLevel l
      0≤rowExcess N Q L d a ∧
        finalDebt N Q L d g a+rowExcess N Q L d a≤afterPairs N Q L d g a+(ε/2)*thetaAtom N Q d := by
    let d := wordProduct l; let L := wordLevel l
    obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
    have hθ := thetaAtom_nonneg hN4 hd (sameQ_residual_gt_one (by omega) hd (frozenResidualFloor_pos.trans_le hL.1) hQ)
    have hεθ := mul_nonneg (half_pos he).le hθ
    rcases a with ij | j
    · exact ⟨le_rfl,by simpa only [afterPairs,rowExcess,add_zero] using
        (le_add_of_nonneg_right hεθ : finalDebt N Q L d g (.inl ij)≤_)⟩
    · have hsum := sum_le_sum (s:=univ) (fun k _ => (hnew l j k g).2)
      simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsum
      constructor
      · exact div_nonneg (sum_nonneg (fun k _ => (hnew l j k g).1)) (by norm_num)
      · dsimp only [finalDebt,rowExcess,afterPairs,Part5OriginalH430W2SignedOrdinaryBase.rowDebt]
        rw [sum_add_distrib]
        linarith only [hsum,hεθ]
  constructor
  · exact sum_nonneg (fun a _ => sum_nonneg (fun l _ => mul_nonneg (mark_pos (levelOccurrence l)).le (point a l).1))
  · have hs : (∑ a : Original106Action,∑ l∈S a,levelMark l*finalDebt N Q (wordLevel l) (wordProduct l) g a)+
        markedPairExcess N n r t p g ≤
          (∑ a : Original106Action,∑ l∈S a,levelMark l*afterPairs N Q (wordLevel l) (wordProduct l) g a)+
            ε/2*actualBankTheta N n r t p g := by
      unfold markedPairExcess actualBankTheta
      rw [←sum_add_distrib,mul_sum,←sum_add_distrib]
      apply sum_le_sum
      intro a _
      unfold levelTheta
      rw [←sum_add_distrib,mul_sum,←sum_add_distrib]
      apply sum_le_sum
      intro l _
      have hpnt := mul_le_mul_of_nonneg_left (point a l).2 (mark_pos (levelOccurrence l)).le
      simpa only [mul_add,mul_assoc,mul_left_comm,mul_comm,levelMark] using hpnt
    linarith only [hprior,hs]

end
end ImbalancedChen.Part5OriginalH430BankAfterPairRosser
