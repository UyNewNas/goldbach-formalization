import ImbalancedChen.Part5OriginalH430SeedSevenPhysicalWindows
import ImbalancedChen.Part5OriginalH430SignedSeedCount

/-! Four source-specified rounds. Both the original safe ordinary coefficient
and the original seven-function feedback coefficient are paid by actual
marked masses. The right side displays the predecessor count obligations. -/
namespace ImbalancedChen.Part5OriginalH430SeedFourMarkedRounds
noncomputable section
open Set Finset
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift P2OriginalCompactThetaMass
open P2OriginalW2CentreThetaPayment (groupedSigma)
open P2EnhancedSeedActualFeedbackAssembly (lambda)
open P2SeedFeedbackOriginalNumerical (actual_lambda_gt_thirteen_hundredths)
open P2SeedOmegaOriginalNumerical (actualJ2omega_gt_safe_base)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430SeedPairFeedbackMass (prime_pair_feedback pairMass)
open Part5OriginalH430SeedSingletonFeedbackMass (prime_singleton_feedback singleMass)
open Part5OriginalH430SeedSevenPhysicalWindows Part5OriginalH430SignedSeedCount
open Part5OriginalH430SelectedOrdinaryPairCounts (trueAt)
open scoped Classical BigOperators

def originalRound (r : Fin 5) : ℝ :=
  ![1/50,22849/1000000,2321937/100000000,232675181/10000000000,23273777353/1000000000000] r

theorem previous_round (r : Fin 4) :
    0<originalRound r.castSucc ∧ originalRound r.succ=
      20249/1000000+(13/100)*originalRound r.castSucc := by
  fin_cases r <;> norm_num [originalRound]

theorem fourth_surplus : originalRound 4 - 2327/100000 = 3777353/1000000000000 := by
  norm_num [originalRound]

private theorem floor_upper : frozenResidualFloor≤1 := by
  unfold frozenResidualFloor
  have h : (1:ℝ)≤101^440 := one_le_pow₀ (by norm_num)
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h])

/-- Strict scalar slack in the 4096-cell certificate absorbs the actual
prime-quadrature errors in all seven physical windows at a single target
threshold valid for every positive subfamily of original histories. -/
theorem seven_actual_on_marks :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ B : Finset (LevelIndex N n k t p dep),
        (13/100:ℝ)*markedTheta B ≤
          ∑ l∈B,levelMark l*physicalFeedback N (rootQ N n k t p) (wordLevel l) (wordProduct l) := by
  let e := (lambda-13/100)/2
  have he : 0<e := half_pos (sub_pos.mpr actual_lambda_gt_thirteen_hundredths)
  choose Ts hs using (fun j => prime_singleton_feedback frozenResidualFloor_pos floor_upper he j)
  choose Tp hp' using (fun j => prime_pair_feedback frozenResidualFloor_pos floor_upper he j)
  obtain ⟨Ta,ha⟩ := compact_multiplier_error (k:=1) frozenResidualFloor_pos floor_upper
    (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)<1)
  let T := max 4 (max Ta (max (univ.sup Ts) (univ.sup Tp)))
  refine ⟨T,le_max_left _ _,?_⟩
  intro N hN n k t p dep ht ht' hn hp B
  have h4 : 4≤N := (le_max_left _ _).trans hN
  have hA := (le_max_left Ta _).trans ((le_max_right 4 _).trans hN)
  have hsup : max (univ.sup Ts) (univ.sup Tp)≤N :=
    (le_max_right Ta _).trans ((le_max_right 4 _).trans hN)
  unfold markedTheta
  rw [mul_sum]
  apply sum_le_sum
  intro l hl
  let L := wordLevel l
  let Q := rootQ N n k t p
  let d := wordProduct l
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
  have hL' := frozenResidualFloor_pos.trans_le hL.1
  have hθ := thetaAtom_nonneg h4 hd (sameQ_residual_gt_one (by omega) hd hL' hQ)
  have hAs := (ha N hA L hL).1
  have hsingle (j : Fin 3) := (abs_lt.mp (hs j N ((le_sup (mem_univ j)).trans
    ((le_max_left _ _).trans hsup)) L hL d)).1
  have hpair (j : Fin 4) := (abs_lt.mp (hp' j N ((le_sup (mem_univ j)).trans
    ((le_max_right _ _).trans hsup)) L hL d)).1
  have hlim : (13/100:ℝ) ≤ ((∑ j : Fin 3,singleMass N L d j)+(∑ j : Fin 4,pairMass N L d j))/5 := by
    have hgap := actual_lambda_gt_thirteen_hundredths
    rw [Fin.sum_univ_three,Fin.sum_univ_four]
    dsimp only [e,lambda] at hsingle hpair hgap
    linarith only [hsingle 0,hsingle 1,hsingle 2,hpair 0,hpair 1,hpair 2,hpair 3,hgap]
  have hfin : (13/100:ℝ)*thetaAtom N Q d ≤ physicalFeedback N Q L d := by
    unfold physicalFeedback
    simp_rw [physical_single_eq (by omega : 1<N) hd hL' hAs hQ,
      physical_pair_eq (by omega : 1<N) hd hL' hAs hQ]
    rw [←mul_sum,←mul_sum]
    nlinarith only [mul_le_mul_of_nonneg_right hlim hθ]
  nlinarith only [mul_le_mul_of_nonneg_left hfin (mark_pos (levelOccurrence l)).le]

/-- Marked count debt at each of the four literal output values. The seven
positive terms strengthen the required lower bounds on the prior singleton
counts and the prior upper bounds on the good pair counts. -/
theorem four_physical_round_count_debts {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ r : Fin 4,let Q := rootQ N n k t p
        let B := seedPositions N n k t p
        let D := B.image wordProduct
        let σ := groupedSigma B wordProduct levelMark
        5*((∑ l∈B,levelMark l*trueAt l)-(1-originalRound r.succ)*markedTheta B) ≤
          signedAnchors N Q D σ+signedSingles N Q D σ+signedPositive N Q D σ+
          5*originalRound r.castSucc*(∑ l∈B,levelMark l*physicalFeedback N Q (wordLevel l) (wordProduct l))+
          ε*markedTheta B := by
  obtain ⟨Ta,hTa,ha⟩ := seed_source_debt_below_base he actualJ2omega_gt_safe_base
  obtain ⟨Tb,hTb,hb⟩ := seven_actual_on_marks
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hN hEven n k t p ht ht' hn hp r
  have hu := ha N ((le_max_left _ _).trans hN) hEven n k t p ht ht' hn hp
  dsimp only at hu ⊢
  have hc := hb N ((le_max_right _ _).trans hN) n k t p 0 ht ht' hn hp (seedPositions N n k t p)
  have hpos := (previous_round r).1
  have hscaled := mul_le_mul_of_nonneg_left hc hpos.le
  rw [(previous_round r).2]
  linarith only [hu,hscaled]

end
end ImbalancedChen.Part5OriginalH430SeedFourMarkedRounds
