import ImbalancedChen.Part5OriginalH430SeedMarkedPositiveAP

/-! All seven ordinary seed windows at their actual signed AP. The
restricted positive source is the original bad Γ5 prime count and all
Γ9–21 prime-tested words, compared with their same-Q converted integer
mass. Both physical Rosser excesses stay on the count side. -/
namespace ImbalancedChen.Part5OriginalH430SeedSevenOrdinaryAP
noncomputable section
open Finset
open P2EnhancedNegativeChildModulusPrimePayment (piCenteredPhysicalError)
open P2OriginalW2CentreThetaPayment (groupedSigma)
open P2OriginalPositiveSameQMassLift (sameQ_residual_gt_one)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SeedHistoryMass
open Part5OriginalH430SelectedOrdinaryPairCounts (trueAt)
open Part5OriginalH430SeedRosserCountCredit (credit credit_nonneg)
open Part5OriginalH430SeedUpperAnchorsAP (anchorAP)
open Part5OriginalH430SeedFourMarkedRounds (originalRound)
open Part5OriginalH430SeedSevenPhysicalWindows (physicalFeedback)
open Part5OriginalH430SeedAtSignedAP (residue initial_and_four_rounds_at_signed_AP)
open Part5OriginalH430SeedMarkedPositiveAP
open scoped Classical BigOperators

def ordinaryAP {N n p dep : ℕ} {r : Root} {t : ℝ} (B : Finset (LevelIndex N n r t p dep)) : ℝ :=
  let Q := rootQ N n r t p; let D := B.image wordProduct; let σ := groupedSigma B wordProduct levelMark
  anchorAP N Q D σ-piCenteredPhysicalError N Q D σ+pairAP B

theorem original_seed_and_four_rounds_at_seven_AP {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (r : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N r →
      let Q := rootQ N n r t p; let S := seedPositions N n r t p
      let D := S.image wordProduct; let σ := groupedSigma S wordProduct levelMark
      let C := ∑ l∈S,levelMark l*trueAt l
      0≤credit N Q D σ ∧ 0≤pairCredit S ∧
        (5*(C-(1-1/50:ℝ)*markedTheta S)+credit N Q D σ+pairCredit S ≤
          ordinaryAP S+switchDifference S+ε*markedTheta S) ∧
        (∀ j : Fin 4,5*(C-(1-originalRound j.succ)*markedTheta S)+credit N Q D σ+pairCredit S ≤
          ordinaryAP S+switchDifference S+5*originalRound j.castSucc*
            (∑ l∈S,levelMark l*physicalFeedback N Q (wordLevel l) (wordProduct l))+ε*markedTheta S) := by
  obtain ⟨Ta,h4,ha⟩ := initial_and_four_rounds_at_signed_AP (half_pos he)
  obtain ⟨Tb,_,hb⟩ := marked_positive_at_actual_AP (half_pos he)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n r t p ht ht' hn hp
  have hNa := (le_max_left Ta Tb).trans hN
  have hN4 := h4.trans hNa
  let S := seedPositions N n r t p; let Q := rootQ N n r t p
  let D := S.image wordProduct; let σ := groupedSigma S wordProduct levelMark
  have fields (d : ℕ) (hd : d∈D) : 0<d ∧ 1<Q/(d:ℝ) := by
    obtain ⟨l,_,rfl⟩ := mem_image.mp hd
    obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
    exact ⟨hd,sameQ_residual_gt_one (by omega) hd (frozenResidualFloor_pos.trans_le hL.1) hQ⟩
  have hcredit : 0≤credit N Q D σ := credit_nonneg (fun d hd => (fields d hd).1)
    (fun _ _ => sum_nonneg (fun l _ => (mark_pos (levelOccurrence l)).le)) (fun d hd => (fields d hd).2)
  obtain ⟨hinit,hround⟩ := ha N hNa hEven n r t p ht ht' hn hp
  obtain ⟨hpair,hnew⟩ := hb N ((le_max_right Ta Tb).trans hN) hEven n r t p 0 ht ht' hn hp S
  refine ⟨hcredit,hpair,?_,?_⟩
  · dsimp only at hinit hnew ⊢
    unfold residue at hinit
    unfold ordinaryAP
    dsimp only at *
    linarith only [hinit,hnew]
  · intro j
    have h := hround j
    dsimp only at h hnew ⊢
    unfold residue at h
    unfold ordinaryAP
    dsimp only at *
    linarith only [h,hnew]

end
end ImbalancedChen.Part5OriginalH430SeedSevenOrdinaryAP
