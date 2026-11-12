import ImbalancedChen.Part5OriginalH430SeedSevenOrdinaryAP
import ImbalancedChen.Part5OriginalH430SeedPurifiedPrimeFibres

/-! The precise remaining switched distribution call at the adopted seed.
The numerator restores the additive prime on the same ordinary rough
integers whose untested masses furnish the priced Γ5/Γ9–21 denominator.
Local old-prefix repetitions and target-divisor centres have been paid
while the output is still prime. The coefficient is the original K/4. -/
namespace ImbalancedChen.Part5OriginalH430SeedSameCarrierPP
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2EnhancedBadGamma5CostTheta (convertedBad)
open P2EnhancedShortWordInclusiveMass (convertedOrdinary)
open P2EnhancedExactExceptionTheta (weightedErrors localErrors exact_errors_theta_payment)
open P2OriginalW2CentreThetaPayment (weighted_fiber_sum groupedSigma)
open P2OriginalPositiveSameQMassLift (sameQ_residual_gt_one)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OriginalRootQBound
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430SeedConvertedMass (converted)
open Part5OriginalH430SeedHistoryMass Part5OriginalH430SeedPurifiedPrimeFibres
open Part5OriginalH430SeedThirteenPrimeWords (restrictedPrime)
open Part5OriginalH430SeedMarkedPositiveAP (switchDifference pairCredit)
open Part5OriginalH430SelectedOrdinaryPairCounts (trueAt)
open Part5OriginalH430SeedRosserCountCredit (credit)
open Part5OriginalH430SeedFourMarkedRounds (originalRound)
open Part5OriginalH430SeedSevenPhysicalWindows (physicalFeedback)
open Part5OriginalH430SeedSevenOrdinaryAP (ordinaryAP original_seed_and_four_rounds_at_seven_AP)
open scoped Classical BigOperators

private theorem sum_colour_words (D : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → List ℕ → ℝ)
    (xs : List (List ℕ)) :
    (xs.map (fun cs => ∑ d∈D,w d*F d cs)).sum=∑ d∈D,w d*(xs.map (F d)).sum := by
  induction xs with
  | nil => simp
  | cons c xs ih => simp only [List.map_cons,List.sum_cons,ih,mul_add,sum_add_distrib]

theorem converted_eq_untested (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) :
    converted N Q D σ=∑ d∈D,σ d*(thetaConversion N d*switchedFibre false N Q d) := by
  let w := fun d => σ d*thetaConversion N d
  let F := fun d => wordFibre false N Q d
  have hs : (∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map
        (convertedOrdinary N Q D σ)).sum) =
      ∑ d∈D,w d*∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map (F d)).sum := by
    calc
      _ = ∑ j : Fin 13,∑ d∈D,w d*((secondFunctionalMotherGammaWords (9+j.val)).map (F d)).sum := by
        apply sum_congr rfl
        intro j _
        change ((secondFunctionalMotherGammaWords (9+j.val)).map
          (fun cs => ∑ d∈D,σ d*thetaConversion N d*
            P2EnhancedReceiverRoughPurification.ordinaryWordMass N Q d cs)).sum=_
        simp_rw [←raw_word]
        exact sum_colour_words D w F (secondFunctionalMotherGammaWords (9+j.val))
      _ = ∑ d∈D,∑ j : Fin 13,w d*((secondFunctionalMotherGammaWords (9+j.val)).map (F d)).sum := sum_comm
      _ = _ := by apply sum_congr rfl; intro d _; rw [mul_sum]
  unfold converted convertedBad
  rw [hs,←sum_add_distrib]
  apply sum_congr rfl
  intro d _
  dsimp only [w,F,switchedFibre]
  rw [raw_bad]
  ring

/-- Marking is done outside all word lists. The same occurrence uses the
same d, Q and multiplier in the tested and untested halves. -/
def switchedPPBalance {N n p dep : ℕ} {r : Root} {t : ℝ}
    (B : Finset (LevelIndex N n r t p dep)) : ℝ :=
  let Q := rootQ N n r t p
  ∑ l∈B,levelMark l*(switchedFibre true N Q (wordProduct l)-
    (K/4)*thetaConversion N (wordProduct l)*switchedFibre false N Q (wordProduct l))

theorem purify_on_original_marks {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (r : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N r →
      ∀ B : Finset (LevelIndex N n r t p dep),
      switchDifference B≤switchedPPBalance B+ε*markedTheta B := by
  obtain ⟨T,h4,ht⟩ := exact_errors_theta_payment frozenLeafCutoffFloor_pos he
  refine ⟨T,h4,?_⟩
  intro N hN hEven n r t p dep htau htau' hn hp B
  have hN4 := h4.trans hN
  let Q := rootQ N n r t p; let D := B.image wordProduct; let σ := groupedSigma B wordProduct levelMark
  have fields (d : ℕ) (h : d∈D) : 0<d ∧ 1<Q/(d:ℝ) ∧
      (∀ q∈d.primeFactors,(N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ)) ∧
      (N:ℝ)^frozenLeafCutoffFloor≤cutoff Q d (227/50) := by
    obtain ⟨l,_,rfl⟩ := mem_image.mp h
    obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) htau htau' hn hp l
    exact ⟨hd,sameQ_residual_gt_one (by omega) hd (frozenResidualFloor_pos.trans_le hL.1) hQ,
      (history_integer_roughness (by omega : 2≤N) htau htau' hn hp (levelOccurrence_source l).1).2.2⟩
  have herror := ht N hN hEven Q D σ (original_root_Q_le_target N n r t p (by omega) htau htau' hp)
    (fun d h => (fields d h).1) (fun _ _ => sum_nonneg (fun l _ => (mark_pos (levelOccurrence l)).le))
    (fun d h => (fields d h).2.1) (fun d h => (fields d h).2.2.1) (fun d h => (fields d h).2.2.2)
  change (∑ d∈B.image wordProduct,groupedSigma B wordProduct levelMark d*localErrors N Q d)≤
    ε*_ at herror
  rw [weighted_fiber_sum,real_word_theta] at herror
  have htotal := sum_le_sum (s:=B) (fun l hl => mul_le_mul_of_nonneg_left
    (restricted_prime_purified Q hN4 hEven (fields (wordProduct l) (mem_image_of_mem _ hl)).1)
    (mark_pos (levelOccurrence l)).le)
  simp only [mul_add,sum_add_distrib] at htotal
  have hprice : (K/4)*markedConverted B=∑ l∈B,levelMark l*
      ((K/4)*thetaConversion N (wordProduct l)*switchedFibre false N Q (wordProduct l)) := by
    unfold markedConverted
    rw [converted_eq_untested,weighted_fiber_sum,mul_sum]
    apply sum_congr rfl
    intro l _
    ring
  unfold switchDifference switchedPPBalance
  dsimp only
  rw [hprice]
  simp only [mul_sub,sum_sub_distrib]
  linarith only [htotal,herror]

theorem actual_seed_and_four_rounds_at_common_prime_restriction {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (r : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N r →
      let Q := rootQ N n r t p; let S := seedPositions N n r t p
      let D := S.image wordProduct; let σ := groupedSigma S wordProduct levelMark
      let C := ∑ l∈S,levelMark l*trueAt l
      0≤credit N Q D σ ∧ 0≤pairCredit S ∧
        (5*(C-(1-1/50:ℝ)*markedTheta S)+credit N Q D σ+pairCredit S ≤
          ordinaryAP S+switchedPPBalance S+ε*markedTheta S) ∧
        (∀ j : Fin 4,5*(C-(1-originalRound j.succ)*markedTheta S)+credit N Q D σ+pairCredit S ≤
          ordinaryAP S+switchedPPBalance S+5*originalRound j.castSucc*
            (∑ l∈S,levelMark l*physicalFeedback N Q (wordLevel l) (wordProduct l))+ε*markedTheta S) := by
  obtain ⟨Ta,h4,ha⟩ := original_seed_and_four_rounds_at_seven_AP (half_pos he)
  obtain ⟨Tb,_,hb⟩ := purify_on_original_marks (half_pos he)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n r t p ht ht' hn hp
  obtain ⟨hnc,hpc,hstart,hround⟩ := ha N ((le_max_left Ta Tb).trans hN) hEven n r t p ht ht' hn hp
  have hs := hb N ((le_max_right Ta Tb).trans hN) hEven n r t p 0 ht ht' hn hp (seedPositions N n r t p)
  refine ⟨hnc,hpc,?_,?_⟩
  · dsimp only at hstart hs ⊢
    linarith only [hstart,hs]
  · intro j
    have hj := hround j
    dsimp only at hj hs ⊢
    linarith only [hj,hs]

end
end ImbalancedChen.Part5OriginalH430SeedSameCarrierPP
