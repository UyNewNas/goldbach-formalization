import ImbalancedChen.Part5OriginalH430SeedOrdinaryFourIntegral
import ImbalancedChen.Part5OriginalH430SeedThirteenPrimeWords
import ImbalancedChen.Part5OriginalH430SeedAtSignedAP

/-! Positive part of the signed seed inequality on the real history marks.
The four ordinary main terms cancel against the seed functional. Each
prime-restricted long colour word keeps its own multiplicity. -/
namespace ImbalancedChen.Part5OriginalH430SeedMarkedPositiveAP
noncomputable section
open Finset
open P5OriginalActionMassBound (originalW2At)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2EnhancedTwentyOneChildCorrection (localPositivePairs positivePairs)
open P2ActualSameQTwentyOnePositiveSourceBinding (actualLocalPrimeMass)
open P2SeedOmegaLiteralFibre (K)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalPositiveSameQMassLift (sameQ_residual_gt_one)
open P2OriginalW2CentreThetaPayment (groupedSigma weighted_fiber_sum all36_charge_theta_payment)
open P2OriginalW2ComplementAction (W2Charge)
open P2OriginalW2CountTupleReindex (sourceGoodOccurrence)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OriginalRootQBound
open Part5OriginalH430SeedHistoryMass Part5OriginalH430SignedSeedCount (signedPositive)
open Part5OriginalH430OrdinaryPairCounts (ordinaryIntegral)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430PairOrdinaryCountPayment (laneAP laneExcess all_good_pair_count_means)
open Part5OriginalH430GoodPairSourcesAtAP (actual_good_pair_to_original_integral)
open Part5OriginalH430SeedOrdinaryFourIntegral (seed_four_ordinary)
open Part5OriginalH430SeedThirteenPrimeWords (restrictedPrime mother_positive_split)
open scoped Classical BigOperators

def pairCredit {N n p dep : ℕ} {r : Root} {t : ℝ} (B : Finset (LevelIndex N n r t p dep)) : ℝ :=
  ∑ l∈B,levelMark l*∑ k : Fin 4,laneExcess N (rootQ N n r t p) (wordLevel l) (wordProduct l) 0 k

def pairAP {N n p dep : ℕ} {r : Root} {t : ℝ} (B : Finset (LevelIndex N n r t p dep)) : ℝ :=
  ∑ l∈B,levelMark l*∑ k : Fin 4,laneAP N (rootQ N n r t p) (wordLevel l) (wordProduct l) 0 k

def switchDifference {N n p dep : ℕ} {r : Root} {t : ℝ} (B : Finset (LevelIndex N n r t p dep)) : ℝ :=
  (∑ l∈B,levelMark l*restrictedPrime N (rootQ N n r t p) (wordProduct l))-(K/4)*markedConverted B

theorem marked_positive_at_actual_AP {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (r : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N r →
      ∀ B : Finset (LevelIndex N n r t p dep),
      let Q := rootQ N n r t p; let D := B.image wordProduct; let σ := groupedSigma B wordProduct levelMark
      0≤pairCredit B ∧ signedPositive N Q D σ+pairCredit B≤pairAP B+switchDifference B+ε*markedTheta B := by
  obtain ⟨Ta,h4,ha⟩ := actual_good_pair_to_original_integral (show 0<ε/8 by positivity)
  obtain ⟨Tb,_,hb⟩ := all36_charge_theta_payment frozenResidualFloor_pos (half_pos he)
  obtain ⟨Tc,_,hc⟩ := all_good_pair_count_means (show (0:ℝ)<1 by norm_num)
  refine ⟨max Ta (max Tb Tc),h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n r t p dep ht ht' hn hp B
  have hNa := (le_max_left Ta _).trans hN
  have htbc := (le_max_right Ta _).trans hN
  have hNb := (le_max_left Tb Tc).trans htbc
  have hN4 := h4.trans hNa
  let Q := rootQ N n r t p; let D := B.image wordProduct; let σ := groupedSigma B wordProduct levelMark
  have hcoef := hc N ((le_max_right Tb Tc).trans htbc) hEven n r t p dep ht ht' hn hp
  constructor
  · exact sum_nonneg (fun l _ => mul_nonneg (mark_pos (levelOccurrence l)).le
      (sum_nonneg (fun k _ => (hcoef l 0 k 0).1)))
  · let c := ∑ k : Fin 4,ordinaryIntegral 0 k
    have point (l : LevelIndex N n r t p dep) :
        let d := wordProduct l; let L := wordLevel l
        localPositivePairs N Q d+actualLocalPrimeMass N Q d+(∑ k : Fin 4,laneExcess N Q L d 0 k) ≤
          (∑ k : Fin 4,laneAP N Q L d 0 k)+restrictedPrime N Q d+c*thetaAtom N Q d+
            (ε/2)*thetaAtom N Q d+W2Charge N Q d 0 := by
      let d := wordProduct l
      obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
      have hR := sameQ_residual_gt_one (by omega : 1<N) hd (frozenResidualFloor_pos.trans_le hL.1) hQ
      have hbase := mother_positive_split hN4 hEven hd hR
      have hfour := sum_le_sum (s:=univ) (fun k _ => ha N hNa hEven n r t p dep ht ht' hn hp l 0 k)
      change (∑ k : Fin 4,(sourceGoodOccurrence N Q (actualState N) d (originalW2At 0) k+
        laneExcess N Q (wordLevel l) d 0 k)) ≤ ∑ k : Fin 4,(laneAP N Q (wordLevel l) d 0 k+
        thetaAtom N Q d*ordinaryIntegral 0 k+(ε/8)*thetaAtom N Q d) at hfour
      simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,←mul_sum] at hfour
      dsimp only
      dsimp only [c]
      linarith only [hbase,hfour]
    have hgeom (d : ℕ) (hd : d∈D) : 0<d ∧ (N:ℝ)^frozenResidualFloor≤Q/d := by
      obtain ⟨l,_,rfl⟩ := mem_image.mp hd
      have hl := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
      exact ⟨hl.1,hl.2.2.2.1⟩
    have hcharge := hb N hNb hEven Q D σ (original_root_Q_le_target N n r t p (by omega) ht ht' hp)
      (fun d h => (hgeom d h).1) (fun _ _ => sum_nonneg (fun l _ => (mark_pos (levelOccurrence l)).le))
      (fun d h => (hgeom d h).2) 0
    change (∑ d∈B.image wordProduct,groupedSigma B wordProduct levelMark d*W2Charge N Q d 0)≤
      (ε/2)*_ at hcharge
    rw [weighted_fiber_sum,real_word_theta] at hcharge
    have total := sum_le_sum (s:=B) (fun l _ => mul_le_mul_of_nonneg_left (point l) (mark_pos (levelOccurrence l)).le)
    dsimp only at total
    simp only [mul_add,sum_add_distrib] at total
    have mass (a : ℝ) : (∑ l∈B,levelMark l*(a*thetaAtom N Q (wordProduct l)))=a*markedTheta B := by
      unfold markedTheta
      rw [mul_sum]
      apply sum_congr rfl
      intro l _
      ring
    rw [mass c,mass (ε/2)] at total
    change signedPositive N Q (B.image wordProduct) (groupedSigma B wordProduct levelMark)+pairCredit B≤
      pairAP B+switchDifference B+ε*markedTheta B
    unfold signedPositive positivePairs pairCredit pairAP switchDifference markedConverted
    rw [weighted_fiber_sum,weighted_fiber_sum,real_word_theta,←seed_four_ordinary]
    dsimp only [c] at total
    linarith only [total,hcharge]

end
end ImbalancedChen.Part5OriginalH430SeedMarkedPositiveAP
