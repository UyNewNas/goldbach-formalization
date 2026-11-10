import ImbalancedChen.Part5OriginalH430OrdinaryPairCounts

/-! Read the preceding H on the very four mother occurrences that contain
the actual receiver counts. The finite enclosure here uses exact counts
for both sides of the old arithmetic state. -/
namespace ImbalancedChen.Part5OriginalH430SelectedOrdinaryPairCounts
noncomputable section
open Set Finset
open P5OriginalActionMassBound P2AllW1SameQRawCountInduction (PhysicalState)
open P2W2PhysicalChildFeedback P2OriginalW2ComplementAction P2OriginalW2CountTupleReindex
open P2FrozenReceiverCountActions P5OriginalU5FrozenSource (receiver)
open P2OriginalW2CentreThetaPayment P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalHalfOpenProfileCarrier (below_two_comparison)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430BankSlotTargets
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430HistoryQuotientCounts
open Part5OriginalH430OriginalRootQBound Part5OriginalH430SeedHistoryMass
open Part5OriginalH430OrdinaryPairCounts
open scoped Classical BigOperators

def actualState (N : ℕ) : PhysicalState :=
  let c := fun d z => (frozenCount N d (receiver N) z:ℝ)
  ⟨c,c⟩

def trueAt {N n p dep : ℕ} {root : Root} {t : ℝ}
    (l : LevelIndex N n root t p dep) : ℝ :=
  ((chenSiftedQuotientPrimeSource N (wordProduct l)
    (cutoff (rootQ N n root t p) (wordProduct l) (levelOccurrence l).current.node.physical.argument)).card:ℝ)

def retainedTerms (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (g : Fin 430) : ℝ :=
  4*(actualState N).upper d (cutoff Q d (originalW2At j).s0) +
    (actualState N).upper d (cutoff Q d (originalW2At j).phi1) +
    countRemainder N Q (actualState N) d (originalW2At j) +
    ∑ k : Fin 4, childDiscrepancy N Q L (actualState N) d j k g

def ordinaryPairCentre (j : Fin 36) (g : Fin 430) : ℝ :=
  ∑ k : Fin 4, ordinaryIntegral j k - archivedLane j k g

/-- Raw integer occurrences at each parent's own argument, with the legal
monotone comparison to the selected action and the true centre-charge bound.
This is one selected W2 row at a time, before summing the 106 disjoint slots. -/
theorem actual_selected_W2_count {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N → ∀ (n : ℕ) (root : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N root →
      ∀ (g : Fin 430) (j : Fin 36), let S := selectedLevel N n root t p g (.inr j)
      let Q := rootQ N n root t p
      5*(∑ l ∈ S, levelMark l*trueAt l) ≤
        (∑ l ∈ S, levelMark l*retainedTerms N Q (wordLevel l) (wordProduct l) j g) +
          markedTheta S*ordinaryPairCentre j g + ε*markedTheta S := by
  obtain ⟨Ta,hTa,ha⟩ := uniform_four_ordinary_cells (show 0<ε/8 by positivity)
  obtain ⟨Tb,hTb,hb⟩ := all36_charge_theta_payment frozenResidualFloor_pos (half_pos hε)
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hNT he n root t p ht ht' hn hp g j
  have hNa := (le_max_left Ta Tb).trans hNT
  have hNb := (le_max_right Ta Tb).trans hNT
  have hN4 := hTa.trans hNa
  have hN1 : 1<N := by omega
  let S := selectedLevel N n root t p g (.inr j)
  let Q := rootQ N n root t p
  have point (l : Index N n root t p g) (hl : l∈S) :
      5*trueAt l ≤ retainedTerms N Q (wordLevel l) (wordProduct l) j g +
        thetaAtom N Q (wordProduct l)*ordinaryPairCentre j g +
        (ε/2)*thetaAtom N Q (wordProduct l) + W2Charge N Q (wordProduct l) j := by
    let d := wordProduct l
    let L := wordLevel l
    obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
    have hR := P2OriginalPositiveSameQMassLift.sameQ_residual_gt_one hN1 hd
      (frozenResidualFloor_pos.trans_le hL.1) hQ
    have hs := rootHistory_support hN1 ht ht' hn (original_band_prime hp)
      (original_band_geometry (by omega) hp) (levelOccurrence_source l).1
    have hc := rootHistory_coherent hN1 ht ht' hn (original_band_prime hp)
      (original_band_geometry (by omega) hp) (levelOccurrence_source l).1
    obtain ⟨i,hi⟩ := (mem_filter.mp hl).2
    have htarget := (requested_bank_tests hc hi).2.1
    rw [action_slot] at htarget
    change (levelOccurrence l).current.node.physical.argument ≤ (originalW2At j).s at htarget
    have hleft : trueAt l ≤ (frozenCount N d (receiver N) (cutoff Q d (originalW2At j).s):ℝ) := by
      unfold trueAt
      rw [← history_frozen_count_eq_true_quotient (by omega : 2≤N) ht ht' hn hp
        (levelOccurrence_source l).1]
      exact_mod_cast below_two_comparison N d (receiver N) hR.le
        (zero_lt_one.trans_le hs.2.2.2.1.1) htarget
    have hfinite := W2Bound_upper N Q (receiver N) (actualState N) j hd hR
      (fun _ _ _ => ⟨le_rfl,le_rfl⟩)
    rw [W2Bound_eq_paid_add_charge,paidW2_eq_four_good_counts N Q _ d j hR.le] at hfinite
    have hpairs := sum_le_sum (s:=univ) (fun k _ =>
      ha N hNa n root t p (g.val+1) ht ht' hn hp l (actualState N) j k g)
    change (∑ k : Fin 4, sourceGoodOccurrence N Q (actualState N) d (originalW2At j) k) ≤
      ∑ k : Fin 4, (thetaAtom N Q d*(ordinaryIntegral j k-archivedLane j k g) +
        childDiscrepancy N Q L (actualState N) d j k g + (ε/8)*thetaAtom N Q d) at hpairs
    simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_ofNat] at hpairs
    dsimp only [retainedTerms,ordinaryPairCentre]
    linarith only [hleft,hfinite,hpairs]
  have total := sum_le_sum (s:=S) (fun l hl =>
    mul_le_mul_of_nonneg_left (point l hl) (mark_pos _).le)
  let D := S.image wordProduct
  let σ := groupedSigma S wordProduct levelMark
  have hgeom (d : ℕ) (hd : d∈D) : 0<d ∧ (N:ℝ)^frozenResidualFloor≤Q/d := by
    obtain ⟨l,_,rfl⟩ := mem_image.mp hd
    have h := scale_and_alpha (by omega : 2≤N) ht ht' hn hp l
    exact ⟨h.1,h.2.2.2.1⟩
  have hcharge := hb N hNb he Q D σ (original_root_Q_le_target N n root t p (by omega) ht ht' hp)
    (fun d hd => (hgeom d hd).1) (fun _ _ => sum_nonneg (fun l _ => (mark_pos _).le))
    (fun d hd => (hgeom d hd).2) j
  change (∑ d ∈ S.image wordProduct, groupedSigma S wordProduct levelMark d * W2Charge N Q d j) ≤
    (ε/2)*_ at hcharge
  rw [weighted_fiber_sum,real_word_theta] at hcharge
  simp only [mul_add,sum_add_distrib] at total
  have a (l : Index N n root t p g) : levelMark l*(5*trueAt l)=5*(levelMark l*trueAt l) := by ring
  have b (l : Index N n root t p g) : levelMark l*(thetaAtom N Q (wordProduct l)*ordinaryPairCentre j g) =
      (levelMark l*thetaAtom N Q (wordProduct l))*ordinaryPairCentre j g := by ring
  have c (l : Index N n root t p g) : levelMark l*((ε/2)*thetaAtom N Q (wordProduct l)) =
      (ε/2)*(levelMark l*thetaAtom N Q (wordProduct l)) := by ring
  simp_rw [a,b,c] at total
  simp only [← mul_sum,← sum_mul] at total
  change 5*(∑ l∈S,levelMark l*trueAt l) ≤ (∑ l∈S,levelMark l*retainedTerms N Q
      (wordLevel l) (wordProduct l) j g) + markedTheta S*ordinaryPairCentre j g +
      (ε/2)*markedTheta S + _ at total
  linarith only [total,hcharge]

end
end ImbalancedChen.Part5OriginalH430SelectedOrdinaryPairCounts
