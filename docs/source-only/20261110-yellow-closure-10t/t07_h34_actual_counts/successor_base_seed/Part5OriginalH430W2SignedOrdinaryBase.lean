import ImbalancedChen.Part5OriginalH430W2SignedSingletons

/-! All ordinary terms of the 36 selected W2 inequalities with the original
4:1 fixed-channel weights, three negative old-h and four positive old-H
children. The bad pair and remaining positive mother words are explicit. -/
namespace ImbalancedChen.Part5OriginalH430W2SignedOrdinaryBase
noncomputable section
open Finset Wu2008DoubleSieve
open P5OriginalActionMassBound P2FrozenReceiverCountActions P5OriginalU5FrozenSource (receiver)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalW2CountTupleReindex P2OriginalW2ComplementAction P2OriginalW2MotherOccurrenceReindex
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2Selected430CausalOccurrenceExporter (iterate)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430BankSlotTargets Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430FixedReadDictionary Part5OriginalH430SelectedFixedReadSupply
open Part5OriginalH430ActualFeedbackQuotientRemainders Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430W2UpperBankPayment Part5OriginalH430W2UpperWeights
open Part5OriginalH430W2UpperArchiveData Part5OriginalH430W2ArchivedSingletons
open Part5OriginalH430W2UpperPolygons (original_parameters parameterQ physical)
open Part5OriginalH430SeedHistoryMass Part5OriginalH430OrdinaryPairCounts
open Part5OriginalH430SelectedOrdinaryPairCounts Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430W2SignedSingletons Part5OriginalUpsilon5CausalDictionary
open P5CanonicalUpperCancellation (upperA)
open scoped Classical BigOperators

def ordinaryBase (j : Fin 36) : ℝ :=
  let a := originalW2At j
  upperA a.s - (4*upperA a.s0+upperA a.phi1 -
    (∑ k : Fin 3,integral (.inr (j,k))) + ∑ k : Fin 4,ordinaryIntegral j k)/5

def fixedDebt (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) (g : Fin 430) : ℝ :=
  let a := originalW2At j
  (4*(actualState N).upper d (cutoff Q d a.s0)+(actualState N).upper d (cutoff Q d a.phi1))/5 -
    thetaAtom N Q d*((4*upperA a.s0+upperA a.phi1)/5-fixedValue (precedingH g) (.inr j))

def positive (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) : ℝ :=
  let a := originalW2At j
  let A := cutoff Q d a.s0
  let B := cutoff Q d a.phi1
  let C := cutoff Q d a.phi2
  let D := cutoff Q d a.phi3
  let Z := cutoff Q d a.s
  (∑ k : Fin 4,sourceRejectedOccurrence N Q d a k) + higherPaidSwitched N Q (actualState N) d A B C D Z +
    P2EnhancedTwentyOneQuotientFinite.collisionSwitched N d N A B C D Z +
    fourthRowMotherBadPrime N d A Z + fourthRowMotherBadPrime N d A C + fourthRowMotherBadPrime N d A D

def switchedDebt (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) : ℝ :=
  positive N Q d j/5-(ordinaryBase j-baseValue (.inr j))*thetaAtom N Q d

def rowDebt (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (g : Fin 430) : ℝ :=
  fixedDebt N Q d j g +
    (∑ k : Fin 3,lowerDebt N Q L d j k g)/5 +
    (∑ k : Fin 4,childDiscrepancy N Q L (actualState N) d j k g)/5 + switchedDebt N Q d j

private theorem remainder_exact (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) :
    countRemainder N Q (actualState N) d (originalW2At j) =
      positive N Q d j - ∑ k : Fin 3,negative N Q d j k := by
  simp only [countRemainder,positive,negative,stop,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,add_zero]
  ring

theorem upper_lanes_eq_archive (j : Fin 36) (g : Fin 430) :
    (∑ k : Fin 4,archivedLane j k g) = 5*archivedChannel (iterate g.val) j true := by
  rw [archive_upper_cells,mul_sum]
  unfold archivedLane
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [Int.cast_sum]
  simp only [←sum_mul,←sum_div]
  change (_ / (2^80:ℝ)) * floorValue (precedingH g) i =
    5*((_/(2^80:ℝ)/5)*floorValue (precedingH g) i)
  ring

theorem targets_le_three (j : Fin 36) : (originalW2At j).s≤3 := by
  rw [←original_parameters j]
  change (parameterQ j 0:ℝ)≤3
  fin_cases j <;> norm_num [parameterQ]

theorem selected_W2_signed_base {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ (g : Fin 430) (j : Fin 36), let S := selectedLevel N n k t p g (.inr j)
      let Q := rootQ N n k t p
      (∑ l∈S,levelMark l*(trueAt l - thetaAtom N Q (wordProduct l) *
        (upperA (levelOccurrence l).current.node.physical.argument - baseValue (.inr j) -
          fixedValue (precedingH g) (.inr j)-idealFeedbackValue (iterate g.val) (.inr j)))) ≤
        (∑ l∈S,levelMark l*rowDebt N Q (wordLevel l) (wordProduct l) j g) + ε*markedTheta S := by
  let e := 5*ε/2
  have hpos : 0<e := by dsimp [e]; positivity
  obtain ⟨Ta,hTa,ha⟩ := actual_selected_W2_count hpos
  obtain ⟨Tb,hTb,hb⟩ := all_W2_singles_signed hpos
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hN hEven n rt t p ht ht' hn hp g j
  have hNa := (le_max_left Ta Tb).trans hN
  have hNb := (le_max_right Ta Tb).trans hN
  have hN4 := hTa.trans hNa
  let S := selectedLevel N n rt t p g (.inr j)
  let Q := rootQ N n rt t p
  let θ := fun l : Index N n rt t p g => thetaAtom N Q (wordProduct l)
  let U := fun l : Index N n rt t p g => θ l*(upperA (levelOccurrence l).current.node.physical.argument -
    baseValue (.inr j)-fixedValue (precedingH g) (.inr j)-idealFeedbackValue (iterate g.val) (.inr j))
  let D := fun l : Index N n rt t p g => rowDebt N Q (wordLevel l) (wordProduct l) j g
  let R := fun l : Index N n rt t p g => retainedTerms N Q (wordLevel l) (wordProduct l) j g
  have hh := ha N hNa hEven n rt t p ht ht' hn hp g j
  change 5*(∑ l∈S,levelMark l*trueAt l) ≤ (∑ l∈S,levelMark l*R l) +
    markedTheta S*ordinaryPairCentre j g+e*markedTheta S at hh
  have point (l : Index N n rt t p g) (hl : l∈S) :
      R l+θ l*ordinaryPairCentre j g ≤ 5*(U l+D l)+e*θ l := by
    have hs := rootHistory_support (by omega : 1<N) ht ht' hn (original_band_prime hp)
      (original_band_geometry (by omega) hp) (levelOccurrence_source l).1
    have hc := rootHistory_coherent (by omega : 1<N) ht ht' hn (original_band_prime hp)
      (original_band_geometry (by omega) hp) (levelOccurrence_source l).1
    obtain ⟨u,hu⟩ := (mem_filter.mp hl).2
    have htar := (requested_bank_tests hc hu).2.1
    rw [action_slot] at htar
    change (levelOccurrence l).current.node.physical.argument ≤ (originalW2At j).s at htar
    have ht3 := targets_le_three j
    have h2 := (P2AllW2SameQRawCountAction.original_W2_order _ (originalW2At_mem j)).1
    have hA := P5CanonicalUpperCancellation.upperA_eq_one
      (zero_lt_one.trans_le hs.2.2.2.1.1) (htar.trans ht3)
    have hB := P5CanonicalUpperCancellation.upperA_eq_one (by linarith [h2]) ht3
    have hlo := hb N hNb n rt t p (g.val+1) ht ht' hn hp l g j
    dsimp only at hlo
    dsimp only [R,θ,U,D,retainedTerms,rowDebt,ordinaryPairCentre,fixedDebt,switchedDebt,ordinaryBase]
    rw [hA,hB,archived_w2_split,remainder_exact,sum_sub_distrib,upper_lanes_eq_archive]
    linarith only [hlo]
  have cleaned : (∑ l∈S,levelMark l*R l)+markedTheta S*ordinaryPairCentre j g ≤
      5*(∑ l∈S,levelMark l*U l)+5*(∑ l∈S,levelMark l*D l)+e*markedTheta S := by
    unfold markedTheta
    change (∑ l∈S,levelMark l*R l)+(∑ l∈S,levelMark l*θ l)*_ ≤
      5*(∑ l∈S,levelMark l*U l)+5*(∑ l∈S,levelMark l*D l)+e*(∑ l∈S,levelMark l*θ l)
    rw [sum_mul,mul_sum,mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro l hl
    nlinarith only [mul_le_mul_of_nonneg_left (point l hl) (mark_pos (levelOccurrence l)).le]
  change (∑ l∈S,levelMark l*(trueAt l-U l)) ≤ (∑ l∈S,levelMark l*D l)+ε*markedTheta S
  simp only [mul_sub,sum_sub_distrib]
  dsimp only [e] at hh cleaned
  linarith only [hh,cleaned]

end
end ImbalancedChen.Part5OriginalH430W2SignedOrdinaryBase
