import ImbalancedChen.Part5OriginalH430SeedRejectedPairCounts
import ImbalancedChen.P2ActualSameQTwentyOnePositiveSourceBinding

/-! The residual positive prime restriction at the seed consists of the
original bad Γ5 and the thirteen longer Γ9–21 lanes. This uses the
native arithmetic label and the original penultimate-prime cutoff, with
unit quotients and the original multiplicity of each colour word. -/
namespace ImbalancedChen.Part5OriginalH430SeedThirteenPrimeWords
noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions
open P2AllW1SameQRawCountInduction (PhysicalState)
open P2W2PhysicalChildFeedback
open P2OriginalW2ComplementAction P2OriginalW2CountTupleReindex P2OriginalW2MotherOccurrenceReindex
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedTwentyOneChildCorrection (localPositivePairs localSwitched)
open P2EnhancedTwentyOneQuotientFinite (quotientPrefixTerm)
open P2ActualSameQTwentyOnePositiveSourceBinding (actualLocalPrimeMass actual_local_source_identity)
open P2TwentyOneUnsiftedArithmeticSource (arithmeticLabels product quotientPrefixTerm_eq_primeMass)
open P2EnhancedSwitchedUnsiftedSource (originalBadPairCount)
open P2OriginalW2CentreIncidence (complement_nonnegative)
open P5OriginalU5FrozenSource (receiver)
open P5OriginalActionMassBound (originalW2At)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430SeedRejectedPairCounts (four_rejected_eq_original)
open scoped Classical BigOperators

def primeWord (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  p5z_labelledPrimeMass (arithmeticLabels N d N (cutoff Q d (227/50)) (cutoff Q d (353/100))
    (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5)) cs)
    (product d) (fun _ => 1) N

def longPrime (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map (primeWord N Q d)).sum

def restrictedPrime (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ := originalBadPairCount N Q d+longPrime N Q d

private theorem higher_index (F : List ℕ → ℝ) :
    (secondFunctionalMotherPrefixIndices.map fun i =>
      (((secondFunctionalMotherGammaWords i).filter (fun cs => cs.length≠2)).map F).sum).sum =
      ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map F).sum := by
  norm_num [secondFunctionalMotherPrefixIndices,secondFunctionalMotherGammaWords,Fin.sum_univ_succ]
  <;> ring

private theorem paid_long (N : ℕ) (Q : ℝ) (old : PhysicalState) (d : ℕ)
    (a b c e f : ℝ) {cs : List ℕ} (hc : cs.length≠2) :
    paidPrefix N Q old d a b c e f cs=quotientPrefixTerm N d N a b c e f cs := by
  unfold paidPrefix quotientPrefixTerm
  apply sum_congr rfl
  intro l hl
  have hlen := ((secondFunctionalMother_tuple_mem _ _ l).mp hl).1
  split_ifs
  · exact paidQuotient_long N Q old d l (by omega)
  · rfl

theorem higher_prime_words {N d : ℕ} (Q : ℝ) (old : PhysicalState)
    (hN : 4≤N) (he : Even N) (hd : 0<d) :
    higherPaidSwitched N Q old d (cutoff Q d (227/50)) (cutoff Q d (353/100))
        (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5))=longPrime N Q d := by
  unfold longPrime higherPaidSwitched
  rw [← higher_index]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  apply congrArg List.sum
  apply List.map_congr_left
  intro cs hcs
  have hlen : cs.length≠2 := by simpa using (List.mem_filter.mp hcs).2
  rw [paid_long _ _ _ _ _ _ _ _ _ hlen]
  simpa only [one_mul,primeWord] using
    (quotientPrefixTerm_eq_primeMass (N:=N) (d:=d) (M:=N) (cs:=cs)
      (a:=cutoff Q d (227/50)) (b:=cutoff Q d (353/100)) (c:=cutoff Q d (29/10))
      (e:=cutoff Q d (61/25)) (f:=cutoff Q d (11/5)) hN he hd 1)

/-- Local count comparison before any average or distribution estimate. -/
theorem mother_positive_split {N d : ℕ} {Q : ℝ} (hN : 4≤N) (he : Even N)
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) :
    localPositivePairs N Q d+actualLocalPrimeMass N Q d ≤
      (∑ k : Fin 4,sourceGoodOccurrence N Q (actualState N) d (originalW2At 0) k)+
        restrictedPrime N Q d+W2Charge N Q d 0 := by
  let A := cutoff Q d (227/50); let B := cutoff Q d (353/100)
  let C := cutoff Q d (29/10); let E := cutoff Q d (61/25); let Z := cutoff Q d (11/5)
  let o := actualState N
  have h5 := positivePairs_upper N Q (receiver N) o A C A C hd (fun _ _ _ => ⟨le_rfl,le_rfl⟩)
  have h6 := positivePairs_upper N Q (receiver N) o A B C E hd (fun _ _ _ => ⟨le_rfl,le_rfl⟩)
  have h7 := switchedFeedback_upper N Q (receiver N) o A B C E Z hd (fun _ _ _ => ⟨le_rfl,le_rfl⟩)
  rw [positivePairs_eq_paid_add_charge] at h5 h6
  rw [switchedFeedback_eq_paid_add_charge,paidSwitched_occurrences] at h7
  have hfour := four_original_occurrences_split N Q o d 0 hR.le
  change paidPairs N Q o d A C A C+paidPairs N Q o d A B C E+
    paidPrefix N Q o d A B C E Z [0,0]+paidPrefix N Q o d A B C E Z [0,1]=
      (∑ k : Fin 4,sourceGoodOccurrence N Q o d (originalW2At 0) k)+
      (∑ k : Fin 4,sourceRejectedOccurrence N Q d (originalW2At 0) k) at hfour
  rw [four_rejected_eq_original hd hR] at hfour
  rw [higher_prime_words Q o hN he hd] at h7
  rw [←actual_local_source_identity Q hN he hd]
  unfold restrictedPrime
  change fourthRowMotherPair N d N A C A C+fourthRowMotherPair N d N A B C E+
    P2EnhancedTwentyOneQuotientFinite.quotientSwitched N d N A B C E Z ≤
      (∑ k : Fin 4,sourceGoodOccurrence N Q o d (originalW2At 0) k)+
      (originalBadPairCount N Q d+longPrime N Q d)+
      (4*complementCount N d (receiver N) A+complementCount N d (receiver N) B+
        pairCharge N Q d A C A C+pairCharge N Q d A B C E+switchedCharge N Q d A B C E Z)
  linarith only [h5,h6,h7,hfour,complement_nonnegative N d A,complement_nonnegative N d B]

end
end ImbalancedChen.Part5OriginalH430SeedThirteenPrimeWords
