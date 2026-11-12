import ImbalancedChen.Part5OriginalH430ReceiptPairIncidences

/-! Strict ordinary pairs use the original receipt. Only off-gate pairs
and genuine longer words enter the old full positive source. -/
namespace ImbalancedChen.Part5OriginalH430ReceiptPositiveBudget
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneQuotientFinite P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalW2ComplementAction P2OriginalW2MotherOccurrenceReindex
open P2OriginalW2CountTupleReindex P2AllW1SameQRawCountInduction (PhysicalState)
open P2W2PhysicalChildFeedback (PairGate count_le_true)
open P5OriginalActionMassBound (originalW2At)
open Part5OriginalH430ReceiptFourBand
open Part5OriginalH430ReceiptPairIncidences
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430FreshBankBudget (remainingPositive collision)
open scoped Classical BigOperators

def maskedState (N : ℕ) (E : ℕ → Prop) : PhysicalState :=
  ⟨fun d z => count N d E z,fun d z => count N d E z⟩

private def high := secondFunctionalMotherPrefixIndices.drop 2

private def highMass (N d : ℕ) (E : ℕ → Prop) (a b c e f : ℝ) : ℝ :=
  ∑ ell∈outputs N d a E,(high.map fun i =>
    (secondFunctionalMotherGammaLabels (labels N d a f ell)
      (secondFunctionalMotherColour b c e) i:ℝ)).sum

private theorem high_bound (N d : ℕ) (Q : ℝ) (E : ℕ → Prop) (a b c e f : ℝ) :
    highMass N d E a b c e f ≤ higherPaidSwitched N Q (actualState N) d a b c e f +
      collisionSwitched N d N a b c e f := by
  let G := secondFunctionalMotherGammaWords
  let T := secondFunctionalMotherPrefixTerm N d (d*N) a b c e f
  let P := paidPrefix N Q (actualState N) d a b c e f
  let C := collisionPrefixTerm N d N a b c e f
  have hlen (i : ℕ) (hi : i∈high) (cs : List ℕ) (hc : cs∈G i) : 3≤cs.length := by
    simp only [high,secondFunctionalMotherPrefixIndices,List.drop_succ_cons,List.drop_zero,
      List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [G,secondFunctionalMotherGammaWords,List.mem_cons,List.not_mem_nil,or_false] at hc <;>
      aesop
  have hm : highMass N d E a b c e f ≤
      (high.map fun i => ((G i).map T).sum).sum := by
    apply le_trans _ (secondFunctionalMother_package_mass_le N d a b c e f high
      (fun i hi cs hc => le_trans (by decide : 2≤3) (hlen i hi cs hc)))
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro ell _ _
    apply List.sum_nonneg
    intro y hy
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hy
    positivity
  have hw (i : ℕ) (hi : i∈high) (cs : List ℕ) (hc : cs∈G i) : T cs≤P cs+C cs := by
    have he : P cs=quotientPrefixTerm N d N a b c e f cs := by
      unfold P paidPrefix quotientPrefixTerm
      apply sum_congr rfl
      intro l hl
      have hh := ((secondFunctionalMother_tuple_mem _ _ _).mp hl).1
      have hl3 := hlen i hi cs hc
      rw [paidQuotient_long N Q (actualState N) d l (by omega)]
    rw [he]
    exact (secondFunctionalMother_prefix_mono N d a b c e f cs).trans
      (prefixTerm_le_quotient_add_collision N d N a b c e f cs)
  have hs := secondFunctionalMother_list_sum_mono high
    (fun i => ((G i).map T).sum) (fun i => ((G i).map P).sum+((G i).map C).sum)
    (fun i hi => by simpa only [List.sum_map_add] using
      secondFunctionalMother_list_sum_mono (G i) T (fun cs => P cs+C cs) (hw i hi))
  rw [List.sum_map_add] at hs
  have hP : (high.map fun i => ((G i).map P).sum).sum =
      higherPaidSwitched N Q (actualState N) d a b c e f := by
    norm_num [high,G,P,higherPaidSwitched,secondFunctionalMotherPrefixIndices,
      secondFunctionalMotherGammaWords]
  have hC : (high.map fun i => ((G i).map C).sum).sum ≤ collisionSwitched N d N a b c e f := by
    change _ ≤ (secondFunctionalMotherPrefixIndices.map fun i => ((G i).map C).sum).sum
    rw [show secondFunctionalMotherPrefixIndices=7::8::high from rfl]
    simp only [List.map_cons,List.sum_cons]
    have hpos (i : ℕ) : 0≤((G i).map C).sum := by
      apply List.sum_nonneg
      intro y hy
      obtain ⟨cs,_,rfl⟩ := List.mem_map.mp hy
      exact collisionPrefixTerm_nonneg _ _ _ _ _ _ _ _ _
    linarith only [hpos 7,hpos 8]
  exact hm.trans (hs.trans (add_le_add hP.le hC))

private theorem rect_paid (N d : ℕ) (Q : ℝ) (E : ℕ → Prop) (a u v w : ℝ)
    (z : ℕ → ℕ → ℝ) :
    rect (primeWindow (d*N) a u) (primeWindow (d*N) v w)
        (fun p q => count N (d*p*q) E (z p q)) ≤
      rect (primeWindow N a u) (primeWindow N v w)
        (fun p q => paidChild N Q (maskedState N E) d p q (z p q)) := by
  let F := fun p q : ℕ => if p<q then paidChild N Q (maskedState N E) d p q (z p q) else 0
  have hF (p q : ℕ) : 0≤F p q := by
    dsimp only [F,paidChild,maskedState,count,P2FrozenReceiverCountActions.frozenCount]
    split_ifs <;> positivity
  unfold rect
  calc
    _ ≤ ∑ p∈primeWindow (d*N) a u, ∑ q∈primeWindow (d*N) v w,F p q := by
      apply sum_le_sum
      intro p _
      apply sum_le_sum
      intro q _
      dsimp only [F,paidChild,maskedState]
      split_ifs <;> first | exact le_rfl | exact count_le_true _ _ _ _
    _ ≤ ∑ p∈primeWindow (d*N) a u, ∑ q∈primeWindow N v w,F p q :=
      sum_le_sum fun p _ => sum_le_sum_of_subset_of_nonneg
        (fourthRowMother_window_subset N d v w) (fun q _ _ => hF p q)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fourthRowMother_window_subset N d a u)
      (fun p _ _ => sum_nonneg fun q _ => hF p q)

theorem positive_budget (N d : ℕ) (Q : ℝ) (E : ℕ → Prop) (j : Fin 36)
    (hR : 1≤Q/(d:ℝ)) :
    let k := originalW2At j
    positiveMass N d E (cutoff Q d k.s0) (cutoff Q d k.phi1) (cutoff Q d k.phi2)
        (cutoff Q d k.phi3) (cutoff Q d k.s) ≤
      (∑ s : Fin 4,sourceGoodOccurrence N Q (maskedState N E) d k s) +
        remainingPositive N Q d j + collision N Q d j := by
  let k := originalW2At j
  let a := cutoff Q d k.s0
  let b := cutoff Q d k.phi1
  let c := cutoff Q d k.phi2
  let e := cutoff Q d k.phi3
  let f := cutoff Q d k.s
  let old := maskedState N E
  obtain ⟨hab,hbc,hce,hef⟩ := P2AllW2SameQRawCountAction.bank_cutoff_order j hR
  have hbf : b≤f := hbc.trans (hce.trans hef)
  have hcf : c≤f := hce.trans hef
  have h56 := gamma56 N d E hab hbc hce hef
  have h7 := prefix_pair_mass N d E a b c e f 0 0
  have h8 := prefix_pair_mass N d E a b c e f 0 1
  dsimp only at h56 h7 h8 ⊢
  rw [MotherPair.colour_zero_window (d*N) hbf] at h7
  rw [MotherPair.colour_zero_window (d*N) hbf,MotherPair.colour_one_window (d*N) hab hcf] at h8
  have hr5 := h56.1.le.trans (rect_paid N d Q E a c a c (fun _ _ => a))
  have hr6 := h56.2.le.trans (rect_paid N d Q E a b c e (fun _ _ => a))
  have hr7 := h7.le.trans (rect_paid N d Q E a b a b (fun p _ => (p:ℝ)))
  have hr8 := h8.le.trans (rect_paid N d Q E a b b c (fun p _ => (p:ℝ)))
  have split := four_original_occurrences_split N Q old d j hR
  dsimp only at split
  have hp (x y z : ℝ) : paidPairs N Q old d a x y z =
      rect (primeWindow N a x) (primeWindow N y z) (fun p q => paidChild N Q old d p q a) := by
    unfold paidPairs rect
    rw [sum_comm]
  change paidPairs N Q old d a c a c + paidPairs N Q old d a b c e +
      paidPrefix N Q old d a b c e f [0,0]+paidPrefix N Q old d a b c e f [0,1] = _ at split
  rw [hp,hp,paidPrefix_seven N Q old d hbf,paidPrefix_eight N Q old d hab hbf hcf] at split
  let L := fun ell => labels N d a f ell
  let χ := secondFunctionalMotherColour b c e
  let S := outputs N d a E
  have he : positiveMass N d E a b c e f =
      (∑ ell∈S,((fourthRowMotherLowPairs (L ell) χ).card:ℝ))+
      (∑ ell∈S,((fourthRowMotherCrossPairs (L ell) χ).card:ℝ))+
      (∑ ell∈S,((fourthRowMotherColoured (L ell) χ [0,0]).card:ℝ))+
      (∑ ell∈S,((fourthRowMotherColoured (L ell) χ [0,1]).card:ℝ))+highMass N d E a b c e f := by
    unfold positiveMass positiveLabels highMass
    rw [show secondFunctionalMotherPrefixIndices=7::8::high from rfl]
    simp only [List.map_cons,List.sum_cons]
    change (∑ ell∈S, _)=_
    simp only [sum_add_distrib]
    simp [secondFunctionalMotherGammaLabels,secondFunctionalMotherGammaWords,L,χ,S,labels,outputs]
    <;> ring
  have hh := high_bound N d Q E a b c e f
  change positiveMass N d E a b c e f ≤ _ + remainingPositive N Q d j + collision N Q d j
  rw [he]
  dsimp only [remainingPositive,collision]
  dsimp only [S,L,χ,old,rect] at hr5 hr6 hr7 hr8 split ⊢
  linarith only [hr5,hr6,hr7,hr8,split,hh]

end
end ImbalancedChen.Part5OriginalH430ReceiptPositiveBudget
