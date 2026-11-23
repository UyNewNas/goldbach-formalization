import ImbalancedChen.Part5OriginalH430ActualMaskedBankWindows
import ImbalancedChen.Part5OriginalH430ReceiptSignedPredecessors

/-! The 106 selected signed rows on the actual root-receipt mask. Every
strict ordinary child is excluded by the original root quotient. The
rejected shell keeps the old lower and upper prices with their own signs. -/
namespace ImbalancedChen.Part5OriginalH430SelectedReceiptPlateau
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5OriginalActionMassBound P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedLowerPhysicalNode (residual)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430BankSlotTargets
open Part5OriginalH430SeedHistoryMass Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430SelectedFreshWindows Part5OriginalH430ReceiptFourBand
open Part5OriginalH430MonotoneSieveHeight Part5OriginalH430MaskedSievePlateau
open Part5OriginalH430ActualMaskedBankWindows
open Part5OriginalH430OwnedReceiptNet Part5OriginalH430ReceiptSignedPredecessors
open scoped Classical BigOperators

variable {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}

/-- The actual negative child sum for each W1 row and all three W2
lanes is zero. Its model lower price remains that of the previous row. -/
theorem direct_negative_zero (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) (l : Index N n k t p g)
    (b : Lane) (hl : l∈selectedLevel N n k t p g (owner b)) :
    Part5OriginalH430SelectedReceiptMother.strictSingle l b = 0 := by
  apply sum_eq_zero
  intro q hq
  rw [strict_single_carrier_empty hN ht hu hn hp l b hl hq _,card_empty,Nat.cast_zero]

/-- At the four actual positive ordinary children, the smaller fresh
prime alone already excludes the root receipt before summation. -/
theorem direct_pair_zero (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) (l : Index N n k t p g)
    (j : Fin 36) (s : Fin 4) (hl : l∈selectedLevel N n k t p g (.inr j)) : pairCount l j s=0 := by
  apply sum_eq_zero
  intro v hv
  rw [strict_pair_carrier_empty hN ht hu hn hp l j s hl hv _,card_empty,Nat.cast_zero]

/-- All fixed masked anchors, all true negative children, and all true
good pairs on their original selected row and original parent. -/
theorem selected_ordinary_values (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) (l : Index N n k t p g)
    (A : Original106Action) (hl : l∈selectedLevel N n k t p g A) :
    anchors l A=parentCount l ∧ negatives l A=0 ∧ positives l A=0 := by
  let r := levelOccurrence l
  have ho := (levelOccurrence_source l).1
  have hid : ∀ell,rootMask N p ell→rootMask N p ell := fun _ h => h
  have ha (s : ℝ) (hs : actionTarget A≤s) :
      count N (wordProduct l) (rootMask N p) (cutoff (rootQ N n k t p) (wordProduct l) s) = parentCount l :=
    counts_equal (original_band_prime hp).1.pos (member_product ho) hid
      (selected_cutoff_le hN ht hu hn hp l A hl hs) (member_cutoff_le_original hN ht hu hn hp ho)
  rcases A with ⟨i,j⟩ | j
  · exact ⟨ha _ (W1_target_le_anchor i j),by simp only [negatives,
      direct_negative_zero hN ht hu hn hp l (.inl (i,j)) hl,zero_div],rfl⟩
  · have hs (s : Fin 3) := direct_negative_zero hN ht hu hn hp l (.inr (j,s)) hl
    have hpair (s : Fin 4) := direct_pair_zero hN ht hu hn hp l j s hl
    refine ⟨?_,by simp only [negatives,hs,sum_const_zero,zero_div],
      by simp only [positives,hpair,sum_const_zero,zero_div]⟩
    change (4*count N _ _ _+count N _ _ _)/5=parentCount l
    rw [ha _ (W2_target_le_fixed j true),ha _ (W2_target_le_fixed j false)]
    ring

/-- The exact previous-generation net on the original receiver, with
both shell signs. The full switched price previously used to majorize
the masked mother can be subtracted in its entirety on this route. -/
theorem exact_previous_net (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) (l : Index N n k t p g)
    (A : Original106Action) (hl : l∈selectedLevel N n k t p g A) :
    parentCount l-parentModel l = Part5OriginalH430FreshBankBudget.strictDebt l A +
      correction l A+(modelRow l A-parentModel l)-switched l A := by
  obtain ⟨ha,hlow,hupp⟩ := selected_ordinary_values hN ht hu hn hp l A hl
  have he := signed_price_identity hN ht hu hn hp l A
  unfold row at he
  rw [ha,hlow,hupp] at he
  linarith only [he]

end
end ImbalancedChen.Part5OriginalH430SelectedReceiptPlateau
