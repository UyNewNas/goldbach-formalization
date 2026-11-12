import ImbalancedChen.Part5OriginalH430ReceiptPositiveBudget
import ImbalancedChen.Part5OriginalH430SelectedReceiptMother
import ImbalancedChen.Part5OriginalH430ReceiptDirections

/-! The original U3/U4 receipts in the selected 106-bank count inequality.
Only the positive switched sources are relaxed. The original square
payments are applied on this family's existing parent atoms. -/
namespace ImbalancedChen.Part5OriginalH430OwnedReceiptNet
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalPositiveSameQMassLift P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedCollisionThetaPayment (residual_level_le_N)
open P2AllW1FrozenReceiverFiniteAction (rawTripleCount original_W1_parameters)
open P2FrozenReceiverCountActions (quotientCount)
open P2OriginalW2CountTupleReindex P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430SelectedFreshWindows Part5OriginalH430FreshReceiptCounts (pair_receipt_split)
open Part5OriginalH430FreshBankBudget (remainingPositive all36_collision_on_history)
open Part5OriginalH430ReceiptFourBand (count)
open Part5OriginalH430ReceiptPositiveBudget (maskedState positive_budget)
open Part5OriginalH430SelectedReceiptMother (strictSingle selected_W1_receipt_mother selected_W2_receipt_mother)
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430W1FirstSquare (true_clean_count)
open Part5OriginalH430BankAfterW1PrimeRestriction (primeRestriction prime_restriction_eq)
open Part5OriginalH430ActualSelectedRowBudget (actualBankTheta)
open Part5OriginalH430OwnedRootCounts Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RequestedReads (requestValue)
open P2Selected430CausalOccurrenceExporter (iterate)
open scoped Classical BigOperators

variable {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}

def pairCount (l : Index N n k t p g) (j : Fin 36) (s : Fin 4) : ℝ :=
  let Q := rootQ N n k t p
  let d := wordProduct l
  ∑ v∈pairChildren j s N Q (oldWord l) (ceilingAt l),
    ((inheritedChild N (d*v.1.val*v.2.val) (tailProduct (levelOccurrence l)*v.2.val*v.1.val)
      (occurrenceCutoff Q d (originalW2At j) s v.1.val v.2.val)).card:ℝ)

theorem selected_pair_count (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k)
    (l : Index N n k t p g) (j : Fin 36) (s : Fin 4)
    (hl : l∈selectedLevel N n k t p g (.inr j)) :
    sourceGoodOccurrence N (rootQ N n k t p) (maskedState N (rootMask N p))
      (wordProduct l) (originalW2At j) s = pairCount l j s := by
  obtain ⟨hd,_,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
  rw [sourceGoodOccurrence_eq_window hd hQ,pair_W2 hN ht hu hn hp j s l hl]
  unfold pairCount
  apply sum_congr rfl
  intro v hv
  exact (pair_receipt_split hN ht hu hn hp l j s v hv).1

def parentCount (l : Index N n k t p g) : ℝ :=
  let Q := rootQ N n k t p
  count N (wordProduct l) (rootMask N p) (memberCutoff Q (levelOccurrence l))

def parentModel (l : Index N n k t p g) : ℝ :=
  let r := (levelOccurrence l).current
  thetaAtom N (rootQ N n k t p) (wordProduct l)*(P5CanonicalUpperCancellation.upperA
    r.node.physical.argument-requestValue (iterate (g.val+1)) r)

def anchors (l : Index N n k t p g) : Original106Action → ℝ
  | .inl (_,j) => count N (wordProduct l) (rootMask N p)
      (cutoff (rootQ N n k t p) (wordProduct l) (W1Anchor j))
  | .inr j =>
      let d := wordProduct l
      let z := cutoff (rootQ N n k t p) d
      let a := originalW2At j
      (4*count N d (rootMask N p) (z a.s0)+count N d (rootMask N p) (z a.phi1))/5

def negatives (l : Index N n k t p g) : Original106Action → ℝ
  | .inl (i,j) => strictSingle l (.inl (i,j))/2
  | .inr j => (∑ s : Fin 3,strictSingle l (.inr (j,s)))/5

def positives (l : Index N n k t p g) : Original106Action → ℝ
  | .inl _ => 0
  | .inr j => (∑ s : Fin 4,pairCount l j s)/5

def switched (l : Index N n k t p g) : Original106Action → ℝ
  | .inl (i,j) =>
      let z := cutoff (rootQ N n k t p) (wordProduct l)
      primeRestriction N (wordProduct l) (z (W1Anchor j)) (z (W1Target i))/2
  | .inr j => remainingPositive N (rootQ N n k t p) (wordProduct l) j/5

def row (l : Index N n k t p g) (a : Original106Action) : ℝ :=
  anchors l a-negatives l a+positives l a+switched l a

theorem selected_net {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N k →
      ∀ (g : Fin 430) (a : Original106Action) (l : Index N n k t p g),
      l∈selectedLevel N n k t p g a →
      parentCount l ≤ row l a + ε*thetaAtom N (rootQ N n k t p) (wordProduct l) := by
  obtain ⟨Tc,hc4,hc⟩ := all36_collision_on_history (show 0<5*ε by positivity)
  obtain ⟨Tw,hw4,hw⟩ := true_clean_count (div_pos frozenResidualFloor_pos (by norm_num : (0:ℝ)<5))
    (show 0<2*ε by positivity)
  refine ⟨max Tc Tw,hc4.trans (le_max_left _ _),?_⟩
  intro N hN hev n k t p ht hu hn hp g a l hl
  have hNc := (le_max_left Tc Tw).trans hN
  have hNw := (le_max_right Tc Tw).trans hN
  have h2 : 2≤N := by omega
  let Q := rootQ N n k t p
  let d := wordProduct l
  let E := rootMask N p
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha h2 ht hu hn hp l
  have hs := selected_geometry h2 ht hu hn hp a l hl
  have hR := (parentWindow_logs hs.1).2.1
  rcases a with ⟨i,j⟩|j
  · let z := cutoff Q d (W1Anchor j)
    let w := cutoff Q d (W1Target i)
    have hm := selected_W1_receipt_mother h2 ht hu hn hp i j l hl
    have hr : Q/(d:ℝ)≤(N:ℝ) := residual_level_le_N hd hs.1.2.2.2.1
    obtain ⟨hs0,hs1,hs5⟩ := original_W1_parameters i j
    have hz : (N:ℝ)^(frozenResidualFloor/5)≤z := by
      dsimp only [z]
      rw [cutoff_eq_physical_power hd hQ]
      apply rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
      exact (div_le_div_of_nonneg_right hL.1 (by norm_num : (0:ℝ)≤5)).trans
        (div_le_div_of_nonneg_left (frozenResidualFloor_pos.trans_le hL.1).le (by linarith) hs5)
    have hclean := hw N hNw Q d z w hd hR hr hz hs.2.2.2
    rw [prime_restriction_eq _ _ _ _ hd] at hclean
    have hh : (rawTripleCount N d (d*N) E z w:ℝ) ≤
        (rawTripleCount N d (d*N) (receiver N) z w:ℝ) := by
      exact_mod_cast Part5OriginalH430ReceiptDirections.W1_raw_positive_le_receiver N p d (d*N) z w
    change 2*parentCount l ≤ 2*count N d E z-strictSingle l (.inl (i,j))+
      (rawTripleCount N d (d*N) E z w:ℝ) at hm
    change parentCount l ≤ count N d E z - strictSingle l (.inl (i,j))/2 + 0 +
      primeRestriction N d z w/2 + ε*thetaAtom N Q d
    linarith only [hm,hh,hclean]
  · let b := originalW2At j
    let z := cutoff Q d
    have hm := selected_W2_receipt_mother h2 ht hu hn hp j l hl
    have hP := positive_budget N d Q E j hR.le
    dsimp only at hP
    simp_rw [selected_pair_count h2 ht hu hn hp l j _ hl] at hP
    have hcoll := hc N hNc hev n k t p (g.val+1) ht hu hn hp l j
    change 5*parentCount l ≤ 4*count N d E (z b.s0)+count N d E (z b.phi1)-
      strictSingle l (.inr (j,0))-strictSingle l (.inr (j,1))-
      strictSingle l (.inr (j,2))+_ at hm
    change parentCount l ≤ (4*count N d E (z b.s0)+count N d E (z b.phi1))/5-
      (∑ s : Fin 3,strictSingle l (.inr (j,s)))/5 + (∑ s : Fin 4,pairCount l j s)/5+
      remainingPositive N Q d j/5 + ε*thetaAtom N Q d
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at ⊢
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hP
    linarith only [hm,hP,hcoll]

/-- A genuine same-cell U3/U4 absolute budget. The loss is charged on the
old marked atoms, also when the fibre is empty. The center is the
selected argument and its own immutable table request. -/
theorem owned_106_net {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n m : ℕ) (k : Root) (t : ℝ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → ∀ (c : RootKey n m) (g : Fin 430),
      let P := rootFibre N n m k t c
      let Q := cellQ N n c.1
      (∑ p∈P,∑ a : Original106Action,∑ l∈selectedLevel N n k t p g a,
        levelMark l*(((originalReceiptLane N p (tailProduct (levelOccurrence l))
          (memberCutoff Q (levelOccurrence l))).card:ℝ)-parentModel l)) ≤
      (∑ p∈P,∑ a : Original106Action,∑ l∈selectedLevel N n k t p g a,
        levelMark l*(row l a-parentModel l)) + ε*(∑ p∈P,actualBankTheta N n k t p g) := by
  obtain ⟨T,h4,hT⟩ := selected_net he
  refine ⟨T,h4,?_⟩
  intro N hN hev n m k t ht hu hn c g
  dsimp only
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have h2 : 2≤N := by omega
  have hb := (mem_filter.mp hp).1
  have hQ := (original_fibre_geometry h2 ht hu hn hp).1
  unfold actualBankTheta
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro a _
  unfold levelTheta
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro l hl
  have hh := hT N hN hev n k t p ht hu hn hb g a l hl
  have hc := owned_member_masked_count h2 ht hu hn hp (levelOccurrence_source l).1
  dsimp only at hc
  rw [←hc,hQ]
  nlinarith only [mul_le_mul_of_nonneg_left hh (mark_pos (levelOccurrence l)).le]

end
end ImbalancedChen.Part5OriginalH430OwnedReceiptNet
