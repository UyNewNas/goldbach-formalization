import ImbalancedChen.Part5OriginalH430FreshBankBudget
import ImbalancedChen.Part5OriginalH430OriginalReceiptMemberPullback

/-! The strict ordinary child retains the original additive prime. Its
old-word multiplier identifies exactly which raw quotients also belong to
the original root receipt. This is a count splitting, without a density
claim about the difference or a changed parent normalizer. -/
namespace ImbalancedChen.Part5OriginalH430FreshReceiptCounts
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5OriginalActionMassBound
open P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2OriginalHalfOpenProfileCarrier (normalizedLog)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open Part5OriginalH430ImmutableBankProfiles (precedingH precedingh)
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger (selectedBankRoundingLoss)
open Part5OriginalH430ActualSelectedRowBudget (actualBankTheta)
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open P2EnhancedCollisionWeightedBudget (list_prime_divisor_lower)
open P2FrozenReceiverCountActions (frozenCount)
open P5OriginalU5FrozenSource (receiver frozenCount_eq_original_count)
open P2OriginalW2CountTupleReindex (occurrenceCutoff)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430SelectedFreshWindows Part5OriginalH430FreshBankBudget
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430OwnedRootCounts Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RequestedReads (requestValue)
open P2Selected430CausalOccurrenceExporter (iterate)
open scoped Classical BigOperators

variable {N n p : ℕ} {rt : Root} {t : ℝ} {g : Fin 430}

private theorem prime_power (hN : 2≤N) {q : ℕ} (hq : q.Prime) :
    (N:ℝ)^physicalPrime N q=(q:ℝ) :=
  actualPrimeTupleLog_rpow (by omega : 1<N) (fun _ : Fin 1 => q) (fun _ => hq.pos) 0

private theorem rough_times_prime {z : ℝ} {b q : ℕ}
    (hb : ChenPrimeRough z b) (hq : q.Prime) (hz : z≤q) : ChenPrimeRough z (b*q) := by
  intro r hr hdiv
  rcases hr.dvd_mul.mp hdiv with h | h
  · exact hb r hr h
  · rwa [(Nat.prime_dvd_prime_iff_eq hr hq).mp h]

private theorem old_rough_physical (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (l : Index N n rt t p g) {x : ℝ} (hx : x≤ceilingAt l) :
    ChenPrimeRough ((N:ℝ)^x) (wordProduct l) := by
  have ho := (levelOccurrence_source l).1
  have hc := rootHistory_coherent (by omega : 1<N) ht hu hn (original_band_prime hp)
    (original_band_geometry hN hp) ho
  intro r hr hd
  apply list_prime_divisor_lower (oldWord l) hr hd
  intro q hq
  have hpr := (hc.letters q hq).1
  refine ⟨hpr,?_⟩
  rw [←prime_power hN hpr]
  exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
    (hx.trans (history_ceiling_le_letter hN ht hu hn hp ho q hq))

private theorem receipt_split {B D : ℕ} {z : ℝ} (hp : 0<p) (hB : B=p*D)
    (hr : ChenPrimeRough z B) :
    (frozenCount N B (rootMask N p) z:ℝ) = ((inheritedChild N B D z).card:ℝ) ∧
    (frozenCount N B (receiver N) z:ℝ) =
      (frozenCount N B (rootMask N p) z:ℝ) + ((rejectedChild N B D z).card:ℝ) := by
  have hm := rootMasked_count hp hB hr
  refine ⟨hm,?_⟩
  rw [frozenCount_eq_original_count _ _ _ hr,hm]
  have hh : inheritedChild N B D z ⊆ chenSiftedQuotientPrimeSource N B z :=
    filter_subset _ _
  exact_mod_cast (show (chenSiftedQuotientPrimeSource N B z).card =
      (inheritedChild N B D z).card + (rejectedChild N B D z).card by
    simpa only [rejectedChild,Nat.add_comm] using (card_sdiff_add_card_eq_card hh).symm)

theorem single_receipt_split (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (l : Index N n rt t p g) (a : Lane) (q : Fin (N+1))
    (hq : q∈singleChildren (rule a) N (rootQ N n rt t p) (oldWord l) (ceilingAt l)) :
    let Q := rootQ N n rt t p
    let B := wordProduct l*q.val
    let D := tailProduct (levelOccurrence l)*q.val
    let z := cutoff Q (wordProduct l) (anchor a)
    (frozenCount N B (rootMask N p) z:ℝ) = ((inheritedChild N B D z).card:ℝ) ∧
    (frozenCount N B (receiver N) z:ℝ) =
      (frozenCount N B (rootMask N p) z:ℝ) + ((rejectedChild N B D z).card:ℝ) := by
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
  let Q := rootQ N n rt t p
  let x := singleCutoff (rule a) N Q (oldWord l) q.val
  have hz : cutoff Q (wordProduct l) (anchor a)=(N:ℝ)^x := by
    rw [cutoff_eq_physical_power hd hQ]
    rcases a with ⟨i,j⟩ | ⟨j,s⟩ <;> rfl
  have hfit := single_cutoff_below_prime hq
  have hpr := (mem_singleChildren.mp hq).1.1
  have hrough := old_rough_physical hN ht hu hn hp l (hfit.1.trans hfit.2.le)
  have hqz : (N:ℝ)^x≤q.val := (rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1≤N by omega) : (1:ℝ)≤N) hfit.1).trans_eq (prime_power hN hpr)
  apply receipt_split (original_band_prime hp).1.pos
  · show parentProduct (levelOccurrence l).current.old*q.val=_
    rw [member_product (levelOccurrence_source l).1,Nat.mul_assoc]
  · rw [hz]
    exact rough_times_prime hrough hpr hqz

theorem pair_receipt_split (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (l : Index N n rt t p g) (j : Fin 36) (s : Fin 4) (v : Fin (N+1) × Fin (N+1))
    (hv : v∈pairChildren j s N (rootQ N n rt t p) (oldWord l) (ceilingAt l)) :
    let Q := rootQ N n rt t p
    let B := wordProduct l*v.1.val*v.2.val
    let D := tailProduct (levelOccurrence l)*v.2.val*v.1.val
    let z := occurrenceCutoff Q (wordProduct l) (originalW2At j) s v.1.val v.2.val
    (frozenCount N B (rootMask N p) z:ℝ) = ((inheritedChild N B D z).card:ℝ) ∧
    (frozenCount N B (receiver N) z:ℝ) =
      (frozenCount N B (rootMask N p) z:ℝ) + ((rejectedChild N B D z).card:ℝ) := by
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
  let Q := rootQ N n rt t p
  let x := pairCutoff j s N Q (oldWord l) v.1.val
  have hm := mem_pairChildren.mp hv
  have hpr := hm.1.1.1
  have hqr := hm.1.2.1
  have hz : occurrenceCutoff Q (wordProduct l) (originalW2At j) s v.1.val v.2.val=(N:ℝ)^x := by
    dsimp only [x,occurrenceCutoff,pairCutoff]
    split_ifs
    · exact cutoff_eq_physical_power hd hQ
    · exact (prime_power hN hpr).symm
  have hfit := pair_cutoff_below_prime hv
  have hrough := old_rough_physical hN ht hu hn hp l (hfit.1.trans hfit.2.1.le)
  have hpz : (N:ℝ)^x≤v.1.val := (rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1≤N by omega) : (1:ℝ)≤N) hfit.1).trans_eq (prime_power hN hpr)
  have hqz : (N:ℝ)^x≤v.2.val := hpz.trans (by exact_mod_cast hm.2.2.1.le)
  apply receipt_split (original_band_prime hp).1.pos
  · show parentProduct (levelOccurrence l).current.old*v.1.val*v.2.val=_
    rw [member_product (levelOccurrence_source l).1]
    ring
  · rw [hz]
    exact rough_times_prime (rough_times_prime hrough hpr hpz) hqr hqz

/-- The negative singleton count subtracts the shell; the positive pair
count adds it. Each shell is an actual quotient set with the same z. -/
def receiptSingle (l : Index N n rt t p g) (a : Lane) : ℝ :=
  let Q := rootQ N n rt t p
  let d := wordProduct l
  let z := cutoff Q d (anchor a)
  ∑ q∈singleChildren (rule a) N Q (oldWord l) (ceilingAt l),
    let B := d*q.val
    let D := tailProduct (levelOccurrence l)*q.val
    let u := argument N Q d q.val a
    thetaAtom N Q B*(P5CanonicalUpperCancellation.lowerBar u+tableFunction true (precedingh g) u) -
      ((inheritedChild N B D z).card:ℝ) - ((rejectedChild N B D z).card:ℝ)

def receiptPair (l : Index N n rt t p g) (j : Fin 36) (s : Fin 4) : ℝ :=
  let Q := rootQ N n rt t p
  let d := wordProduct l
  let a := originalW2At j
  ∑ v∈pairChildren j s N Q (oldWord l) (ceilingAt l),
    let B := d*v.1.val*v.2.val
    let D := tailProduct (levelOccurrence l)*v.2.val*v.1.val
    let z := occurrenceCutoff Q d a s v.1.val v.2.val
    let u := pairProfile a s (normalizedLog N (wordLevel l)
      (P2OriginalPairChildWindowDictionary.pairTuple v))
    ((inheritedChild N B D z).card:ℝ) + ((rejectedChild N B D z).card:ℝ) -
      thetaAtom N Q B*(P5CanonicalUpperCancellation.upperA u-tableFunction false (precedingH g) u)

theorem strict_receipt_rows (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt) (l : Index N n rt t p g) :
    (∀ a,strictSingle l a = receiptSingle l a) ∧
    (∀ j s,strictPair l j s = receiptPair l j s) := by
  constructor
  · intro a
    unfold strictSingle receiptSingle
    apply sum_congr rfl
    intro q hq
    obtain ⟨hm,hh⟩ := single_receipt_split hN ht hu hn hp l a q hq
    dsimp only at hm hh ⊢
    rw [hh,hm]
    ring
  · intro j s
    unfold strictPair receiptPair
    apply sum_congr rfl
    intro v hv
    obtain ⟨hm,hh⟩ := pair_receipt_split hN ht hu hn hp l j s v hv
    dsimp only at hm hh ⊢
    unfold pairDifference
    change (frozenCount N _ (receiver N) _:ℝ)-_ = _ + _ - _
    rw [hh,hm]

def receiptDebt (l : Index N n rt t p g) : Original106Action → ℝ
  | .inl (i,j) =>
    let Q := rootQ N n rt t p
    let d := wordProduct l
    Part5OriginalH430W1SignedOrdinaryBase.fixedDebt N Q d i j g +
      receiptSingle l (.inl (i,j))/2 + Part5OriginalH430BankAfterW1PrimeRestriction.cleanDebt N Q d i j
  | .inr j =>
    let Q := rootQ N n rt t p
    let d := wordProduct l
    Part5OriginalH430W2SignedOrdinaryBase.fixedDebt N Q d j g +
      (∑ s : Fin 3, receiptSingle l (.inr (j,s)))/5 +
      (∑ s : Fin 4, receiptPair l j s)/5 +
      (remainingPositive N Q d j/5 - (Part5OriginalH430W2SignedOrdinaryBase.ordinaryBase j -
        Part5OriginalH430FixedReadDictionary.baseValue (.inr j))*thetaAtom N Q d)

theorem full_bank_receipt_shell_budget {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (rt : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N rt →
      ∀ g : Fin 430,
        (∑ a : Original106Action,∑ l∈selectedLevel N n rt t p g a,
          levelMark l*Part5OriginalH430AllBankSignedCounts.physicalDefect l)+
          selectedBankRoundingLoss N n rt t p g ≤
        (∑ a : Original106Action,∑ l∈selectedLevel N n rt t p g a,levelMark l*receiptDebt l a)+
          ε*actualBankTheta N n rt t p g := by
  obtain ⟨T,h4,hT⟩ := full_bank_strict_after_exceptions he
  refine ⟨T,h4,?_⟩
  intro N hN hEven n rt t p ht hu hn hp g
  have h := hT N hN hEven n rt t p ht hu hn hp g
  have hd (l : Index N n rt t p g) (a : Original106Action) : strictDebt l a=receiptDebt l a := by
    obtain ⟨h1,h2⟩ := strict_receipt_rows (by omega : 2≤N) ht hu hn hp l
    rcases a with ⟨i,j⟩ | j <;> simp only [strictDebt,receiptDebt,h1,h2]
  simpa only [hd] using h

def receiptParent (Q : ℝ) (l : Index N n rt t p g) : ℝ :=
  let o := levelOccurrence l
  let d := wordProduct l
  let D := tailProduct o
  let z := memberCutoff Q o
  ((originalReceiptLane N p D z).card:ℝ) + ((rejectedChild N d D z).card:ℝ) -
    thetaAtom N Q d*(P5CanonicalUpperCancellation.upperA o.current.node.physical.argument -
      requestValue (iterate (g.val+1)) o.current)

/-- Fix the original tagged root fibre before adding its prime labels.
Parent and children have their literal receipt and rejected terms; all
positions in this estimate have the common level cellQ N n c.1. -/
theorem owned_fibre_bank_receipt_budget {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n m : ℕ) (rt : Root) (t : ℝ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → ∀ (c : RootKey n m) (g : Fin 430),
      let P := rootFibre N n m rt t c
      let Q := cellQ N n c.1
      (∑ p∈P, ((∑ a : Original106Action, ∑ l∈selectedLevel N n rt t p g a,levelMark l*receiptParent Q l) +
        selectedBankRoundingLoss N n rt t p g)) ≤
      (∑ p∈P, ∑ a : Original106Action, ∑ l∈selectedLevel N n rt t p g a,levelMark l*receiptDebt l a) +
        ε*(∑ p∈P,actualBankTheta N n rt t p g) := by
  obtain ⟨T,h4,hT⟩ := full_bank_receipt_shell_budget he
  refine ⟨T,h4,?_⟩
  intro N hN hEven n m rt t ht hu hn c g
  dsimp only
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have h2 : 2≤N := by omega
  have hband := (mem_filter.mp hp).1
  have hQ := (original_fibre_geometry h2 ht hu hn hp).1
  have hparent (l : Index N n rt t p g) :
      Part5OriginalH430AllBankSignedCounts.physicalDefect l = receiptParent (cellQ N n c.1) l := by
    have hcount := actual_member_count_split h2 ht hu hn hp (levelOccurrence_source l).1
    have hf := history_frozen_count_eq_true_quotient h2 ht hu hn hband (levelOccurrence_source l).1
    dsimp only at hcount hf
    unfold Part5OriginalH430AllBankSignedCounts.physicalDefect
      Part5OriginalH430SelectedOrdinaryPairCounts.trueAt receiptParent
    rw [←hf,←hQ]
    change (frozenCount N _ (receiver N) (memberCutoff (cellQ N n c.1) (levelOccurrence l)):ℝ) -
        _ = _ + _ - _
    rw [hcount]
  simpa only [hparent] using hT N hN hEven n rt t p ht hu hn hband g

end
end ImbalancedChen.Part5OriginalH430FreshReceiptCounts
