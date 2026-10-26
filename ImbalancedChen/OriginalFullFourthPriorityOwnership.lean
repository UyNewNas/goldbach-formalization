import ImbalancedChen.P1OriginalFullTableCheckProgramSoundness
import ImbalancedChen.P1OriginalProducerAttainedRowBinding
import ImbalancedChen.P1OriginalVariableFourthProfileRegularity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

An exact positional ownership refinement of the ACTUAL original fourth
producer maximum for an arbitrary complete ordered raw table. Positions
are never deduplicated: slot zero is the inherited raw-Q3 seed, and slot
i+1 is the literal input record i, with the original lo/hi/mask decoder.

Among all eligible MAXIMIZERS, the first bank position owns the point.
This is an accounting refinement: it does not replace the original maximum
by first-match eligibility. Seed wins a tie with every row; raw-record order
breaks row ties. Any original externally specified priority can instantiate
the input list in that order. No assertion is made that an absent original
priority/history payload was recovered from the saved NPZ statistics.

The resulting source regions cover every point, including the inherited
fallback, and are exactly disjoint even at closed-box faces and ties.
Arbitrary signed tests disintegrate with coefficient ONE, so negative
contributions are not discarded. The exact original rank-four history cap
is tied to this owner, retaining e/chi/omega and the original raw-Q3 seed.

This does NOT supply the complete 22-successor geometric license, the
external row licenses, a full-table check pass, or any saved gain. The raw
payload has no e/chi/omega, dynamic raw-Q3 owner, or successor-history fields.
-/

namespace ImbalancedChen.OriginalFullFourthPriorityOwnership20261026a

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalProducerAttainedRowBinding
open P1OriginalVariableFourthProfileRegularity

abbrev BankPosition (records : List FourthWireRow) := Fin (records.length+1)

def rowAt (records : List FourthWireRow) (i : Fin records.length) : ProducerRow :=
  (records.get i).toProducerRow

theorem rowAt_mem_family (records : List FourthWireRow) (i : Fin records.length) :
    rowAt records i∈fourthFamily records := by
  apply (mem_fourthFamily_iff records _).mpr
  exact ⟨records.get i,List.get_mem _ _,rfl⟩

def slotEligible (records : List FourthWireRow) (licensed : ProducerRow→Prop)
    (t : Point) : BankPosition records→Prop :=
  Fin.cases True (fun i => producerEligible licensed (rowAt records i) t)

def slotValue (records : List FourthWireRow) (e seed : ℝ) (t : Point) :
    BankPosition records→ℝ :=
  Fin.cases seed (fun i => (rowAt records i).bufferedCandidate e t)

def winningSlots (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) : Finset (BankPosition records) :=
  Finset.univ.filter (fun i => slotEligible records licensed t i ∧
    slotValue records e seed t i=producerProfile4 e (fourthFamily records) licensed seed t)

theorem mem_winningSlots (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) (i : BankPosition records) :
    i∈winningSlots records e seed licensed t ↔
      slotEligible records licensed t i ∧ slotValue records e seed t i=
        producerProfile4 e (fourthFamily records) licensed seed t := by
  simp only [winningSlots,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Attainment is proved from the existing actual finite maximum and the
literal List.get witness. It is not a winner/ownership premise. -/
theorem winningSlots_nonempty (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) :
    (winningSlots records e seed licensed t).Nonempty := by
  rcases finiteMax_seed_or_winning_row (fourthFamily records)
    (fun r => producerEligible licensed r t) (fun r => r.bufferedCandidate e t) seed with hs | hr
  · refine ⟨0,(mem_winningSlots records e seed licensed t 0).mpr ?_⟩
    exact ⟨True.intro,hs.1.symm⟩
  · obtain ⟨r,hr,he,_hseed,_hdom,hvalue⟩ := hr
    obtain ⟨raw,hraw,hdecode⟩ := (mem_fourthFamily_iff records r).mp hr
    obtain ⟨i,hget⟩ := List.mem_iff_get.mp hraw
    refine ⟨i.succ,(mem_winningSlots records e seed licensed t i.succ).mpr ?_⟩
    simpa only [slotEligible,slotValue,Fin.cases_succ,rowAt,hget,hdecode] using
      (show producerEligible licensed r t ∧ r.bufferedCandidate e t=
        producerProfile4 e (fourthFamily records) licensed seed t from ⟨he,hvalue.symm⟩)

def owner (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) : BankPosition records :=
  (winningSlots records e seed licensed t).min'
    (winningSlots_nonempty records e seed licensed t)

theorem owner_mem (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) :
    owner records e seed licensed t∈winningSlots records e seed licensed t :=
  Finset.min'_mem _ _

theorem owner_le (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) (i : BankPosition records)
    (hi : i∈winningSlots records e seed licensed t) :
    owner records e seed licensed t≤i := Finset.min'_le _ _ hi

theorem owner_value (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) :
    slotValue records e seed t (owner records e seed licensed t)=
      producerProfile4 e (fourthFamily records) licensed seed t :=
  ((mem_winningSlots records e seed licensed t _).mp (owner_mem records e seed licensed t)).2

theorem eligible_slot_le_profile (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) (i : BankPosition records)
    (hi : slotEligible records licensed t i) :
    slotValue records e seed t i≤producerProfile4 e (fourthFamily records) licensed seed t := by
  revert hi
  refine Fin.cases ?_ (fun j => ?_) i
  · intro _hi
    exact finiteMax_seed_le (fourthFamily records) _ _ seed
  · intro hi
    exact finiteMax_row_le (fourthFamily records) _ _ seed (rowAt records j)
      (rowAt_mem_family records j) hi

theorem profile_le_of_slots (records : List FourthWireRow) (e seed upper : ℝ)
    (licensed : ProducerRow→Prop) (t : Point)
    (hslots : ∀ i,slotEligible records licensed t i→slotValue records e seed t i≤upper) :
    producerProfile4 e (fourthFamily records) licensed seed t≤upper := by
  apply finiteMax_le (fourthFamily records) _ _ seed upper (hslots 0 True.intro)
  intro r hr he
  obtain ⟨raw,hraw,hdecode⟩ := (mem_fourthFamily_iff records r).mp hr
  obtain ⟨i,hget⟩ := List.mem_iff_get.mp hraw
  have he' : slotEligible records licensed t i.succ := by
    simpa only [slotEligible,Fin.cases_succ,rowAt,hget,hdecode] using he
  have h := hslots i.succ he'
  simpa only [slotValue,Fin.cases_succ,rowAt,hget,hdecode] using h

/-- Explicit priority semantics, including tied records and repeated
identical rows: ownership is the least position among true maximizers. -/
theorem owner_eq_iff (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) (i : BankPosition records) :
    owner records e seed licensed t=i ↔
      i∈winningSlots records e seed licensed t ∧
        ∀ j∈winningSlots records e seed licensed t,i≤j := by
  constructor
  · intro hi
    subst i
    exact ⟨owner_mem records e seed licensed t,fun j hj => owner_le records e seed licensed t j hj⟩
  · rintro ⟨hi,hmin⟩
    exact le_antisymm (owner_le records e seed licensed t i hi)
      (hmin _ (owner_mem records e seed licensed t))

/-- Literal geometric gate description of the owner: weak dominance
over all eligible rows, but STRICT dominance over every earlier eligible
position. Thus tied box faces cannot be charged to two bank positions. -/
def orderedGates (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) (i : BankPosition records) : Prop :=
  slotEligible records licensed t i ∧
    (∀ j,slotEligible records licensed t j→slotValue records e seed t j≤slotValue records e seed t i) ∧
    (∀ j,j<i→slotEligible records licensed t j→slotValue records e seed t j<slotValue records e seed t i)

theorem owner_eq_iff_orderedGates (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) (i : BankPosition records) :
    owner records e seed licensed t=i ↔ orderedGates records e seed licensed t i := by
  constructor
  · intro ho
    have hwin := (mem_winningSlots records e seed licensed t i).mp
      (ho ▸ owner_mem records e seed licensed t)
    refine ⟨hwin.1,fun j hj => ?_,fun j hji hj => ?_⟩
    · rw [hwin.2]
      exact eligible_slot_le_profile records e seed licensed t j hj
    · have hle : slotValue records e seed t j≤slotValue records e seed t i := by
        rw [hwin.2]
        exact eligible_slot_le_profile records e seed licensed t j hj
      apply lt_of_le_of_ne hle
      intro heq
      have hjwin := (mem_winningSlots records e seed licensed t j).mpr ⟨hj,heq.trans hwin.2⟩
      have hprio := owner_le records e seed licensed t j hjwin
      rw [ho] at hprio
      exact (not_le_of_gt hji) hprio
  · rintro ⟨hi,hdom,hstrict⟩
    have hv : slotValue records e seed t i=producerProfile4 e (fourthFamily records) licensed seed t :=
      le_antisymm (eligible_slot_le_profile records e seed licensed t i hi)
        (profile_le_of_slots records e seed _ licensed t hdom)
    apply (owner_eq_iff records e seed licensed t i).mpr
    refine ⟨(mem_winningSlots records e seed licensed t i).mpr ⟨hi,hv⟩,?_⟩
    intro j hj
    apply le_of_not_gt
    intro hji
    have hjw := (mem_winningSlots records e seed licensed t j).mp hj
    have hs := hstrict j hji hjw.1
    rw [hjw.2,hv] at hs
    exact lt_irrefl _ hs

/-- The entire non-improving branch is retained, including eligible rows
that lose to or tie the original seed. No positivity is assumed. -/
theorem owner_zero_iff (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) :
    owner records e seed licensed t=0 ↔
      producerProfile4 e (fourthFamily records) licensed seed t=seed := by
  constructor
  · intro howner
    have hv := owner_value records e seed licensed t
    rw [howner] at hv
    exact hv.symm
  · intro hseed
    apply (owner_eq_iff records e seed licensed t 0).mpr
    exact ⟨(mem_winningSlots records e seed licensed t 0).mpr ⟨True.intro,hseed.symm⟩,
      fun _ _ => Fin.zero_le _⟩

theorem owned_row_is_actual_source (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (t : Point) (i : Fin records.length)
    (howner : owner records e seed licensed t=i.succ) :
    rowAt records i∈fourthFamily records ∧ licensed (rowAt records i) ∧
      t∈(rowAt records i).box ∧
      producerProfile4 e (fourthFamily records) licensed seed t=
        (rowAt records i).bufferedCandidate e t := by
  have hm := (mem_winningSlots records e seed licensed t i.succ).mp
    (howner ▸ owner_mem records e seed licensed t)
  exact ⟨rowAt_mem_family records i,hm.1.1,hm.1.2,hm.2.symm⟩

def ownedRegion (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (R : Set Point) (i : BankPosition records) : Set Point :=
  {t | t∈R ∧ owner records e seed licensed t=i}

theorem continuous_slotValue (records : List FourthWireRow) (e seed : ℝ)
    (i : BankPosition records) : Continuous (fun t => slotValue records e seed t i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · exact continuous_bufferedCandidate (rowAt records j) e

theorem measurableSet_slotEligible (records : List FourthWireRow)
    (licensed : ProducerRow→Prop) (i : BankPosition records) :
    MeasurableSet {t : Point | slotEligible records licensed t i} := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact MeasurableSet.univ
  · by_cases hl : licensed (rowAt records j)
    · have hbox : IsClosed (rowAt records j).box := by
        change IsClosed {t : Point | (∀ k,((rowAt records j).lower k:ℝ)≤t k) ∧
          ∀ k,t k≤((rowAt records j).upper k:ℝ)}
        simp only [setOf_and,setOf_forall]
        exact (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)).inter
          (isClosed_iInter fun k => isClosed_le (continuous_apply k) continuous_const)
      simpa only [slotEligible,Fin.cases_succ,producerEligible,hl,true_and] using hbox.measurableSet
    · simpa only [slotEligible,Fin.cases_succ,producerEligible,hl,false_and,setOf_false] using
        MeasurableSet.empty (α:=Point)

theorem measurableSet_owner (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (i : BankPosition records) :
    MeasurableSet {t : Point | owner records e seed licensed t=i} := by
  have hweak (j : BankPosition records) : MeasurableSet {t : Point |
      slotEligible records licensed t j→slotValue records e seed t j≤slotValue records e seed t i} := by
    have heq : {t : Point | slotEligible records licensed t j→
        slotValue records e seed t j≤slotValue records e seed t i}=
        {t : Point | slotEligible records licensed t j}ᶜ ∪
          {t : Point | slotValue records e seed t j≤slotValue records e seed t i} := by
      ext t
      simp only [mem_setOf_eq,mem_union,mem_compl_iff,imp_iff_not_or]
    rw [heq]
    exact (measurableSet_slotEligible records licensed j).compl.union
      (isClosed_le (continuous_slotValue records e seed j) (continuous_slotValue records e seed i)).measurableSet
  have hstrict (j : BankPosition records) : MeasurableSet {t : Point |
      j<i→slotEligible records licensed t j→slotValue records e seed t j<slotValue records e seed t i} := by
    by_cases hji : j<i
    · have heq : {t : Point | j<i→slotEligible records licensed t j→
          slotValue records e seed t j<slotValue records e seed t i}=
          {t : Point | slotEligible records licensed t j}ᶜ ∪
            {t : Point | slotValue records e seed t j<slotValue records e seed t i} := by
        ext t
        simp only [mem_setOf_eq,mem_union,mem_compl_iff,hji,true_implies,imp_iff_not_or]
      rw [heq]
      exact (measurableSet_slotEligible records licensed j).compl.union
        (isOpen_lt (continuous_slotValue records e seed j) (continuous_slotValue records e seed i)).measurableSet
    · simpa only [hji,false_implies,setOf_true] using MeasurableSet.univ (α:=Point)
  have heq : {t : Point | owner records e seed licensed t=i}=
      {t : Point | slotEligible records licensed t i} ∩
        (⋂ j : BankPosition records,{t : Point | slotEligible records licensed t j→
          slotValue records e seed t j≤slotValue records e seed t i}) ∩
        (⋂ j : BankPosition records,{t : Point | j<i→slotEligible records licensed t j→
          slotValue records e seed t j<slotValue records e seed t i}) := by
    ext t
    simp only [mem_setOf_eq,mem_inter_iff,mem_iInter,owner_eq_iff_orderedGates,orderedGates,and_assoc]
  rw [heq]
  exact ((measurableSet_slotEligible records licensed i).inter (MeasurableSet.iInter hweak)).inter
    (MeasurableSet.iInter hstrict)

theorem measurableSet_ownedRegion (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (R : Set Point) (hR : MeasurableSet R) (i : BankPosition records) :
    MeasurableSet (ownedRegion records e seed licensed R i) :=
  hR.inter (measurableSet_owner records e seed licensed i)

/-- Full geometric coverage: fallback, overlaps and every closed face
are included; no whole-payload geometry-check witness is needed. -/
theorem ownedRegion_cover (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (R : Set Point) :
    (⋃ i : BankPosition records,ownedRegion records e seed licensed R i)=R := by
  ext t
  simp only [mem_iUnion,ownedRegion,mem_setOf_eq]
  exact ⟨fun ⟨_,ht,_⟩ => ht,fun ht => ⟨owner records e seed licensed t,ht,rfl⟩⟩

theorem ownedRegion_disjoint (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (R : Set Point) {i j : BankPosition records} (hij : i≠j) :
    Disjoint (ownedRegion records e seed licensed R i) (ownedRegion records e seed licensed R j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  exact hij (hi.2.symm.trans hj.2)

theorem ownedRegion_row_subset_box (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (R : Set Point) (i : Fin records.length) :
    ownedRegion records e seed licensed R i.succ⊆(rowAt records i).box := by
  intro t ht
  exact (owned_row_is_actual_source records e seed licensed t i ht.2).2.2.1

/-- Signed pointwise conservation, with exact coefficient one. This
applies to the negative branch too; it is not a positive-saving estimate. -/
theorem indicator_eq_sum_owned {A : Type*} [AddCommMonoid A]
    (records : List FourthWireRow) (e seed : ℝ) (licensed : ProducerRow→Prop)
    (R : Set Point) (f : Point→A) (t : Point) :
    R.indicator f t=
      ∑ i : BankPosition records,(ownedRegion records e seed licensed R i).indicator f t := by
  symm
  rw [Finset.sum_eq_single (owner records e seed licensed t)]
  · by_cases ht : t∈R
    · rw [indicator_of_mem ht,indicator_of_mem (show t∈ownedRegion records e seed licensed R
        (owner records e seed licensed t) from ⟨ht,rfl⟩)]
    · rw [indicator_of_notMem ht,indicator_of_notMem
        (show t∉ownedRegion records e seed licensed R (owner records e seed licensed t)
          from fun h => ht h.1)]
  · intro i _hi hine
    apply indicator_of_notMem
    intro ht
    exact hine ht.2.symm
  · simp

theorem finite_signed_sum_eq_owned_sums {A : Type*} [AddCommMonoid A]
    (records : List FourthWireRow) (e seed : ℝ) (licensed : ProducerRow→Prop)
    (R : Set Point) (points : Finset Point) (f : Point→A) :
    (∑ t∈points,R.indicator f t)=
      ∑ i : BankPosition records,∑ t∈points,
        (ownedRegion records e seed licensed R i).indicator f t := by
  simp_rw [indicator_eq_sum_owned records e seed licensed R f]
  rw [Finset.sum_comm]

/-- Exact integral disintegration of the WHOLE source, with no discarded
unselected region and no nonnegativity condition on the integrand. -/
theorem signed_integral_eq_owned_integrals (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow→Prop) (R : Set Point) (hR : MeasurableSet R)
    (f : Point→ℝ) (hf : IntegrableOn f R) :
    (∫ t in R,f t)=∑ i : BankPosition records,∫ t in ownedRegion records e seed licensed R i,f t := by
  have hi (i : BankPosition records) : Integrable
      ((ownedRegion records e seed licensed R i).indicator f) :=
    (integrable_indicator_iff (measurableSet_ownedRegion records e seed licensed R hR i)).mpr
      (hf.mono_set (fun _ ht => ht.1))
  calc
    (∫ t in R,f t)=(∫ t,R.indicator f t) := (integral_indicator hR).symm
    _ = ∫ t,∑ i : BankPosition records,(ownedRegion records e seed licensed R i).indicator f t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (indicator_eq_sum_owned records e seed licensed R f)
    _ = ∑ i : BankPosition records,∫ t,(ownedRegion records e seed licensed R i).indicator f t :=
      integral_finset_sum _ (fun i _ => hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact integral_indicator (measurableSet_ownedRegion records e seed licensed R hR i)

/-- The positional owner is bound to the exact original rank-four
history, its inherited raw-Q3 seed and its original e/chi/omega. -/
theorem original_history_level_eq_owner (records : List FourthWireRow)
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (licensed : ProducerRow→Prop)
    (history : List ℕ) (hlen : history.length=4) :
    producerLevel4 e chi m omega N (fourthFamily records) licensed history=
      N ^ slotValue records e (seedExponent e chi m omega N history)
        (primeHistoryLogCoordinates N 4 history)
        (owner records e (seedExponent e chi m omega N history) licensed
          (primeHistoryLogCoordinates N 4 history)) := by
  rw [owner_value]
  change N ^ (if history.length=4 then _ else _)=_
  rw [if_pos hlen]
  rfl

theorem original_history_seed_branch (records : List FourthWireRow)
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (licensed : ProducerRow→Prop)
    (history : List ℕ) (hlen : history.length=4)
    (howner : owner records e (seedExponent e chi m omega N history) licensed
      (primeHistoryLogCoordinates N 4 history)=0) :
    producerLevel4 e chi m omega N (fourthFamily records) licensed history=
      HistoricalThirdCoarse.frozenLevel e chi m omega N history := by
  rw [original_history_level_eq_owner records e chi m omega N licensed history hlen,howner]
  exact (frozenLevel_eq_rpow_seed e chi m omega N history).symm

end
end ImbalancedChen.OriginalFullFourthPriorityOwnership20261026a
