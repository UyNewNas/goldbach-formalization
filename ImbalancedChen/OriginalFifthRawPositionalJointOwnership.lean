import ImbalancedChen.OriginalFifthParentSignedSaving

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The fifth maximum is refined by ORIGINAL RAW LIST positions. At one fixed
mesh owner, each raw box decodes to at most one row; repeated raw records
remain distinct positions. Position zero is the genuine inherited fourth
parentValue. The first position among eligible maximizers owns a point,
so the parent wins every tie and earlier raw records win later ties.

The fourth positional parent and fifth positional winner give an exact
joint measurable partition, retaining the signed whole source. This does
not turn raw delta/A/B statistics into an archived dynamic-parent history
or a complete original 22-successor license.
-/

namespace ImbalancedChen.OriginalFifthRawPositionalJointOwnership20261026b

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open P1OriginalProducerAttainedRowBinding
open P1ActualVariableFourthFifthCellTestLimit
open OriginalFifthInheritedParentGeometry20261026b

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)
abbrev ParentPosition (records : List FourthWireRow) :=
  OriginalFullFourthPriorityOwnership20261026a.BankPosition records
abbrev FifthPosition (records : List FifthWireRow) := Fin (records.length + 1)

def decodeAt (raw : FifthWireRow) (m : ℕ) (j : Label5 m) : FifthRow m :=
  ⟨j, maskSlots 5 raw.mask.toNat⟩

theorem decodeAt_eq_of_mem (raw : FifthWireRow) (m : ℕ) (j : Label5 m)
    (r : FifthRow m) (hr : r ∈ decodeFifthRows raw m) (hj : r.cell = j) :
    decodeAt raw m j = r := by
  obtain ⟨_hg, _hm, k, _hk, rfl⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
  cases hj
  rfl

def rawRowAt (records : List FifthWireRow) (m : ℕ) (j : Label5 m)
    (k : Fin records.length) : FifthRow m := decodeAt (records.get k) m j

def rawEligible (records : List FifthWireRow) (e : ℚ) (m : ℕ) (j : Label5 m)
    (k : Fin records.length) : Prop :=
  rawRowAt records m j k ∈ decodeFifthRows (records.get k) m ∧
    gateCheck e m (rawRowAt records m j k) = true

theorem rawRowAt_mem_family (records : List FifthWireRow) (m : ℕ) (j : Label5 m)
    (k : Fin records.length) (hk : rawRowAt records m j k ∈ decodeFifthRows (records.get k) m) :
    rawRowAt records m j k ∈ fifthFamily records m :=
  (mem_fifthFamily_iff records m _).mpr ⟨records.get k, List.get_mem _ _, hk⟩

/-- Exact surjection from the literal ordered records to the eligible
policy rows. This is where duplicate raw positions are preserved. -/
theorem family_owner_has_raw_position (records : List FifthWireRow) (e : ℚ)
    (m : ℕ) (j : Label5 m) (r : FifthRow m)
    (hr : r ∈ fifthFamily records m) (he : ownerEligible e m j r) :
    ∃ k : Fin records.length, rawRowAt records m j k = r ∧ rawEligible records e m j k := by
  obtain ⟨raw, hraw, hd⟩ := (mem_fifthFamily_iff records m r).mp hr
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hraw
  have heq : rawRowAt records m j k = r := by
    unfold rawRowAt
    rw [hk]
    exact decodeAt_eq_of_mem raw m j r hd he.1
  refine ⟨k, heq, ?_⟩
  constructor
  · rw [heq, hk]
    exact hd
  · simpa only [heq] using he.2

def slotEligible (records : List FifthWireRow) (e : ℚ) (m : ℕ) (j : Label5 m) :
    FifthPosition records → Prop :=
  Fin.cases True (rawEligible records e m j)

def slotValue (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) : FifthPosition records5 → ℝ :=
  Fin.cases (parentValue records4 e m j parent t)
    (fun k => candidate (e : ℝ) (rawRowAt records5 m j k).selected t)

theorem eligible_slot_le_profile (records4 : List FourthWireRow)
    (records5 : List FifthWireRow) (e : ℚ) (m : ℕ) (j : Label5 m)
    (parent : ParentPosition records4) (t : Point5) (k : FifthPosition records5)
    (hk : slotEligible records5 e m j k) :
    slotValue records4 records5 e m j parent t k ≤ nextFromParent records4 records5 e m j parent t := by
  revert hk
  refine Fin.cases ?_ (fun k => ?_) k
  · intro _hk
    exact finiteMax_seed_le _ _ _ _
  · intro hk
    exact finiteMax_row_le _ _ _ _ (rawRowAt records5 m j k)
      (rawRowAt_mem_family records5 m j k hk.1) ⟨rfl, hk.2⟩

theorem profile_le_of_slots (records4 : List FourthWireRow)
    (records5 : List FifthWireRow) (e : ℚ) (m : ℕ) (j : Label5 m)
    (parent : ParentPosition records4) (t : Point5) (upper : ℝ)
    (hslots : ∀ k, slotEligible records5 e m j k → slotValue records4 records5 e m j parent t k ≤ upper) :
    nextFromParent records4 records5 e m j parent t ≤ upper := by
  apply finiteMax_le _ _ _ _ upper (hslots 0 True.intro)
  intro r hr he
  obtain ⟨k, hk, hel⟩ := family_owner_has_raw_position records5 e m j r hr he
  have h := hslots k.succ hel
  simpa only [slotValue, Fin.cases_succ, hk] using h

def winningSlots (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) : Finset (FifthPosition records5) :=
  Finset.univ.filter (fun k => slotEligible records5 e m j k ∧
    slotValue records4 records5 e m j parent t k = nextFromParent records4 records5 e m j parent t)

theorem mem_winningSlots (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) (k : FifthPosition records5) :
    k ∈ winningSlots records4 records5 e m j parent t ↔
      slotEligible records5 e m j k ∧ slotValue records4 records5 e m j parent t k =
        nextFromParent records4 records5 e m j parent t := by
  simp only [winningSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem winningSlots_nonempty (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4) (t : Point5) :
    (winningSlots records4 records5 e m j parent t).Nonempty := by
  rcases finiteMax_seed_or_winning_row (fifthFamily records5 m) (ownerEligible e m j)
    (fun r => candidate (e : ℝ) r.selected t) (parentValue records4 e m j parent t) with hs | hr
  · refine ⟨0, (mem_winningSlots records4 records5 e m j parent t 0).mpr ?_⟩
    exact ⟨True.intro, hs.1.symm⟩
  · obtain ⟨r, hr, he, _hseed, _hdom, hv⟩ := hr
    obtain ⟨k, hk, hel⟩ := family_owner_has_raw_position records5 e m j r hr he
    refine ⟨k.succ, (mem_winningSlots records4 records5 e m j parent t k.succ).mpr ?_⟩
    refine ⟨hel, ?_⟩
    simpa only [slotValue, Fin.cases_succ, hk] using hv.symm

def fifthOwner (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) : FifthPosition records5 :=
  (winningSlots records4 records5 e m j parent t).min'
    (winningSlots_nonempty records4 records5 e m j parent t)

theorem owner_mem (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4) (t : Point5) :
    fifthOwner records4 records5 e m j parent t ∈ winningSlots records4 records5 e m j parent t :=
  Finset.min'_mem _ _

theorem owner_le (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) (k : FifthPosition records5)
    (hk : k ∈ winningSlots records4 records5 e m j parent t) :
    fifthOwner records4 records5 e m j parent t ≤ k := Finset.min'_le _ _ hk

theorem owner_value (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4) (t : Point5) :
    slotValue records4 records5 e m j parent t (fifthOwner records4 records5 e m j parent t) =
      nextFromParent records4 records5 e m j parent t :=
  ((mem_winningSlots records4 records5 e m j parent t _).mp
    (owner_mem records4 records5 e m j parent t)).2

theorem owner_eq_iff_first_maximizer (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) (k : FifthPosition records5) :
    fifthOwner records4 records5 e m j parent t = k ↔
      k ∈ winningSlots records4 records5 e m j parent t ∧
        ∀ l ∈ winningSlots records4 records5 e m j parent t, k ≤ l := by
  constructor
  · intro hk
    subst k
    exact ⟨owner_mem records4 records5 e m j parent t,
      fun l hl => owner_le records4 records5 e m j parent t l hl⟩
  · rintro ⟨hk, hmin⟩
    exact le_antisymm (owner_le records4 records5 e m j parent t k hk)
      (hmin _ (owner_mem records4 records5 e m j parent t))

theorem parent_wins_tie (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4) (t : Point5) :
    fifthOwner records4 records5 e m j parent t = 0 ↔
      nextFromParent records4 records5 e m j parent t = parentValue records4 e m j parent t := by
  constructor
  · intro ho
    have hv := owner_value records4 records5 e m j parent t
    rw [ho] at hv
    exact hv.symm
  · intro hs
    apply (owner_eq_iff_first_maximizer records4 records5 e m j parent t 0).mpr
    exact ⟨(mem_winningSlots records4 records5 e m j parent t 0).mpr ⟨True.intro, hs.symm⟩,
      fun _ _ => Fin.zero_le _⟩

theorem continuous_slotValue (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (k : FifthPosition records5) : Continuous (fun t => slotValue records4 records5 e m j parent t k) := by
  refine Fin.cases ?_ (fun l => ?_) k
  · exact (OriginalFullFourthPriorityOwnership20261026a.continuous_slotValue records4
      (e : ℝ) (selectedSeed e m j) parent).comp firstFour.continuous
  · have hsum : Continuous (fun t : Point5 => ∑ q ∈ (rawRowAt records5 m j l).selected, t q) := by
      fun_prop
    simpa only [slotValue, Fin.cases_succ, candidate, envelope_eq_v] using
      (VariableEnvelope.continuous_v.comp hsum).sub continuous_const

theorem winning_iff_dominates (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) (k : FifthPosition records5) :
    k ∈ winningSlots records4 records5 e m j parent t ↔
      slotEligible records5 e m j k ∧ ∀ l, slotEligible records5 e m j l →
        slotValue records4 records5 e m j parent t l ≤ slotValue records4 records5 e m j parent t k := by
  rw [mem_winningSlots]
  constructor
  · rintro ⟨hk, hv⟩
    exact ⟨hk, fun l hl => hv.symm ▸ eligible_slot_le_profile records4 records5 e m j parent t l hl⟩
  · rintro ⟨hk, hdom⟩
    exact ⟨hk, le_antisymm (eligible_slot_le_profile records4 records5 e m j parent t k hk)
      (profile_le_of_slots records4 records5 e m j parent t _ hdom)⟩

theorem measurableSet_winning (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (k : FifthPosition records5) :
    MeasurableSet {t : Point5 | k ∈ winningSlots records4 records5 e m j parent t} := by
  by_cases hk : slotEligible records5 e m j k
  · have hl (l : FifthPosition records5) : MeasurableSet {t : Point5 |
        slotEligible records5 e m j l → slotValue records4 records5 e m j parent t l ≤
          slotValue records4 records5 e m j parent t k} := by
      by_cases hel : slotEligible records5 e m j l
      · simpa only [hel, true_implies] using
          (isClosed_le (continuous_slotValue records4 records5 e m j parent l)
            (continuous_slotValue records4 records5 e m j parent k)).measurableSet
      · simpa only [hel, false_implies, setOf_true] using MeasurableSet.univ (α := Point5)
    have heq : {t : Point5 | k ∈ winningSlots records4 records5 e m j parent t} =
        ⋂ l : FifthPosition records5, {t : Point5 | slotEligible records5 e m j l →
          slotValue records4 records5 e m j parent t l ≤ slotValue records4 records5 e m j parent t k} := by
      ext t
      simp only [mem_setOf_eq, mem_iInter, winning_iff_dominates, hk, true_and]
    rw [heq]
    exact MeasurableSet.iInter hl
  · have heq : {t : Point5 | k ∈ winningSlots records4 records5 e m j parent t} = ∅ := by
      ext t
      simp only [mem_setOf_eq, winning_iff_dominates, hk, false_and, mem_empty_iff_false]
    rw [heq]
    exact MeasurableSet.empty

theorem measurableSet_fifthOwner (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (k : FifthPosition records5) :
    MeasurableSet {t : Point5 | fifthOwner records4 records5 e m j parent t = k} := by
  have hl (l : FifthPosition records5) : MeasurableSet {t : Point5 |
      l < k → l ∉ winningSlots records4 records5 e m j parent t} := by
    by_cases hlk : l < k
    · simpa only [hlk, true_implies] using
        (measurableSet_winning records4 records5 e m j parent l).compl
    · simpa only [hlk, false_implies, setOf_true] using MeasurableSet.univ (α := Point5)
  have heq : {t : Point5 | fifthOwner records4 records5 e m j parent t = k} =
      {t : Point5 | k ∈ winningSlots records4 records5 e m j parent t} ∩
        ⋂ l : FifthPosition records5,
          {t : Point5 | l < k → l ∉ winningSlots records4 records5 e m j parent t} := by
    ext t
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, owner_eq_iff_first_maximizer]
    constructor
    · rintro ⟨hk, hmin⟩
      exact ⟨hk, fun l hl hwin => (not_le_of_gt hl) (hmin l hwin)⟩
    · rintro ⟨hk, hprev⟩
      exact ⟨hk, fun l hl => le_of_not_gt (fun hlk => hprev l hlk hl)⟩
  rw [heq]
  exact (measurableSet_winning records4 records5 e m j parent k).inter (MeasurableSet.iInter hl)

abbrev JointPosition (records4 : List FourthWireRow) (records5 : List FifthWireRow) :=
  ParentPosition records4 × FifthPosition records5

def jointOwner (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (t : Point5) : JointPosition records4 records5 :=
  let p := parentOwner records4 e m j licensed t
  (p, fifthOwner records4 records5 e m j p t)

def jointRegion (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (p : JointPosition records4 records5) : Set Point5 :=
  parentRegion records4 e m j licensed R p.1 ∩
    {t | fifthOwner records4 records5 e m j p.1 t = p.2}

theorem mem_jointRegion (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (p : JointPosition records4 records5) (t : Point5) :
    t ∈ jointRegion records4 records5 e m j licensed R p ↔
      t ∈ R ∧ jointOwner records4 records5 e m j licensed t = p := by
  constructor
  · rintro ⟨⟨ht, hp⟩, hk⟩
    refine ⟨ht, Prod.ext hp ?_⟩
    change fifthOwner records4 records5 e m j (parentOwner records4 e m j licensed t) t = p.2
    rw [hp]
    exact hk
  · rintro ⟨ht, hp⟩
    have hfirst := congrArg Prod.fst hp
    have hsecond := congrArg Prod.snd hp
    change parentOwner records4 e m j licensed t = p.1 at hfirst
    change fifthOwner records4 records5 e m j (parentOwner records4 e m j licensed t) t = p.2 at hsecond
    rw [hfirst] at hsecond
    refine ⟨⟨ht, hfirst⟩, ?_⟩
    exact hsecond

theorem measurableSet_jointRegion (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (hR : MeasurableSet R) (p : JointPosition records4 records5) :
    MeasurableSet (jointRegion records4 records5 e m j licensed R p) :=
  (measurableSet_parentRegion records4 e m j licensed R hR p.1).inter
    (measurableSet_fifthOwner records4 records5 e m j p.1 p.2)

theorem jointRegion_cover (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop) (R : Set Point5) :
    (⋃ p : JointPosition records4 records5, jointRegion records4 records5 e m j licensed R p) = R := by
  ext t
  simp only [mem_iUnion, mem_jointRegion]
  exact ⟨fun ⟨_, ht, _⟩ => ht, fun ht => ⟨jointOwner records4 records5 e m j licensed t, ht, rfl⟩⟩

theorem jointRegion_disjoint (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop) (R : Set Point5)
    {p q : JointPosition records4 records5} (hpq : p ≠ q) :
    Disjoint (jointRegion records4 records5 e m j licensed R p)
      (jointRegion records4 records5 e m j licensed R q) := by
  apply Set.disjoint_left.mpr
  intro t hp hq
  exact hpq (((mem_jointRegion records4 records5 e m j licensed R p t).mp hp).2.symm.trans
    ((mem_jointRegion records4 records5 e m j licensed R q t).mp hq).2)

/-- An owned raw successor retains the original raw box, selected-slot
mask, and all its original whole-cell full/selected square gates. -/
theorem owned_raw_geometry (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (k : Fin records5.length) (hk : fifthOwner records4 records5 e m j parent t = k.succ) :
    t ∈ (records5.get k).originalBox ∧
      (1 / 2 : ℝ) < candidate (e : ℝ) (rawRowAt records5 m j k).selected t ∧
      (∀ q, prefixSquareExpr t q < candidate (e : ℝ) (rawRowAt records5 m j k).selected t) ∧
      (∀ q ∉ (rawRowAt records5 m j k).selected,
        selectedSquareExpr (rawRowAt records5 m j k).selected t q <
          candidate (e : ℝ) (rawRowAt records5 m j k).selected t) := by
  have hw := (mem_winningSlots records4 records5 e m j parent t k.succ).mp
    (hk ▸ owner_mem records4 records5 e m j parent t)
  have hd := decodeFifthRows_source_geometry (records5.get k) m
    (rawRowAt records5 m j k) hw.1.1 t ht
  exact ⟨hd.2.2.2, gateCheck_sound e m (rawRowAt records5 m j k) t hw.1.2 ht⟩

theorem indicator_eq_sum_joint (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (f : Point5 → ℝ) (t : Point5) :
    R.indicator f t = ∑ p : JointPosition records4 records5,
      (jointRegion records4 records5 e m j licensed R p).indicator f t := by
  symm
  rw [Finset.sum_eq_single (jointOwner records4 records5 e m j licensed t)]
  · by_cases ht : t ∈ R
    · rw [indicator_of_mem ht, indicator_of_mem
        ((mem_jointRegion records4 records5 e m j licensed R _ t).mpr ⟨ht, rfl⟩)]
    · rw [indicator_of_notMem ht, indicator_of_notMem
        (show t ∉ jointRegion records4 records5 e m j licensed R
          (jointOwner records4 records5 e m j licensed t) from
            fun h => ht ((mem_jointRegion records4 records5 e m j licensed R _ t).mp h).1)]
  · intro p _hp hpne
    apply indicator_of_notMem
    intro ht
    exact hpne ((mem_jointRegion records4 records5 e m j licensed R p t).mp ht).2.symm
  · simp

/-- Exact signed joint conservation, with one copy of every point. It
applies to the actual fifth saving as well as arbitrary signed tests. -/
theorem signed_integral_eq_joint_integrals (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (hR : MeasurableSet R) (f : Point5 → ℝ) (hf : IntegrableOn f R) :
    (∫ t in R, f t) = ∑ p : JointPosition records4 records5,
      ∫ t in jointRegion records4 records5 e m j licensed R p, f t := by
  have hi (p : JointPosition records4 records5) :
      Integrable ((jointRegion records4 records5 e m j licensed R p).indicator f) :=
    (integrable_indicator_iff (measurableSet_jointRegion records4 records5 e m j licensed R hR p)).mpr
      (hf.mono_set (fun t ht => ((mem_jointRegion records4 records5 e m j licensed R p t).mp ht).1))
  calc
    (∫ t in R, f t) = (∫ t, R.indicator f t) := (integral_indicator hR).symm
    _ = ∫ t, ∑ p : JointPosition records4 records5,
        (jointRegion records4 records5 e m j licensed R p).indicator f t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (indicator_eq_sum_joint records4 records5 e m j licensed R f)
    _ = ∑ p : JointPosition records4 records5,
        ∫ t, (jointRegion records4 records5 e m j licensed R p).indicator f t :=
      integral_finset_sum _ (fun p _ => hi p)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact integral_indicator (measurableSet_jointRegion records4 records5 e m j licensed R hR p)

def jointSavingKernel (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (p : JointPosition records4 records5) (t : Point5) : ℝ :=
  (primeOwnCubeGatedProfile (slotValue records4 records5 e m j p.1 t p.2) t -
    primeOwnCubeGatedProfile (parentValue records4 e m j p.1 t) t) * ∏ q, 1 / t q

/-- The canonical fifth saving uses precisely the positional winner and
its inherited fourth parent on each joint piece, even on equality faces. -/
theorem actualKernel_eq_jointSavingKernel
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (R : Set Point5) (p : JointPosition records4 records5)
    (t : Point5) (ht : t ∈ jointRegion records4 records5 e m j licensed R p)
    (hmesh : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    P1ActualVariableFifthPositiveCellLimit.variableCellKernel e chi m omega j
        (fourthFamily records4) licensed (fifthFamily records5 m) t =
      jointSavingKernel records4 records5 e m j p t := by
  rw [OriginalFifthParentSignedSaving20261026b.actualKernel_eq_parentSavingKernel
    records4 records5 e chi m omega J5 j hj licensed t hmesh p.1 ht.1.2]
  have hv := owner_value records4 records5 e m j p.1 t
  rw [ht.2] at hv
  unfold OriginalFifthParentSignedSaving20261026b.parentSavingKernel jointSavingKernel
  rw [hv]

/-- Complete actual cutoff identity, now refined jointly by original
fourth and fifth positions. No signed charge or fallback is omitted. -/
theorem actual_cutoff_saving_eq_joint_savings
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) :
    P1ActualVariableFifthPositiveCellLimit.variableCellIntegral e chi m omega a j
        (fourthFamily records4) licensed (fifthFamily records5 m) =
      ∑ p : JointPosition records4 records5,
        ∫ t in jointRegion records4 records5 e m j licensed
          (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) p,
          jointSavingKernel records4 records5 e m j p t := by
  unfold P1ActualVariableFifthPositiveCellLimit.variableCellIntegral
  rw [signed_integral_eq_joint_integrals records4 records5 e m j licensed _
    (P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j) _
    (P1ActualVariableFifthPositiveCellLimit.integrableOn_actualVariable5_kernel
      e chi m omega a ha J5 j hj (fourthFamily records4) licensed (fifthFamily records5 m))]
  apply Finset.sum_congr rfl
  intro p _hp
  apply setIntegral_congr_fun (measurableSet_jointRegion records4 records5 e m j licensed _
    (P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j) p)
  intro t ht
  exact actualKernel_eq_jointSavingKernel records4 records5 e chi m omega J5 j hj licensed
    _ p t ht ht.1.1.2.1

end
end ImbalancedChen.OriginalFifthRawPositionalJointOwnership20261026b
