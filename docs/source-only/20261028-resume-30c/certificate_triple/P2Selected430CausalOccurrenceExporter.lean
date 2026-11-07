import ImbalancedChen.P2Selected430LiteralActionData
import ImbalancedChen.P2EnhancedW1FiniteActionBankPayment
import ImbalancedChen.P2PhysicalFrozenPrefixHistory

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The scalar choices below are computed from the literal seed-only430 producer:
all candidate values use the same previous table; only retention maxima read
the mutable decision. A row records its original base, points, individual
floor weights, divisor and target indices. No copied248/312/430 array is an
input. The actual numerical equality to stored430 entries is not asserted.

The physical exporter reconstructs History.start/advance from raw integer
prefixes. It emits an occurrence only after testing computed parent admission,
old-word/product/Q alignment, actual alpha-independent parent-window conditions,
actual W1 target/ceiling, residual lower floor, and query-cell membership.
These finite physical tests are not the analytic positive-product/K licence.
Different prefixes, rounds and query cells retain separate occurrences.
-/
namespace ImbalancedChen.P2Selected430CausalOccurrenceExporter
noncomputable section
open Finset Set
open scoped Classical BigOperators
open P2Selected430LiteralActionData (Row rows logWeights q)
open P2EnhancedW1FiniteActionBankPayment
  (W1Occurrence markedBankMass markedBankMass_theta_payment)
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P2PhysicalFrozenPrefixHistory (History start advance constructed_retained_gates)
open P2EnhancedLowerPhysicalNode (PhysicalNode word residual fullGates selectedGates)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime parentWindow)
open P5OriginalActionMassBound (W1Target W1Anchor)

abbrev Table := Bool → Fin 200 → ℤ

def read (old : Table) (upper : Bool) (j : ℕ) : ℤ :=
  if hj : j < 200 then old upper ⟨j,hj⟩ else 0

def seed : Table := fun upper i =>
  if upper = true ∧ i.val < 60 then 2327*q/100000 else 0

def suffix (old : Table) (upper : Bool) (k : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (200-k),
    read old upper (k+r) * (if hj : k+r < 200 then logWeights ⟨k+r,hj⟩ else 0) / q

def candidate (old : Table) (a : Row) : ℤ :=
  a.base + ((a.points.map (fun p => read old true p.1 * p.2)).sum +
    (a.lowerWeights.map (fun p => read old false p.1 * p.2 / q)).sum +
    (a.upperWeights.map (fun p => read old true p.1 * p.2 / q)).sum) /
      (a.divisor : ℤ)

inductive Choice where
  | retained
  | buchstab
  | bank (slot : Fin 106)
  deriving DecidableEq

structure Decision where
  numerator : ℤ
  choice : Choice

def offer (d : Decision) (v : ℤ) (choice : Choice) : Decision :=
  if d.numerator < v then ⟨v,choice⟩ else d

theorem offer_numerator (d : Decision) (v : ℤ) (choice : Choice) :
    (offer d v choice).numerator = max d.numerator v := by
  by_cases h : d.numerator < v
  · simp [offer,h,max_eq_right h.le]
  · simp [offer,h,max_eq_left (le_of_not_gt h)]

def ordinaryDecision (old : Table) (upper : Bool) (i : Fin 200) : Decision :=
  let retained : Decision := ⟨old upper i,.retained⟩
  if 50 ≤ i.val then
    offer retained (if upper then suffix old false (max 50 (i.val-49))
      else suffix old true (i.val-49)) .buchstab
  else retained

def offerRow (old : Table) (i : Fin 200) (d : Decision) (k : Fin 106) : Decision :=
  if i.val ∈ (rows k).targets then offer d (candidate old (rows k)) (.bank k) else d

def scan (old : Table) (i : Fin 200) : List (Fin 106) → Decision → Decision
  | [],d => d
  | k::ks,d => scan old i ks (offerRow old i d k)


/-- Erasing provenance gives exactly the producer's left-to-right
retention maximum, whose every candidate still reads the same old table. -/
theorem scan_numerator (old : Table) (i : Fin 200)
    (ks : List (Fin 106)) (d : Decision) :
    (scan old i ks d).numerator =
      ks.foldl (fun v k => if i.val ∈ (rows k).targets then
        max v (candidate old (rows k)) else v) d.numerator := by
  induction ks generalizing d with
  | nil => rfl
  | cons k ks ih =>
      simp only [scan,List.foldl_cons]
      rw [ih]
      apply congrArg (fun v => ks.foldl (fun w k =>
        if i.val ∈ (rows k).targets then max w (candidate old (rows k)) else w) v)
      by_cases ht : i.val ∈ (rows k).targets
      · simp only [offerRow,if_pos ht,offer_numerator]
      · simp only [offerRow,if_neg ht]

theorem ordinaryDecision_numerator (old : Table) (upper : Bool) (i : Fin 200) :
    (ordinaryDecision old upper i).numerator =
      if 50 ≤ i.val then
        max (old upper i) (if upper then suffix old false (max 50 (i.val-49))
          else suffix old true (i.val-49))
      else old upper i := by
  by_cases ht : 50 ≤ i.val
  · simp only [ordinaryDecision,if_pos ht,offer_numerator]
  · simp only [ordinaryDecision,if_neg ht]

def roundDecision (old : Table) (upper : Bool) (i : Fin 200) : Decision :=
  if upper then scan old i (List.finRange 106) (ordinaryDecision old upper i)
  else ordinaryDecision old upper i

def roundTable (old : Table) : Table :=
  fun upper i => (roundDecision old upper i).numerator

def iterate : ℕ → Table
  | 0 => seed
  | n+1 => roundTable (iterate n)

def selectedW1 (generation : Fin 430) (cell : Fin 200) : Option (Fin 7 × Fin 10) :=
  match (roundDecision (iterate generation.val) true cell).choice with
  | .bank k => (rows k).w1Label
  | _ => none

/-- The provenance invariant concerns the actual arithmetic candidate,
not an asserted source H/h upper/lower bound. -/
def RowSound (old : Table) (i : Fin 200) (d : Decision) : Prop :=
  ∀ k, d.choice = .bank k →
    i.val ∈ (rows k).targets ∧ d.numerator = candidate old (rows k)

private theorem ordinaryDecision_rowSound (old : Table) (upper : Bool) (i : Fin 200) :
    RowSound old i (ordinaryDecision old upper i) := by
  intro k h
  unfold ordinaryDecision at h
  split at h
  · unfold offer at h
    split at h <;> cases h
  · cases h

private theorem offerRow_rowSound (old : Table) (i : Fin 200)
    (d : Decision) (k : Fin 106) (hd : RowSound old i d) :
    RowSound old i (offerRow old i d k) := by
  intro l hchoice
  by_cases ht : i.val ∈ (rows k).targets
  · by_cases hv : d.numerator < candidate old (rows k)
    · have heq : k = l := by
        have h : Choice.bank k = Choice.bank l := by
          simpa only [offerRow,if_pos ht,offer,if_pos hv] using hchoice
        exact Choice.bank.inj h
      subst l
      exact ⟨ht,by simp [offerRow,ht,offer,hv]⟩
    · have h : d.choice = .bank l := by
        simpa only [offerRow,if_pos ht,offer,if_neg hv] using hchoice
      simpa only [offerRow,if_pos ht,offer,if_neg hv] using hd l h
  · have h : d.choice = .bank l := by
      simpa only [offerRow,if_neg ht] using hchoice
    simpa only [offerRow,if_neg ht] using hd l h

private theorem scan_rowSound (old : Table) (i : Fin 200)
    (ks : List (Fin 106)) (d : Decision) (hd : RowSound old i d) :
    RowSound old i (scan old i ks d) := by
  revert d
  induction ks with
  | nil => intro d hd; exact hd
  | cons k ks ih =>
      intro d hd
      exact ih (offerRow old i d k) (offerRow_rowSound old i d k hd)

/-- Every selected W1 label comes from an actual106-row maximum at the
same upper query cell and exactly the previous generation table. -/
theorem selectedW1_source {g : Fin 430} {cell : Fin 200} {ij : Fin 7 × Fin 10}
    (h : selectedW1 g cell = some ij) :
    ∃ k : Fin 106,
      (roundDecision (iterate g.val) true cell).choice = .bank k ∧
      (rows k).w1Label = some ij ∧ cell.val ∈ (rows k).targets ∧
      (roundDecision (iterate g.val) true cell).numerator =
        candidate (iterate g.val) (rows k) := by
  have hs : RowSound (iterate g.val) cell
      (roundDecision (iterate g.val) true cell) := by
    exact scan_rowSound _ _ _ _ (ordinaryDecision_rowSound _ _ _)
  cases hc : (roundDecision (iterate g.val) true cell).choice with
  | retained => simp [selectedW1,hc] at h
  | buchstab => simp [selectedW1,hc] at h
  | bank k =>
      have hlabel : (rows k).w1Label = some ij := by
        simpa only [selectedW1,hc] using h
      exact ⟨k,hc,hlabel,(hs k hc).1,(hs k hc).2⟩

/-- A raw physical input, with no accepted/gate/K proof field. Prefix
arguments are the actual parameters passed to the frozen step constructor. -/
structure ParentInput where
  root : PhysicalNode
  rootOld : List ℕ
  seedCap : ℝ
  prefix : List (ℕ × ℝ)
  rootMask : ℕ → ℕ → Prop

def oldWord (a : ParentInput) : List ℕ := a.rootOld ++ a.prefix.map Prod.fst

def physicalPath (N : ℕ) (a : ParentInput) : List (ℝ × ℝ) :=
  a.prefix.map (fun p => (physicalPrime N p.1,p.2))

def parentHistory {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N : ℕ) (lo hi : ℝ) (a : ParentInput) : History :=
  advance plan lo hi (start plan lo hi a.seedCap a.root) (physicalPath N a)

/-- Freeze the original receiver at the ROOT integer product. Final
computed admission contains every earlier step admission, so the descendant
cannot optimize or replace an ancestor mask after seeing a later prime. -/
def computedFrozenMask {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N : ℕ) (lo hi : ℝ) (a : ParentInput) : ℕ → ℕ → Prop :=
  fun _ ell => a.rootMask a.rootOld.prod ell ∧
    (parentHistory plan N lo hi a).accepted = true

theorem computedFrozenMask_on_admission {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N : ℕ) (lo hi : ℝ) (a : ParentInput)
    (h : (parentHistory plan N lo hi a).accepted = true) (B ell : ℕ) :
    computedFrozenMask plan N lo hi a B ell ↔ a.rootMask a.rootOld.prod ell := by
  simp only [computedFrozenMask,h,and_true]

/-- Every actual ancestor frame stays in the history used by the
exporter. This equality follows from advance's frozen-frame constructor. -/
theorem exporter_preserves_ancestor_frames {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N : ℕ) (lo hi : ℝ) (a : ParentInput) (xs ys : List (ℝ × ℝ)) :
    (advance plan lo hi
      (advance plan lo hi (start plan lo hi a.seedCap a.root) xs) ys).frames.take
        (advance plan lo hi (start plan lo hi a.seedCap a.root) xs).frames.length =
      (advance plan lo hi (start plan lo hi a.seedCap a.root) xs).frames := by
  exact P2PhysicalFrozenPrefixHistory.advance_ancestor_records plan lo hi _ ys

/-- These are finite physical tests evaluated by the exporter. They are
not fields carrying the desired H/h inequality or positive-product bound. -/
structure ParentTests {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N B : ℕ) (Q chi gamma lo hi : ℝ)
    (a : ParentInput) (ij : Fin 7 × Fin 10) : Prop where
  accepted : (parentHistory plan N lo hi a).accepted = true
  product : (oldWord a).prod = B
  primes : ∀ p ∈ oldWord a, p.Prime
  word_eq : word (parentHistory plan N lo hi a).node = (oldWord a).map (physicalPrime N)
  total_eq : (parentHistory plan N lo hi a).node.total = Real.log Q / Real.log (N : ℝ)
  window : parentWindow N Q (oldWord a) chi
  residualLower : gamma ≤ residual (parentHistory plan N lo hi a).node
  target : (parentHistory plan N lo hi a).node.argument ≤ W1Target ij.1
  ceiling : residual (parentHistory plan N lo hi a).node / W1Target ij.1 ≤
    (parentHistory plan N lo hi a).node.ceiling

def queryCell (i : Fin 200) : Set ℝ :=
  Icc (1+(i.val : ℝ)/50) (1+((i.val : ℝ)+1)/50)

abbrev Slot := Fin (430*200)
def slotGeneration (s : Slot) : Fin 430 := ⟨s.val/200,by have := s.isLt; omega⟩
def slotCell (s : Slot) : Fin 200 := ⟨s.val%200,Nat.mod_lt _ (by norm_num)⟩


theorem slots_cover (g : Fin 430) (cell : Fin 200) :
    ∃ s : Slot, slotGeneration s = g ∧ slotCell s = cell := by
  let s : Slot := ⟨200*g.val+cell.val,by have := g.isLt; have := cell.isLt; omega⟩
  refine ⟨s,?_,?_⟩
  · apply Fin.ext
    dsimp [slotGeneration,s]
    have := cell.isLt
    omega
  · apply Fin.ext
    dsimp [slotCell,s]
    have := cell.isLt
    omega

def exportSlot {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N B : ℕ) (Q chi gamma lo hi : ℝ) (a : ParentInput)
    (s : Slot) : List W1Occurrence :=
  match selectedW1 (slotGeneration s) (slotCell s) with
  | none => []
  | some ij =>
      if ParentTests plan N B Q chi gamma lo hi a ij ∧
          (parentHistory plan N lo hi a).node.argument ∈ queryCell (slotCell s) then
        [⟨oldWord a,ij.1,ij.2,computedFrozenMask plan N lo hi a⟩]
      else []

def exportSlots {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N B : ℕ) (Q chi gamma lo hi : ℝ) (a : ParentInput) :
    List Slot → List W1Occurrence
  | [] => []
  | s::ss => exportSlot plan N B Q chi gamma lo hi a s ++
      exportSlots plan N B Q chi gamma lo hi a ss

def exportParent {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N B : ℕ) (Q chi gamma lo hi : ℝ) (a : ParentInput) : List W1Occurrence :=
  exportSlots plan N B Q chi gamma lo hi a (List.finRange (430*200))

def exportBank {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N B : ℕ) (Q chi gamma lo hi : ℝ) (parents : List ParentInput) :
    List W1Occurrence :=
  parents.flatMap (exportParent plan N B Q chi gamma lo hi)

private theorem exportSlot_length {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N B : ℕ) (Q chi gamma lo hi : ℝ) (a : ParentInput) (s : Slot) :
    (exportSlot plan N B Q chi gamma lo hi a s).length ≤ 1 := by
  unfold exportSlot
  split
  · simp
  · split <;> simp

private theorem exportSlots_length {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N B : ℕ) (Q chi gamma lo hi : ℝ) (a : ParentInput) (ss : List Slot) :
    (exportSlots plan N B Q chi gamma lo hi a ss).length ≤ ss.length := by
  induction ss with
  | nil => simp [exportSlots]
  | cons s ss ih =>
      have hs := exportSlot_length plan N B Q chi gamma lo hi a s
      simp only [exportSlots,List.length_append,List.length_cons]
      omega

theorem exportBank_length {depth mesh : ℕ}
    (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
    (N B : ℕ) (Q chi gamma lo hi : ℝ) (parents : List ParentInput) :
    (exportBank plan N B Q chi gamma lo hi parents).length ≤
      parents.length * (430*200) := by
  have hp (a : ParentInput) :
      (exportParent plan N B Q chi gamma lo hi a).length ≤ 430*200 := by
    simpa only [exportParent,List.length_finRange] using
      exportSlots_length plan N B Q chi gamma lo hi a (List.finRange (430*200))
  induction parents with
  | nil => simp [exportBank]
  | cons a parents ih =>
      simp only [exportBank,List.flatMap_cons,List.length_append,List.length_cons] at *
      have ha := hp a
      nlinarith only [ha,ih]

private theorem mem_exportSlot {depth mesh : ℕ}
    {plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh}
    {N B : ℕ} {Q chi gamma lo hi : ℝ} {a : ParentInput} {s : Slot}
    {o : W1Occurrence} (h : o ∈ exportSlot plan N B Q chi gamma lo hi a s) :
    ∃ ij : Fin 7 × Fin 10,
      selectedW1 (slotGeneration s) (slotCell s) = some ij ∧
      ParentTests plan N B Q chi gamma lo hi a ij ∧
      (parentHistory plan N lo hi a).node.argument ∈ queryCell (slotCell s) ∧
      o = ⟨oldWord a,ij.1,ij.2,computedFrozenMask plan N lo hi a⟩ := by
  cases hs : selectedW1 (slotGeneration s) (slotCell s) with
  | none => simp [exportSlot,hs] at h
  | some ij =>
      by_cases ht : ParentTests plan N B Q chi gamma lo hi a ij ∧
          (parentHistory plan N lo hi a).node.argument ∈ queryCell (slotCell s)
      · exact ⟨ij,hs,ht.1,ht.2,by simpa [exportSlot,hs,ht] using h⟩
      · simp [exportSlot,hs,ht] at h

private theorem mem_exportSlots {depth mesh : ℕ}
    {plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh}
    {N B : ℕ} {Q chi gamma lo hi : ℝ} {a : ParentInput} {ss : List Slot}
    {o : W1Occurrence} (h : o ∈ exportSlots plan N B Q chi gamma lo hi a ss) :
    ∃ s ∈ ss, o ∈ exportSlot plan N B Q chi gamma lo hi a s := by
  revert h
  induction ss with
  | nil => intro h; simp [exportSlots] at h
  | cons s ss ih =>
      intro h
      rcases List.mem_append.mp h with hh | ht
      · exact ⟨s,by simp,hh⟩
      · obtain ⟨t,ht,ho⟩ := ih ht
        exact ⟨t,by simp [ht],ho⟩

/-- Exact selected-row and causal-history provenance for every emitted
occurrence. This is soundness, not a converse coverage theorem. -/
theorem exportBank_provenance {depth mesh : ℕ}
    {plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh}
    {N B : ℕ} {Q chi gamma lo hi : ℝ} {parents : List ParentInput}
    {o : W1Occurrence}
    (h : o ∈ exportBank plan N B Q chi gamma lo hi parents) :
    ∃ a ∈ parents, ∃ s : Slot, ∃ ij : Fin 7 × Fin 10,
      selectedW1 (slotGeneration s) (slotCell s) = some ij ∧
      ParentTests plan N B Q chi gamma lo hi a ij ∧
      (parentHistory plan N lo hi a).node.argument ∈ queryCell (slotCell s) ∧
      o = ⟨oldWord a,ij.1,ij.2,computedFrozenMask plan N lo hi a⟩ := by
  obtain ⟨a,ha,ho⟩ := List.mem_flatMap.mp h
  obtain ⟨s,hs,ho⟩ := mem_exportSlots ho
  obtain ⟨ij,hsel,hphysical,hcell,heq⟩ := mem_exportSlot ho
  exact ⟨a,ha,s,ij,hsel,hphysical,hcell,heq⟩

/-- Full and selected physical gates follow from the actual computed
History admission; they are not new fields of ParentInput. -/
theorem exported_parent_gates {depth mesh : ℕ}
    {plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh}
    {N B : ℕ} {Q chi gamma lo hi : ℝ} {a : ParentInput} {ij : Fin 7 × Fin 10}
    (h : ParentTests plan N B Q chi gamma lo hi a ij) :
    fullGates (parentHistory plan N lo hi a).node ∧
      selectedGates (parentHistory plan N lo hi a).node := by
  exact constructed_retained_gates plan lo hi a.seedCap a.root (physicalPath N a)
    h.accepted

/-- Emitted records supply the physical cutoff at eta=gamma/5 from
their computed parent residual, instead of an arbitrary cutoff premise. -/
theorem exported_occurrence_data {depth mesh : ℕ}
    {plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh}
    {N B : ℕ} {Q chi gamma lo hi : ℝ} {parents : List ParentInput}
    {o : W1Occurrence} (hgamma : 0 < gamma)
    (h : o ∈ exportBank plan N B Q chi gamma lo hi parents) :
    o.old.prod = B ∧ parentWindow N Q o.old chi ∧
      (N : ℝ)^(gamma/5) ≤ cutoff Q B (W1Anchor o.anchor) := by
  obtain ⟨a,ha,s,ij,hsel,hphysical,hcell,rfl⟩ := exportBank_provenance h
  have hcoord :=
    P2EnhancedW1RepeatedLabelClassification.physical_level_eq_parent_residual
      hphysical.window hphysical.primes hphysical.word_eq hphysical.total_eq
  have hlevel : gamma ≤
      P2EnhancedLowerPrimeChildGeometry.physicalLevel N Q (oldWord a) := by
    rw [hcoord]
    exact hphysical.residualLower
  have hcut := P2EnhancedW1RepeatedLabelClassification.w1_anchor_fixed_power
    hphysical.window ij.2 hgamma hlevel
  rw [hphysical.product] at hcut
  exact ⟨hphysical.product,hphysical.window,hcut⟩

/-- The exported selected430 W1 occurrences enter the earlier finite-bank
payment directly. The fixed parent-list bound remains explicit; proving
that every original source parent is exported is a separate obligation. -/
theorem selected430_export_theta_payment (P : ℕ) {gamma epsilon : ℝ}
    (hgamma : 0 < gamma) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q chi lo hi : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
        (E : ℕ → ℕ → Prop) (depth mesh : ℕ)
        (plan : P2PhysicalIncomingPrefixCells.CapPlan depth mesh)
        (parents : ℕ → List ParentInput),
      (∀ B ∈ D, 0 < B) → (∀ B ∈ D, 0 ≤ sigma B) →
      (∀ B ∈ D, (parents B).length ≤ P) →
      (∀ B ∈ D, 1 < Q/(B : ℝ) ∧ Q/(B : ℝ) ≤ (N : ℝ)) →
      markedBankMass N Q D sigma E
        (fun B => exportBank plan N B Q chi gamma lo hi (parents B)) ≤
          epsilon * Theta N Q D sigma := by
  have heta : 0 < gamma/5 := by positivity
  obtain ⟨T,hT,hpay⟩ := markedBankMass_theta_payment ((430*200)*P) heta hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT Q chi lo hi D sigma E depth mesh plan parents hd hsigma hparents hR
  apply hpay N hNT Q chi D sigma E
    (fun B => exportBank plan N B Q chi gamma lo hi (parents B)) hd hsigma
  · intro B hB
    have hlen := exportBank_length plan N B Q chi gamma lo hi (parents B)
    have hmul := Nat.mul_le_mul_right (430*200) (hparents B hB)
    nlinarith only [hlen,hmul]
  · intro B hB o ho
    exact (exported_occurrence_data hgamma ho).1
  · intro B hB o ho
    exact (exported_occurrence_data hgamma ho).2.1
  · intro B hB o ho
    exact (exported_occurrence_data hgamma ho).2.2
  · exact hR

end
end ImbalancedChen.P2Selected430CausalOccurrenceExporter
