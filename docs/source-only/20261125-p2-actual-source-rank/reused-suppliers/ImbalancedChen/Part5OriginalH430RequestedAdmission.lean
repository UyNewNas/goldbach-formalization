import ImbalancedChen.Part5OriginalH430RequestedHistory
import ImbalancedChen.Part5OriginalH430CutoffCoherence

/-!
Manuscript-local admission of the EXISTING selected request recursion.
SOURCE ONLY / UNCOMPILED. No count estimate, error licence or Member proof
is an input field. Coherent is a geometric induction invariant; its root
instance and step preservation are supplied, not outsourced.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedAdmission

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430IntegerItineraries Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430BankSlotTargets Part5OriginalH430CutoffCoherence
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches

/-- Only literal state identities and elementary geometric facts. In
particular fullGates is NOT imposed on every classical frozen root. -/
structure Coherent (N : ℕ) (Q : ℝ) (r : Request) : Prop where
  target_gt_one : 1 < N
  read_valid : ReadValid r
  word_eq : word r.node.physical = r.old.map (physicalPrime N)
  letters : ∀ p ∈ r.old, p.Prime ∧ p.Coprime N
  level_eq : Q = (N : ℝ)^r.node.physical.total
  total_le_one : r.node.physical.total ≤ 1
  residual_pos : 0 < residual r.node.physical
  ceiling_pos : 0 < r.node.physical.ceiling
  cutoff_fits : CutoffFits r.node.physical

theorem coherent_window {N : ℕ} {Q : ℝ} {r : Request} (hr : Coherent N Q r) :
    parentWindow N Q r.old r.node.physical.ceiling := by
  rw [hr.level_eq]
  exact parentWindow_of_realization hr.target_gt_one rfl hr.total_le_one
    hr.word_eq (fun p hp => (hr.letters p hp).1.pos) hr.residual_pos hr.ceiling_pos

theorem coherent_residual {N : ℕ} {Q : ℝ} {r : Request} (hr : Coherent N Q r) :
    residual r.node.physical = physicalLevel N Q r.old := by
  rw [hr.level_eq]
  exact residual_eq_physicalLevel hr.target_gt_one rfl hr.word_eq
    (fun p hp => (hr.letters p hp).1.pos)

/-- Selection is request-aware: a fixed CELL need not be the scalar owner. -/
theorem requested_bank_tests {N g : ℕ} {Q : ℝ} {r : Request} {i : Fin 200}
    {k : Fin 106} (hr : Coherent N Q r) (hs : Selected g r i (.bank k)) :
    r.node.upper = true ∧ r.node.physical.argument ≤ actionTarget (actionOfSlot k) ∧
      residual r.node.physical / actionTarget (actionOfSlot k) ≤ r.node.physical.ceiling := by
  have h := Part5OriginalH430RequestedReads.selected_bank_target hr.read_valid hs
  exact ⟨h.1,h.2,target_cutoff_le_ceiling hr.ceiling_pos hr.cutoff_fits
    (target_positive _) h.2⟩

def EdgeLetters (N : ℕ) (e : Edge N) : Prop :=
  ∀ p ∈ appendedWord (edgeShape e) (edgePrimes e), p.Prime ∧ p.Coprime N

def EdgeAdmitted (N : ℕ) (r : Request) (e : Edge N) : Prop :=
  incomingAllowed r.node.upper (edgeShape e) ∧
    LocalDomain r.node.physical (edgeShape e) (edgeCoordinates e) ∧ EdgeLetters N e

private theorem single_letter {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {rule : SingleRule} {p : Fin (N+1)}
    (hp : p ∈ singleChildren rule N Q old chi) : p.val.Prime ∧ p.val.Coprime N := by
  have h := (mem_singleChildren.mp hp).1
  exact ⟨h.1,(Nat.coprime_mul_iff_right.mp h.2).1⟩

private theorem pair_letters {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {j : Fin 36} {k : Fin 4} {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren j k N Q old chi) :
    (p.1.val.Prime ∧ p.1.val.Coprime N) ∧ (p.2.val.Prime ∧ p.2.val.Coprime N) := by
  have h := (mem_pairChildren.mp hp).1
  exact ⟨⟨h.1.1,(Nat.coprime_mul_iff_right.mp h.1.2).1⟩,
    ⟨h.2.1,(Nat.coprime_mul_iff_right.mp h.2.2).1⟩⟩

private theorem w1_prime_admitted {N : ℕ} {Q : ℝ} {r : Request}
    (hr : Coherent N Q r) (hu : r.node.upper = true) (i : Fin 7) (j : Fin 10)
    (ht : r.node.physical.argument ≤ W1Target i) {p : Fin (N+1)}
    (hp : p ∈ singleChildren (.w1 i j) N Q r.old r.node.physical.ceiling) :
    EdgeAdmitted N r (.w1Prime i j p) := by
  have hc := target_cutoff_le_ceiling hr.ceiling_pos hr.cutoff_fits
    (target_positive (.inl (i,j))) ht
  have hd := singleChild_LocalDomain hp (coherent_residual hr) rfl ⟨ht,hc⟩
  refine ⟨by simpa [edgeShape,incomingAllowed] using hu, ?_, ?_⟩
  · simpa [edgeShape,edgeCoordinates,edgePrimes,singleCoordinates,physicalPrime,
      singleShape] using hd
  · simpa [EdgeLetters,edgeShape,edgePrimes,appendedWord] using single_letter hp

private theorem w2_single_admitted {N : ℕ} {Q : ℝ} {r : Request}
    (hr : Coherent N Q r) (hu : r.node.upper = true) (j : Fin 36) (k : Fin 3)
    (ht : r.node.physical.argument ≤ (originalW2At j).s) {p : Fin (N+1)}
    (hp : p ∈ singleChildren (.w2 j k) N Q r.old r.node.physical.ceiling) :
    EdgeAdmitted N r (.w2Prime j k p) := by
  have hc := target_cutoff_le_ceiling hr.ceiling_pos hr.cutoff_fits
    (target_positive (.inr j)) ht
  have hd := singleChild_LocalDomain hp (coherent_residual hr) rfl ⟨ht,hc⟩
  refine ⟨by simpa [edgeShape,incomingAllowed] using hu, ?_, ?_⟩
  · simpa [edgeShape,edgeCoordinates,edgePrimes,singleCoordinates,physicalPrime,
      singleShape] using hd
  · simpa [EdgeLetters,edgeShape,edgePrimes,appendedWord] using single_letter hp

private theorem w2_pair_admitted {N : ℕ} {Q : ℝ} {r : Request}
    (hr : Coherent N Q r) (hu : r.node.upper = true) (j : Fin 36) (k : Fin 4)
    (ht : r.node.physical.argument ≤ (originalW2At j).s)
    {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren j k N Q r.old r.node.physical.ceiling) :
    EdgeAdmitted N r (.w2Pair j k p) := by
  have hc := target_cutoff_le_ceiling hr.ceiling_pos hr.cutoff_fits
    (target_positive (.inr j)) ht
  have hd := pairChild_LocalDomain hp (coherent_residual hr) rfl ⟨ht,hc⟩
  refine ⟨by simpa [edgeShape,incomingAllowed] using hu, ?_, ?_⟩
  · simpa [edgeShape,edgeCoordinates,edgePrimes,pairCoordinates] using hd
  · obtain ⟨hs,hl⟩ := pair_letters hp
    simpa [EdgeLetters,edgeShape,edgePrimes,appendedWord] using And.intro hl hs

private theorem w2_fixed_admitted {N : ℕ} {Q : ℝ} {r : Request}
    (hr : Coherent N Q r) (hu : r.node.upper = true) (j : Fin 36) (anchor : Bool)
    (ht : r.node.physical.argument ≤ (originalW2At j).s) :
    EdgeAdmitted N r (.w2Fixed j anchor) := by
  have hanchor := W2_target_le_fixed j anchor
  have hc := target_cutoff_le_ceiling hr.ceiling_pos hr.cutoff_fits
    ((target_positive (.inr j)).trans_le hanchor) (ht.trans hanchor)
  exact ⟨by simpa [edgeShape,incomingAllowed] using hu,
    ⟨hr.residual_pos,ht,hc⟩,by simp [EdgeLetters,edgeShape,appendedWord]⟩

/-- Every listed bank component is admitted, using only its actual
selected target. This is not a union over the 106 alternative offers. -/
theorem bank_edges_admitted {N : ℕ} {Q : ℝ} {r : Request}
    (hr : Coherent N Q r) (hu : r.node.upper = true) (a : Original106Action)
    (ht : r.node.physical.argument ≤ actionTarget a) {e : Edge N}
    (he : e ∈ bankEdges N Q r a) : EdgeAdmitted N r e := by
  rcases a with ⟨i,j⟩ | j
  · change r.node.physical.argument ≤ W1Target i at ht
    rcases (show e = .w1Fixed i j ∨ e ∈ w1Edges N Q r i j by
      simpa only [bankEdges,List.mem_cons] using he) with rfl | he
    · have hanchor := W1_target_le_anchor i j
      have hc := target_cutoff_le_ceiling hr.ceiling_pos hr.cutoff_fits
        ((target_positive (.inl (i,j))).trans_le hanchor) (ht.trans hanchor)
      exact ⟨by simpa [edgeShape,incomingAllowed] using hu,
        ⟨hr.residual_pos,ht,hc⟩,by simp [EdgeLetters,edgeShape,appendedWord]⟩
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
      exact w1_prime_admitted hr hu i j ht (Finset.mem_toList.mp hp)
  · change r.node.physical.argument ≤ (originalW2At j).s at ht
    have hsingle (k : Fin 3) {e : Edge N} (he : e ∈ w2SingleEdges N Q r j k) :
        EdgeAdmitted N r e := by
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
      exact w2_single_admitted hr hu j k ht (Finset.mem_toList.mp hp)
    have hpair (k : Fin 4) {e : Edge N} (he : e ∈ w2PairEdges N Q r j k) :
        EdgeAdmitted N r e := by
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
      exact w2_pair_admitted hr hu j k ht (Finset.mem_toList.mp hp)
    simp only [bankEdges,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he
    rcases he with (rfl | rfl) | h0 | h1 | h2 | h0 | h1 | h2 | h3
    · exact w2_fixed_admitted hr hu j true ht
    · exact w2_fixed_admitted hr hu j false ht
    · exact hsingle 0 h0
    · exact hsingle 1 h1
    · exact hsingle 2 h2
    · exact hpair 0 h0
    · exact hpair 1 h1
    · exact hpair 2 h2
    · exact hpair 3 h3

/-- Complete local admission for retained, both Buchstab directions,
W1 fixed/single, and all W2 fixed/single/pair generated requests. -/
theorem child_admission {N g : ℕ} {Q : ℝ} {r : Request} {e : Edge N}
    (hr : Coherent N Q r) (he : e ∈ children N Q g r) : EdgeAdmitted N r e := by
  obtain ⟨i,c,hs,he⟩ := child_source he
  cases c with
  | retained =>
      have heq : e = .retained i := by simpa only [branchEdges,List.mem_singleton] using he
      subst e
      exact ⟨trivial,⟨hr.residual_pos,trivial⟩,by simp [EdgeLetters,edgeShape,appendedWord]⟩
  | buchstab =>
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
      have hp' := Finset.mem_toList.mp hp
      have hd := singleChild_LocalDomain hp' (coherent_residual hr) rfl
        (show SingleParentTests r.node.physical (.buchstab r.node.upper r.node.physical.argument)
          from rfl)
      have hletters := single_letter hp'
      cases hu : r.node.upper
      all_goals
        refine ⟨by simp [edgeShape,incomingAllowed,hu], ?_, ?_⟩
        · simpa [edgeShape,edgeCoordinates,edgePrimes,singleCoordinates,physicalPrime,
            singleShape,hu] using hd
        · simpa [EdgeLetters,edgeShape,edgePrimes,appendedWord,hu] using hletters
  | bank k =>
      have ht := requested_bank_tests hr hs
      exact bank_edges_admitted hr ht.1 (actionOfSlot k) ht.2.1 he

/-- The induction invariant is proved at the next actual request;
its owner/cell validity is supplied by the old exact request theorem. -/
theorem child_coherent {N g : ℕ} {Q : ℝ} {r : Request} {e : Edge N}
    (hr : Coherent N Q r) (he : e ∈ children N Q g r) : Coherent N Q (nextRequest r e) := by
  have hstep := child_admission hr he
  refine ⟨hr.target_gt_one,child_readValid hr.read_valid he,next_word e hr.word_eq,
    ?_,?_,?_,?_,?_,?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hr.letters p hp
    · exact hstep.2.2 p hp
  · simpa only [next_total] using hr.level_eq
  · simpa only [next_total] using hr.total_le_one
  · exact perform_residual_pos hstep.2.1
  · exact perform_ceiling_pos hr.ceiling_pos hstep.2.1
  · exact perform_cutoffFits hr.ceiling_pos hr.cutoff_fits hstep.2.1

/-- Inactive coordinates are exactly1, not an extra prime summation. -/
theorem edge_canonical {N : ℕ} (e : Edge N) :
    Part5OriginalH430SameQHistoryCells.canonicalPoint (edgeShape e) (edgePrimes e) := by
  cases e with
  | buchstab up p => cases up <;> simp [edgeShape,edgePrimes,Part5OriginalH430SameQHistoryCells.canonicalPoint]
  | _ => simp [edgeShape,edgePrimes,Part5OriginalH430SameQHistoryCells.canonicalPoint]

private theorem integer_coordinate_bounds {N : ℕ} (hN : 1 < N)
    (e : Edge N) (hp : EdgeLetters N e) (i : Fin 2) :
    1 ≤ edgePrimes e i ∧ edgePrimes e i ≤ N := by
  cases e with
  | retained _ => fin_cases i <;> simp [edgePrimes]; all_goals omega
  | w1Fixed _ _ => fin_cases i <;> simp [edgePrimes]; all_goals omega
  | w2Fixed _ _ => fin_cases i <;> simp [edgePrimes]; all_goals omega
  | buchstab up p =>
      have hmem : p.val ∈ appendedWord (edgeShape (.buchstab up p))
          (edgePrimes (.buchstab up p)) := by
        cases up <;> simp [edgeShape,edgePrimes,appendedWord]
      have hprime : p.val.Prime := (hp p.val hmem).1
      fin_cases i <;> simp only [edgePrimes,Matrix.cons_val_zero,Matrix.cons_val_one]
      · exact ⟨hprime.one_lt.le,by have := p.isLt; omega⟩
      · exact ⟨le_rfl,by omega⟩
  | w1Prime a b p =>
      have hprime := (hp p.val (by simp [edgeShape,edgePrimes,appendedWord])).1
      fin_cases i <;> simp only [edgePrimes,Matrix.cons_val_zero,Matrix.cons_val_one]
      · exact ⟨hprime.one_lt.le,by have := p.isLt; omega⟩
      · exact ⟨le_rfl,by omega⟩
  | w2Prime a b p =>
      have hprime := (hp p.val (by simp [edgeShape,edgePrimes,appendedWord])).1
      fin_cases i <;> simp only [edgePrimes,Matrix.cons_val_zero,Matrix.cons_val_one]
      · exact ⟨hprime.one_lt.le,by have := p.isLt; omega⟩
      · exact ⟨le_rfl,by omega⟩
  | w2Pair a b p =>
      have hs := (hp p.1.val (by simp [edgeShape,edgePrimes,appendedWord])).1
      have hl := (hp p.2.val (by simp [edgeShape,edgePrimes,appendedWord])).1
      fin_cases i <;> simp only [edgePrimes,Matrix.cons_val_zero,Matrix.cons_val_one]
      · exact ⟨hs.one_lt.le,by have := p.1.isLt; omega⟩
      · exact ⟨hl.one_lt.le,by have := p.2.isLt; omega⟩

theorem child_coordinate_bounds {N g : ℕ} {Q : ℝ} {r : Request} {e : Edge N}
    (hr : Coherent N Q r) (he : e ∈ children N Q g r) (i : Fin 2) :
    edgeCoordinates e i ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hlo,hhi⟩ := integer_coordinate_bounds hr.target_gt_one e
    (child_admission hr he).2.2 i
  have hp : (0 : ℝ) < edgePrimes e i := by exact_mod_cast (show 0 < edgePrimes e i by omega)
  have hN : (1 : ℝ) < N := by exact_mod_cast hr.target_gt_one
  change 0 ≤ Real.log (edgePrimes e i : ℝ)/Real.log (N : ℝ) ∧
    Real.log (edgePrimes e i : ℝ)/Real.log (N : ℝ) ≤ 1
  refine ⟨div_nonneg (Real.log_nonneg (by exact_mod_cast hlo)) (Real.log_pos hN).le,?_⟩
  apply (div_le_iff₀ (Real.log_pos hN)).mpr
  simpa only [one_mul] using Real.log_le_log hp (by exact_mod_cast hhi)

end
end ImbalancedChen.Part5OriginalH430RequestedAdmission
