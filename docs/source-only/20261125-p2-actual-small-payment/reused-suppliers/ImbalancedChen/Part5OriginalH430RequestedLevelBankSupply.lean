import ImbalancedChen.Part5OriginalH430RequestedLocalBankSupply

/-!
Manuscript-local bank supply on the ACTUAL generated request level.
SOURCE ONLY / UNCOMPILED. No caller supplies a generation function, marks,
Member proof or scalar-owner-selected predicate. List positions preserve
multiplicity; the initial root mark is1, not an asserted original count weight.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedLevelBankSupply

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPrimeChildCarriers
open P2OriginalChildPhysicalNormalization
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430SelectedFixedReadSupply Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLocalBankSupply

abbrev Index (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :=
  LevelIndex N n root tau p (g.val+1)

def selectedLevel (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (a : Original106Action) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l => ∃ i, Selected g.val (levelOccurrence l).current i (.bank (slotOfAction a)))

def levelTheta (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ l ∈ selectedLevel N n root tau p g a, levelMark l *
    thetaAtom N (rootQ N n root tau p) (parentProduct (levelOccurrence l).current.old)

def levelError (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ l ∈ selectedLevel N n root tau p g a, levelMark l *
    requestError N (rootQ N n root tau p) (levelOccurrence l).current g a

def levelRow (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (a : Original106Action) (b : RowAtom) : ℝ :=
  ∑ l ∈ selectedLevel N n root tau p g a, levelMark l *
    edgeRow (rootQ N n root tau p) (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val (levelOccurrence l).current) b

def levelAppliedError (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (a : Original106Action) : ℝ :=
  ∑ l ∈ selectedLevel N n root tau p g a, levelMark l *
    |edgeValue (rootQ N n root tau p) (iterate g.val) (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val (levelOccurrence l).current) -
      thetaAtom N (rootQ N n root tau p) (parentProduct (levelOccurrence l).current.old) *
        idealCellProfile (precedingH g) (precedingh g) a|

/-- No modulo/truncated predecessor: every position in this actual
level requests precisely generation g+1 and therefore reads iterate g. -/
theorem level_predecessor {N n : ℕ} {root : Root} {tau : ℝ} {p : ℕ} {g : Fin 430}
    (l : Index N n root tau p g) : predecessor (levelOccurrence l).remaining = some g := by
  have he := (levelOccurrence_source l).2
  obtain ⟨j,hj,hjval⟩ := predecessor_exact
    (remaining := (levelOccurrence l).remaining) (by omega) (by have := g.isLt; omega)
  have hjg : j = g := by apply Fin.ext; omega
  simpa only [hjg] using hj

theorem requested_action_unique {g : ℕ} {r : Request} {i j : Fin 200}
    {a b : Original106Action}
    (ha : Selected g r i (.bank (slotOfAction a)))
    (hb : Selected g r j (.bank (slotOfAction b))) : a = b := by
  have hij : i = j := Option.some.inj (ha.1.symm.trans hb.1)
  subst j
  have hslot : slotOfAction a = slotOfAction b := Choice.bank.inj (ha.2.symm.trans hb.2)
  simpa only [action_slot] using congrArg actionOfSlot hslot

theorem selectedLevel_disjoint {N n : ℕ} (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    {a b : Original106Action} (hab : a ≠ b) :
    Disjoint (selectedLevel N n root tau p g a) (selectedLevel N n root tau p g b) := by
  apply Finset.disjoint_left.mpr
  intro l ha hb
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hb).2
  exact hab (requested_action_unique hi hj)

/-- Exact selected-action partition for any signed test. Repeated path
occurrences stay different LIST POSITIONS even if catalog labels coincide. -/
theorem sum_selectedLevel (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (F : Index N n root tau p g → ℝ) :
    (∑ a : Original106Action, ∑ l ∈ selectedLevel N n root tau p g a, F l) =
      ∑ l : Index N n root tau p g,
        if ∃ a i, Selected g.val (levelOccurrence l).current i (.bank (slotOfAction a))
        then F l else 0 := by
  simp only [selectedLevel,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hex : ∃ a i, Selected g.val (levelOccurrence l).current i (.bank (slotOfAction a))
  · obtain ⟨a,i,hi⟩ := hex
    rw [if_pos ⟨a,i,hi⟩]
    calc
      _ = (if ∃ j, Selected g.val (levelOccurrence l).current j (.bank (slotOfAction a))
          then F l else 0) := by
        apply Finset.sum_eq_single a
        · intro b _ hba
          have hn : ¬∃ j, Selected g.val (levelOccurrence l).current j (.bank (slotOfAction b)) := by
            rintro ⟨j,hj⟩
            exact hba (requested_action_unique hj hi)
          exact if_neg hn
        · intro hn
          exact (hn (Finset.mem_univ a)).elim
      _ = F l := if_pos ⟨i,hi⟩
  · rw [if_neg hex]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun h => hex ⟨a,h⟩)

theorem level_applied_error_le (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action) :
    levelAppliedError N n root tau p g a ≤ levelError N n root tau p g a := by
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_left (request_applied_error_le _ _ _ _ _) (mark_pos _).le

/-- One pre-N threshold for every original root kind, prime, precision,
remaining-generation slice and selected slot. All geometric support and
marks are supplied from the generated recursion, not accepted as licences.
This is a feedback-row result, NOT a U3+U4 count defect or a smooth441 limit. -/
theorem uniform_level_bank_supply {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ n : ℕ, ∀ root : Root,
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) → physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430, ∀ a : Original106Action,
      levelError N n root tau p g a ≤ epsilon*levelTheta N n root tau p g a ∧
      levelAppliedError N n root tau p g a ≤ epsilon*levelTheta N n root tau p g a ∧
      (∀ b, 0 ≤ levelRow N n root tau p g a b) ∧
      (∑ b : RowAtom, levelRow N n root tau p g a b) ≤ 12*levelTheta N n root tau p g a ∧
      (levelTheta N n root tau p g a = 0 → levelError N n root tau p g a = 0 ∧
        ∀ b, levelRow N n root tau p g a b = 0) := by
  obtain ⟨T,hTlo,hT⟩ := uniform_requested_bank_local he
  refine ⟨T,hTlo,?_⟩
  intro N hN n root tau ht ht' hn p hp hb g a
  have hN1 : 1 < N := by omega
  let Q := rootQ N n root tau p
  let S := selectedLevel N n root tau p g a
  have hlocal (l : Index N n root tau p g) (hl : l ∈ S) :
      requestError N Q (levelOccurrence l).current g a ≤
        epsilon*thetaAtom N Q (parentProduct (levelOccurrence l).current.old) ∧
      (∀ b, 0 ≤ edgeRow Q (levelOccurrence l).current
        (children N Q g.val (levelOccurrence l).current) b) ∧
      (∑ b : RowAtom, edgeRow Q (levelOccurrence l).current
        (children N Q g.val (levelOccurrence l).current) b) ≤
        12*thetaAtom N Q (parentProduct (levelOccurrence l).current.old) := by
    have ho := (levelOccurrence_source l).1
    have hc := rootHistory_coherent hN1 ht ht' hn hp hb ho
    have hs := rootHistory_support hN1 ht ht' hn hp hb ho
    obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
    have h := hT N hN Q (levelOccurrence l).current g i (slotOfAction a)
      hc hi hs.2.2.1 hs.2.2.2.2.1
    exact ⟨by simpa only [action_slot] using h.1,h.2.1,h.2.2.1⟩
  have herr : levelError N n root tau p g a ≤ epsilon*levelTheta N n root tau p g a := by
    calc
      _ ≤ ∑ l ∈ S, levelMark l * (epsilon*thetaAtom N Q
          (parentProduct (levelOccurrence l).current.old)) :=
        Finset.sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left (hlocal l hl).1 (mark_pos _).le)
      _ = _ := by
        unfold levelTheta
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  have hrow (b : RowAtom) : 0 ≤ levelRow N n root tau p g a b :=
    Finset.sum_nonneg (fun l hl => mul_nonneg (mark_pos _).le ((hlocal l hl).2.1 b))
  have hmass : (∑ b : RowAtom, levelRow N n root tau p g a b) ≤
      12*levelTheta N n root tau p g a := by
    unfold levelRow
    rw [Finset.sum_comm]
    calc
      _ = ∑ l ∈ S, levelMark l * ∑ b : RowAtom,
          edgeRow Q (levelOccurrence l).current (children N Q g.val (levelOccurrence l).current) b := by
        apply Finset.sum_congr rfl
        intro l _
        exact (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ l ∈ S, levelMark l * (12*thetaAtom N Q
          (parentProduct (levelOccurrence l).current.old)) :=
        Finset.sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left (hlocal l hl).2.2 (mark_pos _).le)
      _ = _ := by
        unfold levelTheta
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  refine ⟨herr,(level_applied_error_le _ _ _ _ _ _ _).trans herr,hrow,hmass,?_⟩
  intro hz
  constructor
  · exact le_antisymm (by simpa only [hz,mul_zero] using herr)
      (Finset.sum_nonneg (fun l _ => mul_nonneg (mark_pos _).le (requestError_nonneg _ _ _ _ _)))
  · intro b
    have h := Finset.single_le_sum (fun c _ => hrow c) (Finset.mem_univ b)
    exact le_antisymm (by simpa only [hz,mul_zero] using h.trans hmass) (hrow b)

end
end ImbalancedChen.Part5OriginalH430RequestedLevelBankSupply
