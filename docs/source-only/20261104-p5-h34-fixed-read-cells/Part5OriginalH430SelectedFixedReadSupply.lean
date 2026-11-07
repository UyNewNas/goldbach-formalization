import ImbalancedChen.Part5OriginalH430FixedReadRows

/-!
SOURCE ONLY / UNCOMPILED.

Instantiate the fixed-read correction on the EXISTING selected Member
families, with the old W1/W2 production thresholds. The correction is
identical in the arithmetic and ideal rows; no error budget is spent.
The result is a cell-labelled fixed-read profile, not a proof that the
original counts obey the preceding closed-cell induction invariant.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedFixedReadSupply

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPrimeChildCarriers
open P2OriginalChildPhysicalNormalization
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430SameQHistoryCells
open Part5OriginalH430BankSlotTargets Part5OriginalH430SelectedBankGeometry
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430LiteralBankBudget
open Part5OriginalH430SelectedBankCarrierSupply
open Part5OriginalH430SelectedStrictW1Supply
open Part5OriginalH430SelectedProductionW2Supply
open Part5OriginalH430FixedReadRows


/-- Exact old-generation pin, not a replay of the 430 numerical rounds. -/
theorem literal_old_fixed_channel (g : Fin 430) (a : Original106Action) :
    Part5OriginalH430FixedReadDictionary.rawFixedValue
      (P2Selected430CausalOccurrenceExporter.iterate g.val) a =
      Part5OriginalH430FixedReadDictionary.fixedValue (precedingH g) a :=
  Part5OriginalH430FixedReadDictionary.rawFixedValue_eq _ _

/-- Connect the actual NEW closed owner to the OLD literal point reads.
The unchanged feedback and base terms remain visible obligations. -/
theorem selected_bank_fixedRead_upper (g : Fin 430) (up : Bool)
    (b : Part5OriginalUpsilon5CausalDictionary.FloorAtom) (k : Fin 106)
    (hc : Part5OriginalH430ClosedOwner.selectedChoice g up b = .bank k) :
    Part5OriginalUpsilon5CausalDictionary.floorAtomValue
      (P2Selected430CausalOccurrenceExporter.iterate (g.val+1) up) b ≤
      Part5OriginalH430FixedReadDictionary.baseValue (actionOfSlot k) +
      Part5OriginalH430FixedReadDictionary.fixedValue (precedingH g) (actionOfSlot k) +
      Part5OriginalH430FixedReadDictionary.feedbackValue
        (P2Selected430CausalOccurrenceExporter.iterate g.val) (actionOfSlot k) := by
  rw [Part5OriginalH430ClosedOwner.closed_value_eq_selected,hc]
  have h := Part5OriginalH430FixedReadDictionary.candidate_fixedRead_upper
    (P2Selected430CausalOccurrenceExporter.iterate g.val) (actionOfSlot k)
  simpa only [slot_action,Part5OriginalH430DecisionProvenance.choiceValue] using h

abbrev family (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (a : Original106Action) : Finset (Label N mesh) :=
  bankFamily N n mesh tau c g (slotOfAction a)

abbrev theta (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (a : Original106Action) : ℝ :=
  bankTheta N n mesh tau c g sigma (slotOfAction a)

def pointError (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ b : RowAtom, |cellReadRow N Q old p a b-thetaAtom N Q (parentProduct old)*cellReadIdeal a b| *
    |oldAtomValue (precedingH g) (precedingh g) b|

def oldPointError (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ b : RowAtom, |oldProductionRow N Q old p a b-thetaAtom N Q (parentProduct old)*idealRow a b| *
    |oldAtomValue (precedingH g) (precedingh g) b|

theorem pointError_exact (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (g : Fin 430) (a : Original106Action) :
    pointError N Q old p g a = oldPointError N Q old p g a := by
  simp only [pointError,oldPointError,discrepancy_exact]

def selectedError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (a : Original106Action) : ℝ :=
  ∑ h ∈ family N n mesh tau c g a, sigma h *
    pointError N (cellQ N n c) (labelWord h) (labelNode n tau h).physical (g h) a

def oldSelectedError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (a : Original106Action) : ℝ :=
  ∑ h ∈ family N n mesh tau c g a, sigma h *
    oldPointError N (cellQ N n c) (labelWord h) (labelNode n tau h).physical (g h) a

def selectedRow (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (a : Original106Action)
    (b : RowAtom) : ℝ :=
  ∑ h ∈ family N n mesh tau c g a, sigma h *
    cellReadRow N (cellQ N n c) (labelWord h) (labelNode n tau h).physical a b

def oldSelectedRow (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (a : Original106Action)
    (b : RowAtom) : ℝ :=
  ∑ h ∈ family N n mesh tau c g a, sigma h *
    oldProductionRow N (cellQ N n c) (labelWord h) (labelNode n tau h).physical a b

theorem selectedError_exact (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (a : Original106Action) :
    selectedError N n mesh tau c g sigma a = oldSelectedError N n mesh tau c g sigma a := by
  simp only [selectedError,oldSelectedError,pointError_exact]

theorem selectedRow_mass_exact (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (a : Original106Action) :
    (∑ b : RowAtom, selectedRow N n mesh tau c g sigma a b) =
      ∑ b : RowAtom, oldSelectedRow N n mesh tau c g sigma a b := by
  unfold selectedRow oldSelectedRow
  rw [Finset.sum_comm,Finset.sum_comm (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_sum,← Finset.mul_sum,cellReadRow_mass]

/-- One threshold for all106 selected actions and their literal old cells.
The original input family/generation/mark construction remains separate. -/
theorem uniform_selected_fixedReads {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ, ∀ a : Original106Action,
      (∀ h ∈ family N n mesh tau c g a, 0 ≤ sigma h) →
      selectedError N n mesh tau c g sigma a ≤ epsilon*theta N n mesh tau c g sigma a ∧
      (∀ b, 0 ≤ selectedRow N n mesh tau c g sigma a b) ∧
      (∑ b : RowAtom, selectedRow N n mesh tau c g sigma a b) ≤
        12*theta N n mesh tau c g sigma a ∧
      (theta N n mesh tau c g sigma a = 0 →
        selectedError N n mesh tau c g sigma a = 0 ∧
        ∀ b, selectedRow N n mesh tau c g sigma a b = 0) := by
  obtain ⟨T1,h1⟩ := uniform_selected_strictW1 he
  obtain ⟨T2,h2⟩ := uniform_selected_W2_production he
  refine ⟨max 4 (max T1 T2), ?_⟩
  intro N hN n mesh tau ht ht' hn c g sigma a hs
  have hN4 : 4 ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hbase : oldSelectedError N n mesh tau c g sigma a ≤
        epsilon*theta N n mesh tau c g sigma a ∧
      (∑ b : RowAtom, oldSelectedRow N n mesh tau c g sigma a b) ≤
        12*theta N n mesh tau c g sigma a := by
    rcases a with ⟨i,j⟩ | j
    · have hh := h1 N (by omega) n mesh tau ht ht' hn c g sigma i j hs
      exact ⟨hh.1,hh.2.2.1⟩
    · have hh := h2 N (by omega) n mesh tau ht ht' hn c g sigma j hs
      exact ⟨hh.1,hh.2.2.1⟩
  have herr : selectedError N n mesh tau c g sigma a ≤
      epsilon*theta N n mesh tau c g sigma a := by
    rw [selectedError_exact]
    exact hbase.1
  have hw (b : RowAtom) : 0 ≤ selectedRow N n mesh tau c g sigma a b := by
    apply Finset.sum_nonneg
    intro h hh
    have hsupport := cell_history_support hN1 ht ht' hn (mem_bankFamily.mp hh).1
    exact mul_nonneg (hs h hh) (cellReadRow_nonneg hN4 hsupport.1 a b)
  have hmass : (∑ b : RowAtom, selectedRow N n mesh tau c g sigma a b) ≤
      12*theta N n mesh tau c g sigma a := by
    rw [selectedRow_mass_exact]
    exact hbase.2
  refine ⟨herr,hw,hmass,?_⟩
  intro hz
  constructor
  · apply le_antisymm (by simpa only [hz,mul_zero] using herr)
    exact Finset.sum_nonneg (fun h hh => mul_nonneg (hs h hh)
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  · intro b
    have hb := Finset.single_le_sum (fun c _ => hw c) (Finset.mem_univ b)
    exact le_antisymm ((hb.trans hmass).trans_eq (by rw [hz,mul_zero])) (hw b)

def idealCellProfile (H h : Fin 200 → ℤ) (a : Original106Action) : ℝ :=
  ∑ b : RowAtom, cellReadIdeal a b*oldAtomValue H h b

/-- Applied error is downstream of absolute coefficient control, not a
substitute for it. The ideal is explicitly the cell-labelled ideal. -/
theorem applied_error_le (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode)
    (g : Fin 430) (a : Original106Action) :
    |cellReadProfile N Q old p a (precedingH g) (precedingh g) -
      thetaAtom N Q (parentProduct old)*idealCellProfile (precedingH g) (precedingh g) a| ≤
      pointError N Q old p g a := by
  rw [← cellReadRow_value,idealCellProfile,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc,← sub_mul,abs_mul]

theorem uniform_selected_outer_fixedReads {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ g : Label N mesh → Fin 430, ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ readyCatalog N n mesh tau, 0 ≤ sigma h) →
      (∑ c : RootCode n, ∑ a : Original106Action, selectedError N n mesh tau c g sigma a) ≤
        epsilon*(∑ c : RootCode n, ∑ a : Original106Action, theta N n mesh tau c g sigma a) := by
  obtain ⟨T,hT⟩ := uniform_selected_fixedReads he
  refine ⟨T,?_⟩
  intro N hN n mesh tau ht ht' hn g sigma hs
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  exact (hT N hN n mesh tau ht ht' hn c g sigma a
    (fun h hh => hs h (Finset.mem_filter.mp (mem_bankFamily.mp hh).1).1)).1

end
end ImbalancedChen.Part5OriginalH430SelectedFixedReadSupply
