import ImbalancedChen.Part5OriginalH430BankSlotTargets
import ImbalancedChen.Part5OriginalH430CutoffCoherence
import ImbalancedChen.Part5OriginalH430PrimeChildAdmission

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Selected bank families are filters of the existing integer Member catalog.
The chosen slot supplies its target test; the derived cutoff invariant
supplies the ceiling test. Strict fresh children remain STRICT/FRESH:
no N-window repeat or endpoint fibre is declared equal to this carrier.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedBankGeometry

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430SameQHistoryCells Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430ClosedOwner Part5OriginalH430DecisionProvenance
open Part5OriginalH430CutoffCoherence Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430BankSlotTargets

def SelectedBank (g : Fin 430) (up : Bool) (s : ℝ) (k : Fin 106) : Prop :=
  ∃ b : FloorAtom, s ∈ tableAtomSet (!up) b ∧ selectedChoice g up b = .bank k

theorem selectedBank_unique {g : Fin 430} {up : Bool} {s : ℝ} {k l : Fin 106}
    (hk : SelectedBank g up s k) (hl : SelectedBank g up s l) : k = l := by
  obtain ⟨b,hb,hbk⟩ := hk
  obtain ⟨c,hc,hcl⟩ := hl
  have hbc := tableAtom_unique hb hc
  subst c
  exact Choice.bank.inj (hbk.symm.trans hcl)

theorem selectedBank_target {g : Fin 430} {up : Bool} {s : ℝ} {k : Fin 106}
    (hk : SelectedBank g up s k) : up = true ∧ s ≤ actionTarget (actionOfSlot k) := by
  obtain ⟨b,hb,hchoice⟩ := hk
  exact selected_bank_target hb hchoice

def bankFamily (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (k : Fin 106) : Finset (Label N mesh) :=
  (cellFamily N n mesh tau c).filter (fun h =>
    SelectedBank (g h) (labelNode n tau h).upper (labelNode n tau h).physical.argument k)

def bankUnion (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) : Finset (Label N mesh) :=
  (cellFamily N n mesh tau c).filter (fun h => ∃ k,
    SelectedBank (g h) (labelNode n tau h).upper (labelNode n tau h).physical.argument k)

theorem mem_bankFamily {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {k : Fin 106} {h : Label N mesh} :
    h ∈ bankFamily N n mesh tau c g k ↔ h ∈ cellFamily N n mesh tau c ∧
      SelectedBank (g h) (labelNode n tau h).upper (labelNode n tau h).physical.argument k := by
  simp only [bankFamily, Finset.mem_filter]

theorem bankFamily_from_catalog {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {k : Fin 106} {h : Label N mesh}
    (hv : Valid n tau h) (hc : labelCode n tau h = c)
    (hk : SelectedBank (g h) (labelNode n tau h).upper (labelNode n tau h).physical.argument k) :
    h ∈ bankFamily N n mesh tau c g k := by
  have hup := (selectedBank_target hk).1
  have hg : Part5OriginalH430BuchstabPhysicalBudget.directionGuard
      (labelNode n tau h).upper (labelNode n tau h).physical := by
    rw [hup]
    trivial
  exact mem_bankFamily.mpr ⟨mem_cellFamily.mpr ⟨⟨hv,hg⟩,hc⟩,hk⟩

theorem bankFamily_disjoint {N n mesh : ℕ} (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) {k l : Fin 106} (hkl : k ≠ l) :
    Disjoint (bankFamily N n mesh tau c g k) (bankFamily N n mesh tau c g l) := by
  apply Finset.disjoint_left.mpr
  intro h hk hl
  exact hkl (selectedBank_unique (mem_bankFamily.mp hk).2 (mem_bankFamily.mp hl).2)

/-- Sum of SELECTED alternatives is a disjoint partition, not a sum of
all offers. F may be signed; no product-based quotient is introduced. -/
theorem sum_bankFamily (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (F : Label N mesh → ℝ) :
    (∑ k : Fin 106, ∑ h ∈ bankFamily N n mesh tau c g k, F h) =
      ∑ h ∈ bankUnion N n mesh tau c g, F h := by
  simp only [bankFamily, bankUnion, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases he : ∃ k, SelectedBank (g h) (labelNode n tau h).upper
      (labelNode n tau h).physical.argument k
  · rw [if_pos he]
    obtain ⟨k,hk⟩ := he
    calc
      _ = (if SelectedBank (g h) (labelNode n tau h).upper
          (labelNode n tau h).physical.argument k then F h else 0) := by
        apply Finset.sum_eq_single k
        · intro l _ hl
          exact if_neg (fun hsel => hl (selectedBank_unique hsel hk))
        · intro hnot
          exact (hnot (Finset.mem_univ k)).elim
      _ = F h := if_pos hk
  · have hn (k : Fin 106) : ¬SelectedBank (g h) (labelNode n tau h).upper
        (labelNode n tau h).physical.argument k := fun hk => he ⟨k,hk⟩
    simp only [hn, if_false, Finset.sum_const_zero, if_neg he]

/-- Both missing parent tests are deduced on an actually selected label. -/
theorem selected_parent_tests {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {k : Fin 106} {h : Label N mesh}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ bankFamily N n mesh tau c g k) :
    (labelNode n tau h).upper = true ∧
    (labelNode n tau h).physical.argument ≤ actionTarget (actionOfSlot k) ∧
    residual (labelNode n tau h).physical / actionTarget (actionOfSlot k) ≤
      (labelNode n tau h).physical.ceiling := by
  have hc := (mem_bankFamily.mp hh).1
  have hs := cell_history_support hN ht ht' hn hc
  have hk := selectedBank_target (mem_bankFamily.mp hh).2
  have hf := valid_label_cutoffFits (mem_cellFamily.mp hc).1.1
  exact ⟨hk.1,hk.2,target_cutoff_le_ceiling hs.1.2.2.2.2 hf
    (target_positive _) hk.2⟩

/-- Fixed terms are genuine zero-prime comparisons. Both W2 fixed
occurrences survive separately, including their different arguments. -/
theorem selected_fixed_components {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {k : Fin 106} {h : Label N mesh}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ bankFamily N n mesh tau c g k) :
    match actionOfSlot k with
    | .inl (i,j) => LocalDomain (labelNode n tau h).physical (.w1Fixed i j) (fun _ => 0)
    | .inr j => ∀ anchor : Bool,
        LocalDomain (labelNode n tau h).physical (.w2Fixed j anchor) (fun _ => 0) := by
  have hc := (mem_bankFamily.mp hh).1
  have hs := cell_history_support hN ht ht' hn hc
  have hp := (selected_parent_tests hN ht ht' hn hh).2.1
  have hL : 0 < residual (labelNode n tau h).physical := by
    rw [hs.2.1]
    exact (parentWindow_logs hs.1).2.2
  have hceil := hs.1.2.2.2.2
  have hf := valid_label_cutoffFits (mem_cellFamily.mp hc).1.1
  cases ha : actionOfSlot k with
  | inl ij =>
      rcases ij with ⟨i,j⟩
      have htarget : (labelNode n tau h).physical.argument ≤ W1Target i := by
        simpa only [ha, actionTarget] using hp
      have hanchor := W1_target_le_anchor i j
      have hpos : 0 < W1Anchor j := (target_positive (.inl (i,j))).trans_le hanchor
      exact ⟨hL, htarget, target_cutoff_le_ceiling hceil hf hpos (htarget.trans hanchor)⟩
  | inr j =>
      intro anchor
      have htarget : (labelNode n tau h).physical.argument ≤ (originalW2At j).s := by
        simpa only [ha, actionTarget] using hp
      have hanchor := W2_target_le_fixed j anchor
      have hpos := (target_positive (.inr j)).trans_le hanchor
      exact ⟨hL, htarget, target_cutoff_le_ceiling hceil hf hpos (htarget.trans hanchor)⟩

/-- Actual finite W1 child: no extra parent target or ceiling premise. -/
theorem selected_W1_child {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {k : Fin 106} {h : Label N mesh}
    {i : Fin 7} {j : Fin 10} {p : Fin (N+1)}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ bankFamily N n mesh tau c g k)
    (ha : actionOfSlot k = .inl (i,j))
    (hp : p ∈ singleChildren (.w1 i j) N (cellQ N n c) (labelWord h)
      (labelNode n tau h).physical.ceiling) :
    LocalDomain (labelNode n tau h).physical (.w1Singleton i j)
      (singleCoordinates N p.val) := by
  have hs := cell_history_support hN ht ht' hn (mem_bankFamily.mp hh).1
  have hparent := (selected_parent_tests hN ht ht' hn hh).2
  rw [ha] at hparent
  exact singleChild_LocalDomain hp hs.2.1 rfl hparent

/-- The W2 singleton and pair carriers here are the existing strict,
fresh carriers; original N-window exceptional lanes are still separate. -/
theorem selected_W2_single_child {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {k : Fin 106} {h : Label N mesh}
    {j : Fin 36} {piece : Fin 3} {p : Fin (N+1)}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ bankFamily N n mesh tau c g k)
    (ha : actionOfSlot k = .inr j)
    (hp : p ∈ singleChildren (.w2 j piece) N (cellQ N n c) (labelWord h)
      (labelNode n tau h).physical.ceiling) :
    LocalDomain (labelNode n tau h).physical (.w2Singleton j piece)
      (singleCoordinates N p.val) := by
  have hs := cell_history_support hN ht ht' hn (mem_bankFamily.mp hh).1
  have hparent := (selected_parent_tests hN ht ht' hn hh).2
  rw [ha] at hparent
  exact singleChild_LocalDomain hp hs.2.1 rfl hparent

theorem selected_W2_pair_child {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {k : Fin 106} {h : Label N mesh}
    {j : Fin 36} {piece : Fin 4} {p : Fin (N+1) × Fin (N+1)}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ bankFamily N n mesh tau c g k)
    (ha : actionOfSlot k = .inr j)
    (hp : p ∈ pairChildren j piece N (cellQ N n c) (labelWord h)
      (labelNode n tau h).physical.ceiling) :
    LocalDomain (labelNode n tau h).physical (.w2Pair j piece)
      (pairCoordinates N p.1.val p.2.val) := by
  have hs := cell_history_support hN ht ht' hn (mem_bankFamily.mp hh).1
  have hparent := (selected_parent_tests hN ht ht' hn hh).2
  rw [ha] at hparent
  exact pairChild_LocalDomain hp hs.2.1 rfl hparent

/-- Scalar provenance remains a raw candidate identity. It does NOT
identify that candidate with the continuous or arithmetic bank profile. -/
theorem selected_bank_scalar {g : Fin 430} {up : Bool} {s : ℝ} {k : Fin 106}
    (hk : SelectedBank g up s k) :
    tableFunction (!up) (iterate (g.val+1) up) s =
      ((candidate (iterate g.val) (P2Selected430LiteralActionData.rows k):ℤ):ℝ)/(2:ℝ)^80 := by
  obtain ⟨b,hb,hchoice⟩ := hk
  rw [tableFunction_at_atom _ hb, closed_value_eq_selected, hchoice]
  rfl

end
end ImbalancedChen.Part5OriginalH430SelectedBankGeometry
