import ImbalancedChen.Part5OriginalH430ClosedOwner
import ImbalancedChen.Part5OriginalH430CutoffCoherence
import ImbalancedChen.Part5OriginalH430RealizedBuchstabSupply

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Filter the actual integer Member catalog by the literal closed-owner
Buchstab winner, then apply the existing absolute arithmetic supplier.
The lower direction guard is DERIVED from that winner. The full original
Buchstab interval is supplied by the all-StepShape cutoff invariant.

Generation labels remain explicit: their assignment to original selected
count histories is not inferred from physical Program depth. A conditional
selection of a local row is not the complete U3/U4 count licence.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedBuchstabSupply

noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P5OriginalFeedbackTableKernels
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430DecisionProvenance Part5OriginalH430ClosedOwner
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2OriginalChildPhysicalNormalization
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430ArithmeticParentMass Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalH430BuchstabPhysicalBudget Part5OriginalBuchstabImmutable430Budget
open Part5OriginalH430CutoffCoherence Part5OriginalH430RealizedBuchstabSupply

def SelectedBuchstab (g : Fin 430) (up : Bool) (s : ℝ) : Prop :=
  ∃ b : FloorAtom, s ∈ tableAtomSet (!up) b ∧ selectedChoice g up b = .buchstab

theorem selected_query_ge_two {g : Fin 430} {up : Bool} {s : ℝ}
    (h : SelectedBuchstab g up s) : 2 ≤ s := by
  obtain ⟨b, hb, hc⟩ := h
  exact selected_buchstab_guard hb hc

/-- No atom multiplicity at knots; the two adjacent cells are resolved
by their minimum, not counted twice. -/
theorem selected_atom_unique {g : Fin 430} {up : Bool} {s : ℝ}
    {b c : FloorAtom} (hb : s ∈ tableAtomSet (!up) b)
    (hc : s ∈ tableAtomSet (!up) c) : b = c := tableAtom_unique hb hc

def selectedFamily (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) : Finset (Label N mesh) :=
  (catalog N n mesh tau).filter (fun h => labelCode n tau h = c ∧
    SelectedBuchstab (g h) (labelNode n tau h).upper (labelNode n tau h).physical.argument)

theorem mem_selectedFamily {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {h : Label N mesh} :
    h ∈ selectedFamily N n mesh tau c g ↔ Valid n tau h ∧ labelCode n tau h = c ∧
      SelectedBuchstab (g h) (labelNode n tau h).upper (labelNode n tau h).physical.argument := by
  simp only [selectedFamily, Finset.mem_filter, mem_catalog]

theorem selectedFamily_subset {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} :
    selectedFamily N n mesh tau c g ⊆ cellFamily N n mesh tau c := by
  intro h hh
  obtain ⟨hv, hc, hs⟩ := mem_selectedFamily.mp hh
  have htwo := selected_query_ge_two hs
  have hg : directionGuard (labelNode n tau h).upper (labelNode n tau h).physical := by
    cases hu : (labelNode n tau h).upper with
    | false => exact htwo
    | true => trivial
  exact mem_cellFamily.mpr ⟨⟨hv, hg⟩, hc⟩

theorem selectedFamily_eq_filter (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) :
    selectedFamily N n mesh tau c g = (cellFamily N n mesh tau c).filter (fun h =>
      SelectedBuchstab (g h) (labelNode n tau h).upper (labelNode n tau h).physical.argument) := by
  ext h
  constructor
  · intro hh
    exact Finset.mem_filter.mpr ⟨selectedFamily_subset hh, (mem_selectedFamily.mp hh).2.2⟩
  · intro hh
    obtain ⟨hcell, hs⟩ := Finset.mem_filter.mp hh
    have hc := mem_cellFamily.mp hcell
    exact mem_selectedFamily.mpr ⟨hc.1.1, hc.2, hs⟩

/-- The actual table value, actual allowed cell, and original previous
suffix all appear together. No quadrature/count licence is assumed or
concluded by this exact scalar dictionary. -/
theorem selected_scalar_source {N n mesh : ℕ} {tau : ℝ} {c : RootCode n}
    {g : Label N mesh → Fin 430} {h : Label N mesh}
    (hh : h ∈ selectedFamily N n mesh tau c g) :
    ∃ b : FloorAtom,
      (labelNode n tau h).physical.argument ∈ queryCell
        (selectedOwner (g h) (labelNode n tau h).upper b) ∧
      selectedChoice (g h) (labelNode n tau h).upper b = .buchstab ∧
      tableFunction (!(labelNode n tau h).upper)
        (iterate ((g h).val+1) (labelNode n tau h).upper)
        (labelNode n tau h).physical.argument =
      ((buchstabValue (iterate (g h).val) (labelNode n tau h).upper
        (selectedOwner (g h) (labelNode n tau h).upper b) : ℤ) : ℝ)/(2^80:ℝ) := by
  obtain ⟨b, hb, hc⟩ := (mem_selectedFamily.mp hh).2.2
  refine ⟨b, selected_owner_contains hb, hc, ?_⟩
  rw [tableFunction_at_atom _ hb, closed_value_eq_selected, hc]

def selectedMark {N mesh : ℕ} (n : ℕ) (tau : ℝ)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) (h : Label N mesh) : ℝ :=
  if SelectedBuchstab (g h) (labelNode n tau h).upper (labelNode n tau h).physical.argument
    then sigma h else 0

def selectedTheta (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) : ℝ :=
  parentTheta N (cellQ N n c) (selectedFamily N n mesh tau c g)
    (fun h => parentProduct (labelWord h)) sigma

def selectedError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) : ℝ :=
  ∑ h ∈ selectedFamily N n mesh tau c g, sigma h *
    strictAbsoluteError (labelNode n tau h).upper N (cellQ N n c)
      (labelNode n tau h).physical.ceiling (labelWord h) (labelNode n tau h).physical
      (precedingH (g h)) (precedingh (g h))

def selectedMass (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) : ℝ :=
  ∑ h ∈ selectedFamily N n mesh tau c g, sigma h *
    ∑ b : RowAtom, strictRow (labelNode n tau h).upper N (cellQ N n c)
      (labelNode n tau h).physical.ceiling (labelWord h) (labelNode n tau h).physical b

theorem marked_cellTheta (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) :
    cellTheta N n mesh tau c (selectedMark n tau g sigma) =
      selectedTheta N n mesh tau c g sigma := by
  simp only [cellTheta, selectedTheta, parentTheta, selectedFamily_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hs : SelectedBuchstab (g h) (labelNode n tau h).upper
    (labelNode n tau h).physical.argument <;> simp [selectedMark, hs]

theorem marked_cellError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) :
    cellError N n mesh tau c (selectedMark n tau g sigma) g =
      selectedError N n mesh tau c g sigma := by
  simp only [cellError, selectedError, selectedFamily_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hs : SelectedBuchstab (g h) (labelNode n tau h).upper
    (labelNode n tau h).physical.argument <;> simp [selectedMark, hs]

theorem marked_cellMass (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) :
    cellMass N n mesh tau c (selectedMark n tau g sigma) =
      selectedMass N n mesh tau c g sigma := by
  simp only [cellMass, selectedMass, selectedFamily_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hs : SelectedBuchstab (g h) (labelNode n tau h).upper
    (labelNode n tau h).physical.argument <;> simp [selectedMark, hs]

/-- This finite row is the original strict prime carrier; no integral
is substituted in its definition. -/
def primeProfile {N n mesh : ℕ} (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (h : Label N mesh) : ℝ :=
  let p := (labelNode n tau h).physical
  let up := (labelNode n tau h).upper
  ∑ r ∈ singleChildren (.buchstab up p.argument) N (cellQ N n c) (labelWord h) p.ceiling,
    thetaAtom N (cellQ N n c) (parentProduct (labelWord h)*r.val) *
      tableFunction up (if up then precedingh (g h) else precedingH (g h))
        (P2EnhancedLowerPrimeChildCarriers.buchstabArgument (cellQ N n c) (labelWord h) r.val)

def originalMain {N n mesh : ℕ} (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (h : Label N mesh) : ℝ :=
  thetaAtom N (cellQ N n c) (parentProduct (labelWord h)) *
    originalProfile (labelNode n tau h).upper (labelNode n tau h).physical.argument
      (precedingH (g h)) (precedingh (g h))

def selectedProfileError (N n mesh : ℕ) (tau : ℝ) (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ) : ℝ :=
  ∑ h ∈ selectedFamily N n mesh tau c g, sigma h *
    |primeProfile tau c g h-originalMain tau c g h|

theorem selectedProfileError_le {N n mesh : ℕ} {tau : ℝ} (c : RootCode n)
    (g : Label N mesh → Fin 430) (sigma : Label N mesh → ℝ)
    (hN : 1 < N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hsigma : ∀ h ∈ selectedFamily N n mesh tau c g, 0 ≤ sigma h) :
    selectedProfileError N n mesh tau c g sigma ≤ selectedError N n mesh tau c g sigma := by
  apply Finset.sum_le_sum
  intro h hh
  have hm := selectedFamily_subset hh
  have hd := cell_history_support hN htau htauhi hn hm
  have hc : 0 < (labelNode n tau h).physical.ceiling := hd.1.2.2.2.2
  have hg := (mem_cellFamily.mp hm).1.2
  have hf := valid_label_cutoffFits (mem_selectedFamily.mp hh).1
  have he := actual_strict_profile_error (N := N) (Q := cellQ N n c)
    (chi := (labelNode n tau h).physical.ceiling) (old := labelWord h)
    (p := (labelNode n tau h).physical) hg (precedingH (g h)) (precedingh (g h))
  rw [idealProfile_eq_original hc hf hg] at he
  exact mul_le_mul_of_nonneg_left he (hsigma h hh)

/-- One threshold for the literal selected subfamilies and the original
UNCLIPPED Buchstab profiles. Nonnegative marks may depend on N; they are
not asserted to be the final U3/U4 source coefficients. -/
theorem uniform_selected_buchstab {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ c : RootCode n, ∀ g : Label N mesh → Fin 430,
      ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ selectedFamily N n mesh tau c g, 0 ≤ sigma h) →
      selectedError N n mesh tau c g sigma ≤ epsilon*selectedTheta N n mesh tau c g sigma ∧
      selectedProfileError N n mesh tau c g sigma ≤ epsilon*selectedTheta N n mesh tau c g sigma ∧
      (0 ≤ selectedMass N n mesh tau c g sigma ∧
        selectedMass N n mesh tau c g sigma ≤ 5*selectedTheta N n mesh tau c g sigma) ∧
      (selectedTheta N n mesh tau c g sigma = 0 →
        selectedError N n mesh tau c g sigma = 0 ∧ selectedMass N n mesh tau c g sigma = 0) := by
  obtain ⟨T, hT⟩ := uniform_realized_cells he
  refine ⟨max 2 T, ?_⟩
  intro N hN n mesh tau htau htauhi hn c g sigma hsigma
  have hmarked : ∀ h ∈ cellFamily N n mesh tau c,
      0 ≤ selectedMark n tau g sigma h := by
    intro h hh
    by_cases hs : SelectedBuchstab (g h) (labelNode n tau h).upper
      (labelNode n tau h).physical.argument
    · rw [selectedMark, if_pos hs]
      apply hsigma h
      rw [selectedFamily_eq_filter]
      exact Finset.mem_filter.mpr ⟨hh, hs⟩
    · simp [selectedMark, hs]
  have hv := hT N (by omega) n mesh tau htau htauhi hn c
    (selectedMark n tau g sigma) g hmarked
  simp only [marked_cellTheta, marked_cellError, marked_cellMass] at hv
  exact ⟨hv.1, (selectedProfileError_le c g sigma (by omega) htau htauhi hn hsigma).trans hv.1,
    hv.2.1, hv.2.2⟩

/-- Each cell keeps its own Q. The outer right side is the SUM of those
normalizers, never a single fictitious common-Q normalizer. -/
theorem uniform_selected_outer {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ n mesh : ℕ, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ g : Label N mesh → Fin 430, ∀ sigma : Label N mesh → ℝ,
      (∀ h ∈ catalog N n mesh tau,
        SelectedBuchstab (g h) (labelNode n tau h).upper
          (labelNode n tau h).physical.argument → 0 ≤ sigma h) →
      (∑ c : RootCode n, selectedError N n mesh tau c g sigma) ≤
        epsilon*(∑ c : RootCode n, selectedTheta N n mesh tau c g sigma) ∧
      (∑ c : RootCode n, selectedProfileError N n mesh tau c g sigma) ≤
        epsilon*(∑ c : RootCode n, selectedTheta N n mesh tau c g sigma) ∧
      (∑ c : RootCode n, selectedMass N n mesh tau c g sigma) ≤
        5*(∑ c : RootCode n, selectedTheta N n mesh tau c g sigma) := by
  obtain ⟨T, hT⟩ := uniform_selected_buchstab he
  refine ⟨T, ?_⟩
  intro N hN n mesh tau htau htauhi hn g sigma hsigma
  have hs (c : RootCode n) (h : Label N mesh)
      (hh : h ∈ selectedFamily N n mesh tau c g) : 0 ≤ sigma h := by
    have hm := mem_selectedFamily.mp hh
    exact hsigma h (mem_catalog.mpr hm.1) hm.2.2
  have hc (c : RootCode n) := hT N hN n mesh tau htau htauhi hn c g sigma (hs c)
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ c : RootCode n, epsilon*selectedTheta N n mesh tau c g sigma :=
        Finset.sum_le_sum (fun c _ => (hc c).1)
      _ = _ := by rw [Finset.mul_sum]
  · calc
      _ ≤ ∑ c : RootCode n, epsilon*selectedTheta N n mesh tau c g sigma :=
        Finset.sum_le_sum (fun c _ => (hc c).2.1)
      _ = _ := by rw [Finset.mul_sum]
  · calc
      _ ≤ ∑ c : RootCode n, 5*selectedTheta N n mesh tau c g sigma :=
        Finset.sum_le_sum (fun c _ => (hc c).2.2.1.2)
      _ = _ := by rw [Finset.mul_sum]

end
end ImbalancedChen.Part5OriginalH430SelectedBuchstabSupply
