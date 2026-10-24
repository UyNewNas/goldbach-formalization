import ImbalancedChen.P1HistoricalFourthDoubleWallLocalization
import ImbalancedChen.P1HistoricalFourthUniformCellMargin

/-!
# P1: local interior clipping of each historical fourth cell

The interior is B_old >= delta, rather than a test requiring the entire
mesh cell to have positive margin. Its closed affine boundary is retained.
The complement in the actual admitted cell is exactly 0<B_old<delta.
Both old and raised PLUS legs use this same old-gap clipping.  Boundary
volume and arithmetic payment are separate obligations.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open Set

/-- The complete fourth PLUS affine form, with the last coordinate twice. -/
def p1_fourthInteriorGateForm : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin 4, ContinuousLinearMap.proj i) + ContinuousLinearMap.proj 3

theorem p1_fourthInteriorGateForm_apply (t : Fin 4 → ℝ) :
    p1_fourthInteriorGateForm t = (∑ i, t i) + t 3 := by
  simp [p1_fourthInteriorGateForm]

theorem p1_fourthInteriorGateForm_ne_zero : p1_fourthInteriorGateForm ≠ 0 := by
  intro h
  have hh := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (fun _ => 1)) h
  norm_num [p1_fourthInteriorGateForm] at hh

/-- The equality face belongs to the interior, hence this gate is closed. -/
def p1_fourthInteriorGate (old delta : ℝ) : Set (Fin 4 → ℝ) :=
  {t | p1_fourthInteriorGateForm t ≤ old - delta}

theorem p1_mem_fourthInteriorGate (old delta : ℝ) (t : Fin 4 → ℝ) :
    t ∈ p1_fourthInteriorGate old delta ↔ delta ≤ p1_fourthPlusWallGap old t := by
  change p1_fourthInteriorGateForm t ≤ old - delta ↔ _
  rw [p1_fourthInteriorGateForm_apply]
  unfold p1_fourthPlusWallGap
  constructor <;> intro h <;> linarith

/-- The complementary positive-gap strip uses two strict nonzero rows. -/
def p1_fourthBoundaryGateForms : Fin 2 → (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ![p1_fourthInteriorGateForm, -p1_fourthInteriorGateForm]

def p1_fourthBoundaryGateBounds (old delta : ℝ) : Fin 2 → ℝ := ![old, delta - old]

theorem p1_fourthBoundaryGateForms_ne_zero : ∀ i, p1_fourthBoundaryGateForms i ≠ 0 := by
  intro i
  fin_cases i
  · simpa [p1_fourthBoundaryGateForms] using p1_fourthInteriorGateForm_ne_zero
  · simpa [p1_fourthBoundaryGateForms] using (neg_ne_zero.mpr p1_fourthInteriorGateForm_ne_zero)

theorem p1_mem_fourthBoundaryGateRegion (old delta : ℝ) (t : Fin 4 → ℝ) :
    t ∈ primeAffineGateRegion p1_fourthBoundaryGateForms
      (p1_fourthBoundaryGateBounds old delta) ↔
      0 < p1_fourthPlusWallGap old t ∧ p1_fourthPlusWallGap old t < delta := by
  have hrows : t ∈ primeAffineGateRegion p1_fourthBoundaryGateForms
      (p1_fourthBoundaryGateBounds old delta) ↔
      p1_fourthInteriorGateForm t < old ∧ -p1_fourthInteriorGateForm t < delta - old := by
    simp [primeAffineGateRegion, p1_fourthBoundaryGateForms,
      p1_fourthBoundaryGateBounds, Fin.forall_fin_succ]
  rw [hrows, p1_fourthInteriorGateForm_apply]
  unfold p1_fourthPlusWallGap
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
namespace HistoricalPrefixCapData

/-- The unchanged historical cell plus its parent gates and local old-gap clip. -/
def p1_fourthClippedJointRegion (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : Set (Fin 4 → ℝ) :=
  (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
    primeAffineGateRegion p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)) ∩
      p1_fourthInteriorGate (D.old4 j : ℝ) delta

/-- Closed enclosure retains only the clipped portion of the mesh box. -/
def p1_fourthClippedClosedCell (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : Set (Fin 4 → ℝ) :=
  p1_fourthClosedRationalBox (qLogPrimeMeshLo D.a D.b D.m j)
    (qLogPrimeMeshHi D.a D.b D.m j) ∩ p1_fourthInteriorGate (D.old4 j : ℝ) delta

theorem p1_fourthClippedClosedCell_isCompact (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    IsCompact (D.p1_fourthClippedClosedCell j delta) := by
  have hbox : IsCompact (p1_fourthClosedRationalBox (qLogPrimeMeshLo D.a D.b D.m j)
      (qLogPrimeMeshHi D.a D.b D.m j)) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hgate : IsClosed (p1_fourthInteriorGate (D.old4 j : ℝ) delta) :=
    isClosed_le p1_fourthInteriorGateForm.continuous continuous_const
  exact hbox.inter_right hgate

/-- In particular the entire closure of the strict historical joint
interior stays inside the same compact clipped enclosure. -/
theorem p1_fourthClippedJointRegion_closure_subset (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    closure (D.p1_fourthClippedJointRegion j delta) ⊆ D.p1_fourthClippedClosedCell j delta := by
  apply closure_minimal
  · intro t ht
    exact ⟨D.p1_fourthCell_subset_closedRationalBox j ht.1.1, ht.2⟩
  · exact (D.p1_fourthClippedClosedCell_isCompact j delta).isClosed

/-- Closed-cell terminal coordinates stay uniformly above zero when the
original ambient logarithmic lower endpoint is positive. -/
theorem p1_fourthClippedClosedCell_terminal_bounds (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (ha : 0 < D.a)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ)
    (t : Fin 4 → ℝ) (ht : t ∈ D.p1_fourthClippedClosedCell j delta) :
    0 < t 3 ∧ t 3 ≤ (D.b : ℝ) := by
  have hbounds := logPrimeMeshLoHi_bounds (by exact_mod_cast hab : (D.a : ℝ) < D.b) D.m j 3
  have hlo := (ht.1 3 (Set.mem_univ 3)).1
  have hhi := (ht.1 3 (Set.mem_univ 3)).2
  rw [congrFun (cast_qLogPrimeMeshLo D.a D.b D.m j) 3] at hlo
  rw [congrFun (cast_qLogPrimeMeshHi D.a D.b D.m j) 3] at hhi
  have ha' : (0 : ℝ) < D.a := by exact_mod_cast ha
  exact ⟨ha'.trans_le (hbounds.1.trans hlo), hhi.trans hbounds.2.2⟩

end HistoricalPrefixCapData

/-- A pointwise old-gap clip supplies uniform PLUS margin at every raised
level.  No whole-cell affine maximum test is among the hypotheses. -/
theorem p1_fourthInterior_uniform_ratio (old lambda delta rho : ℝ) (t : Fin 4 → ℝ)
    (hdelta : 0 < delta) (hrho : 0 < rho) (ht3 : 0 < t 3) (htrho : t 3 ≤ rho)
    (hlevel : old ≤ lambda) (hclip : t ∈ p1_fourthInteriorGate old delta) :
    1 + delta / rho ≤ (lambda - ∑ i, t i) / t 3 ∧
      0 < delta / (2 * rho) ∧
      1 + delta / (2 * rho) < (lambda - ∑ i, t i) / t 3 ∧
      t 3 < lambda - ∑ i, t i := by
  have hgap := (p1_mem_fourthInteriorGate old delta t).mp hclip
  unfold p1_fourthPlusWallGap at hgap
  have hmul : (delta / rho) * t 3 ≤ delta := by
    have h := mul_le_mul_of_nonneg_left htrho (div_nonneg hdelta.le hrho.le)
    simpa only [div_mul_cancel₀ _ hrho.ne'] using h
  have hratio : 1 + delta / rho ≤ (lambda - ∑ i, t i) / t 3 := by
    apply (le_div_iff₀ ht3).mpr
    nlinarith only [hgap, hmul, hlevel]
  have hhalf : 0 < delta / (2 * rho) := div_pos hdelta (by positivity)
  have heq : delta / rho = 2 * (delta / (2 * rho)) := by
    field_simp [hrho.ne'] <;> ring
  refine ⟨hratio, hhalf, ?_, ?_⟩
  · rw [heq] at hratio
    linarith
  · linarith

namespace HistoricalPrefixCapData

/-- The old and new parameters use the same clipped compact enclosure. -/
def p1_fourthClippedParameterSet (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (delta lambda : ℝ) : Set (ℝ × ℝ) :=
  (fun t : Fin 4 → ℝ => (lambda - ∑ i, t i, t 3)) '' D.p1_fourthClippedClosedCell j delta

theorem p1_fourthClippedParameterSet_isCompact (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (delta lambda : ℝ) :
    IsCompact (D.p1_fourthClippedParameterSet j delta lambda) := by
  have hF : Continuous (fun t : Fin 4 → ℝ => (lambda - ∑ i, t i, t 3)) := by fun_prop
  exact (D.p1_fourthClippedClosedCell_isCompact j delta).image hF

/-- Every point of either clipped parameter image meets the exact strict
PLUS compact supplier domain, with an explicit positive uniform gap. -/
theorem p1_fourthClippedParameterSet_legal (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (ha : 0 < D.a)
    (j : Fin 4 → Fin (D.m + 1)) (delta lambda : ℝ) (hdelta : 0 < delta)
    (hlevel : (D.old4 j : ℝ) ≤ lambda) :
    ∀ q ∈ D.p1_fourthClippedParameterSet j delta lambda,
      0 < q.2 ∧ q.2 < q.1 ∧ 1 + delta / (D.b : ℝ) ≤ q.1 / q.2 := by
  rintro q ⟨t, ht, rfl⟩
  have hterminal := D.p1_fourthClippedClosedCell_terminal_bounds hab ha j delta t ht
  have hb : (0 : ℝ) < D.b := by exact_mod_cast ha.trans hab
  have hratio := p1_fourthInterior_uniform_ratio (D.old4 j : ℝ) lambda delta (D.b : ℝ)
    t hdelta hb hterminal.1 hterminal.2 hlevel ht.2
  exact ⟨hterminal.1, hratio.2.2.2, hratio.1⟩

/-- Both residual legs now have legal compact source domains without
requiring the uncut whole mesh box to pass a margin check. -/
theorem p1_fourthClipped_both_supplier_domains (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (ha : 0 < D.a) (hlevels : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) (hdelta : 0 < delta) :
    IsCompact (D.p1_fourthClippedParameterSet j delta (D.old4 j : ℝ)) ∧
      IsCompact (D.p1_fourthClippedParameterSet j delta (D.cell4 j : ℝ)) ∧
      (∀ q ∈ D.p1_fourthClippedParameterSet j delta (D.old4 j : ℝ), 0 < q.2 ∧ q.2 < q.1) ∧
      (∀ q ∈ D.p1_fourthClippedParameterSet j delta (D.cell4 j : ℝ), 0 < q.2 ∧ q.2 < q.1) := by
  have hlevel : (D.old4 j : ℝ) ≤ D.cell4 j := by exact_mod_cast D.p1_old4_le_cell4 hlevels j
  refine ⟨D.p1_fourthClippedParameterSet_isCompact j delta _,
    D.p1_fourthClippedParameterSet_isCompact j delta _, ?_, ?_⟩
  · intro q hq
    have h := D.p1_fourthClippedParameterSet_legal hab ha j delta _ hdelta le_rfl q hq
    exact ⟨h.1, h.2.1⟩
  · intro q hq
    have h := D.p1_fourthClippedParameterSet_legal hab ha j delta _ hdelta hlevel q hq
    exact ⟨h.1, h.2.1⟩

/-- The closure of the actual continuous joint interior has the same
explicit uniform margin for both historical PLUS legs. -/
theorem p1_fourthClippedJointRegion_closure_uniform_gap (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (ha : 0 < D.a) (hlevels : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) (hdelta : 0 < delta)
    (t : Fin 4 → ℝ) (ht : t ∈ closure (D.p1_fourthClippedJointRegion j delta)) :
    0 < delta / (2 * (D.b : ℝ)) ∧
      1 + delta / (D.b : ℝ) ≤ ((D.old4 j : ℝ) - ∑ i, t i) / t 3 ∧
      1 + delta / (D.b : ℝ) ≤ ((D.cell4 j : ℝ) - ∑ i, t i) / t 3 ∧
      1 + delta / (2 * (D.b : ℝ)) < ((D.old4 j : ℝ) - ∑ i, t i) / t 3 ∧
      1 + delta / (2 * (D.b : ℝ)) < ((D.cell4 j : ℝ) - ∑ i, t i) / t 3 := by
  have hclosed := D.p1_fourthClippedJointRegion_closure_subset j delta ht
  have hterminal := D.p1_fourthClippedClosedCell_terminal_bounds hab ha j delta t hclosed
  have hb : (0 : ℝ) < D.b := by exact_mod_cast ha.trans hab
  have hlevel : (D.old4 j : ℝ) ≤ D.cell4 j := by exact_mod_cast D.p1_old4_le_cell4 hlevels j
  have hold := p1_fourthInterior_uniform_ratio (D.old4 j : ℝ) (D.old4 j : ℝ) delta (D.b : ℝ)
    t hdelta hb hterminal.1 hterminal.2 le_rfl hclosed.2
  have hnew := p1_fourthInterior_uniform_ratio (D.old4 j : ℝ) (D.cell4 j : ℝ) delta (D.b : ℝ)
    t hdelta hb hterminal.1 hterminal.2 hlevel hclosed.2
  exact ⟨hold.2.1, hold.1, hnew.1, hold.2.2.1, hnew.2.2.1⟩
/-- Literal actual tuple carrier on one owned fourth cell. -/
def p1_fourthActualCellTuples (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) : Finset (Fin 4 → ℕ) :=
  (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)

def p1_fourthInteriorTuples (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : Finset (Fin 4 → ℕ) :=
  (D.p1_fourthActualCellTuples N cap j).filter
    (fun p => delta ≤ p1_fourthPlusWallGap (D.old4 j : ℝ) (actualPrimeTupleLog N p))

def p1_fourthBoundaryTuples (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : Finset (Fin 4 → ℕ) :=
  (D.p1_fourthActualCellTuples N cap j).filter
    (fun p => 0 < p1_fourthPlusWallGap (D.old4 j : ℝ) (actualPrimeTupleLog N p) ∧
      p1_fourthPlusWallGap (D.old4 j : ℝ) (actualPrimeTupleLog N p) < delta)

/-- Exact continuous-affine dictionary for the clipped actual source. -/
theorem p1_fourthInteriorTuples_eq_joint_filter (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hlevels : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    D.p1_fourthInteriorTuples N cap j delta =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => (D.a : ℝ)) (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ D.p1_fourthClippedJointRegion j delta) := by
  unfold p1_fourthInteriorTuples p1_fourthActualCellTuples
  rw [p1_historicalUpperFourthAdmittedTuples_cell_filter D hab hlevels N cap hN hcap j]
  ext p
  simp only [Finset.mem_filter, p1_fourthClippedJointRegion, Set.mem_inter_iff,
    p1_mem_fourthInteriorGate]
  tauto

/-- Every actual interior tuple has its physical old/new quotient parameter
in the corresponding clipped compact image, retaining the full product. -/
theorem p1_fourthInteriorTuples_actualParameters_mem (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hlevels : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta lambda : ℝ) (p : Fin 4 → ℕ)
    (hp : p ∈ D.p1_fourthInteriorTuples N cap j delta) :
    actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ) lambda ∈
      D.p1_fourthClippedParameterSet j delta lambda := by
  have hp' := hp
  rw [D.p1_fourthInteriorTuples_eq_joint_filter hab hlevels N cap hN hcap j delta,
    Finset.mem_filter] at hp'
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp'.1
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  rw [p1_fourth_quotientParameters_eq N p hpos lambda]
  apply Set.mem_image_of_mem
  exact ⟨D.p1_fourthCell_subset_closedRationalBox j hp'.2.1.1, hp'.2.2⟩

/-- The boundary source is the same original cell/parent intersection
with two strict nonzero affine clipping rows. -/
theorem p1_fourthBoundaryTuples_eq_affine_filter (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hlevels : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    D.p1_fourthBoundaryTuples N cap j delta =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => (D.a : ℝ)) (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈
          (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)) ∩
          primeAffineGateRegion p1_fourthBoundaryGateForms
            (p1_fourthBoundaryGateBounds (D.old4 j : ℝ) delta)) := by
  unfold p1_fourthBoundaryTuples p1_fourthActualCellTuples
  rw [p1_historicalUpperFourthAdmittedTuples_cell_filter D hab hlevels N cap hN hcap j]
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff, p1_mem_fourthBoundaryGateRegion]
  tauto

/-- Actual admitted fourth cells have positive old gap, derived before
splitting; the boundary definition adds no unproved admission premise. -/
theorem p1_fourthActualCellTuples_gap_pos (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hlevels : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (p : Fin 4 → ℕ)
    (hp : p ∈ D.p1_fourthActualCellTuples N cap j) :
    0 < p1_fourthPlusWallGap (D.old4 j : ℝ) (actualPrimeTupleLog N p) := by
  obtain ⟨hparent, ht⟩ := Finset.mem_filter.mp hp
  have h := p1_admittedFourth_plusLegality_on_cell D hab hlevels N cap hN hcap p j hparent ht
  unfold p1_fourthPlusWallGap
  linarith [h.2.1]

/-- Exact, disjoint source partition.  The clipping equality face is
assigned to the interior, with every small positive gap in the boundary. -/
theorem p1_fourthActualCellTuples_split (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hlevels : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    D.p1_fourthActualCellTuples N cap j =
      D.p1_fourthInteriorTuples N cap j delta ∪ D.p1_fourthBoundaryTuples N cap j delta := by
  ext p
  simp only [p1_fourthInteriorTuples, p1_fourthBoundaryTuples, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro hp
    have hpos := D.p1_fourthActualCellTuples_gap_pos hab hlevels N cap hN hcap j p hp
    by_cases hclip : delta ≤ p1_fourthPlusWallGap (D.old4 j : ℝ) (actualPrimeTupleLog N p)
    · exact Or.inl ⟨hp, hclip⟩
    · exact Or.inr ⟨hp, hpos, lt_of_not_ge hclip⟩
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp

theorem p1_fourthInterior_boundary_disjoint (D : HistoricalPrefixCapData)
    (N cap : ℕ) (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    Disjoint (D.p1_fourthInteriorTuples N cap j delta) (D.p1_fourthBoundaryTuples N cap j delta) := by
  apply Finset.disjoint_left.mpr
  intro p hi hb
  have hi' := (Finset.mem_filter.mp hi).2
  have hb' := (Finset.mem_filter.mp hb).2.2
  exact (not_lt_of_ge hi') hb'

/-- Arbitrary actual finite summands, including the signed physical
residual difference, split exactly with no positivity assumption. -/
theorem p1_fourthActualCell_sum_split (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hlevels : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) (F : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ D.p1_fourthActualCellTuples N cap j, F p) =
      (∑ p ∈ D.p1_fourthInteriorTuples N cap j delta, F p) +
      (∑ p ∈ D.p1_fourthBoundaryTuples N cap j delta, F p) := by
  rw [D.p1_fourthActualCellTuples_split hab hlevels N cap hN hcap j delta]
  exact Finset.sum_union (D.p1_fourthInterior_boundary_disjoint N cap j delta)

end HistoricalPrefixCapData
end
end ImbalancedChen
