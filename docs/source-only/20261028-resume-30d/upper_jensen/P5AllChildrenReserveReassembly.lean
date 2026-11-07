import ImbalancedChen.P5ChildSelectedOwnerJensenReserve
import ImbalancedChen.P1OriginalFifthActualB13IntegralError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact 64-child-to-parent reassembly of the REAL selected-owner reserve.
The fixed raw parent is charged once, not once per decoded owner/child.
-/
namespace ImbalancedChen.P5AllChildrenReserveReassembly
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1FifthGrid400UnitBoxPartition
open P5OldFifthExact64ChildTiling
open P5ChildSelectedOwnerJensenReserve
open P1OriginalFifthLiteralKernelModulus
open P1OriginalFifthActualB13IntegralError

abbrev Point := Fin 5 → ℝ

def rawRetained (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) : Set Point :=
  raw.originalBox ∩ selectedOwnerUnion e chi m omega J5

def rawOmitted (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) : Set Point :=
  raw.originalBox \ rawRetained raw e chi m omega J5

theorem rawRetained_measurable (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) : MeasurableSet (rawRetained raw e chi m omega J5) :=
  (measurableSet_originalBox raw).inter (selectedOwnerUnion_measurable e chi m omega J5)

theorem rawOmitted_measurable (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) : MeasurableSet (rawOmitted raw e chi m omega J5) :=
  (measurableSet_originalBox raw).diff (rawRetained_measurable raw e chi m omega J5)

theorem rawRetained_eq_union_children (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    rawRetained raw e chi m omega J5 =
      ⋃ c ∈ (Finset.univ : Finset ChildIndex), retainedChild raw c e chi m omega J5 := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, hc⟩ := parent_covered_by_child raw hgrid t ht.1
    exact mem_iUnion₂.mpr ⟨c, Finset.mem_univ _, hc, ht.2⟩
  · intro ht
    obtain ⟨c, _, hc⟩ := mem_iUnion₂.mp ht
    exact ⟨child_subset_parent raw hgrid c hc.1, hc.2⟩

theorem rawOmitted_eq_union_children (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    rawOmitted raw e chi m omega J5 =
      ⋃ c ∈ (Finset.univ : Finset ChildIndex), omittedChild raw c e chi m omega J5 := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, hc⟩ := parent_covered_by_child raw hgrid t ht.1
    refine mem_iUnion₂.mpr ⟨c, Finset.mem_univ _, hc, ?_⟩
    intro hret
    exact ht.2 ⟨ht.1, hret.2⟩
  · intro ht
    obtain ⟨c, _, hc⟩ := mem_iUnion₂.mp ht
    refine ⟨child_subset_parent raw hgrid c hc.1, ?_⟩
    intro hret
    exact hc.2 ⟨hc.1, hret.2⟩

theorem retained_children_pairwise (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) :
    Set.PairwiseDisjoint (Set.univ : Set ChildIndex)
      (fun c => retainedChild raw c e chi m omega J5) := by
  intro a ha b hb hab
  exact ((children_pairwise_disjoint raw) ha hb hab).mono inter_subset_left inter_subset_left

theorem omitted_children_pairwise (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) :
    Set.PairwiseDisjoint (Set.univ : Set ChildIndex)
      (fun c => omittedChild raw c e chi m omega J5) := by
  intro a ha b hb hab
  exact ((children_pairwise_disjoint raw) ha hb hab).mono sdiff_subset sdiff_subset

/-- Constant-one integration proves exact finite real-volume additivity;
no factor 64 is lost in converting ENNReal to real volume. -/
theorem rawRetained_real_volume_eq_sum_children
    (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    volume.real (rawRetained raw e chi m omega J5) =
      ∑ c : ChildIndex, volume.real (retainedChild raw c e chi m omega J5) := by
  calc
    volume.real (rawRetained raw e chi m omega J5) =
        ∫ _ : Point in rawRetained raw e chi m omega J5, (1 : ℝ) := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
    _ = _ := by
      rw [rawRetained_eq_union_children raw hgrid]
      rw [integral_biUnion_finset (Finset.univ : Finset ChildIndex)
        (fun c _ => retainedChild_measurable raw c e chi m omega J5)
        (retained_children_pairwise raw e chi m omega J5)
        (fun c _ => integrableOn_const (childSubset_volume_lt_top raw c inter_subset_left).ne)]
      simp only [setIntegral_const, smul_eq_mul, mul_one]

theorem rawOmitted_real_volume_eq_sum_children
    (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    volume.real (rawOmitted raw e chi m omega J5) =
      ∑ c : ChildIndex, volume.real (omittedChild raw c e chi m omega J5) := by
  calc
    volume.real (rawOmitted raw e chi m omega J5) =
        ∫ _ : Point in rawOmitted raw e chi m omega J5, (1 : ℝ) := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
    _ = _ := by
      rw [rawOmitted_eq_union_children raw hgrid]
      rw [integral_biUnion_finset (Finset.univ : Finset ChildIndex)
        (fun c _ => omittedChild_measurable raw c e chi m omega J5)
        (omitted_children_pairwise raw e chi m omega J5)
        (fun c _ => integrableOn_const (childSubset_volume_lt_top raw c sdiff_subset).ne)]
      simp only [setIntegral_const, smul_eq_mul, mul_one]

/-- This is the exact interface from all64 Jensen reserves to one raw B13
mass/modulus budget. Both sets retain the actual selected original policy. -/
theorem sum64_reserve_eq_single_raw_reserve
    (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    (∑ c : ChildIndex, childOwnerReserve raw c e chi m omega J5) =
      rowMassBound raw * volume.real (rawOmitted raw e chi m omega J5) +
        rowModulus raw e * volume.real (rawRetained raw e chi m omega J5) := by
  rw [sum_childOwnerReserve_eq_two_terms,
    ← rawOmitted_real_volume_eq_sum_children raw hgrid,
    ← rawRetained_real_volume_eq_sum_children raw hgrid]

/-- The raw grid400 parent has its original physical volume once. -/
theorem rawBox_real_volume (raw : FifthWireRow) (hgrid : raw.grid = 400) :
    volume.real raw.originalBox = 1 / (400 : ℝ)^5 := by
  rw [Measure.real, rawBox_volume raw hgrid, ENNReal.toReal_ofReal (by positivity)]

end
end ImbalancedChen.P5AllChildrenReserveReassembly
