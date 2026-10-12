import ImbalancedChen.ActualPrimeBoxMass
import ImbalancedChen.LogPrimeBoxMesh
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuous test functions for actual prime tuples

The target-linked prime tuple sums are transferred to genuine Lebesgue
integrals on a fixed common-endpoint logarithmic cube. Functions may have
either sign. Finite Ico partitions, positivity of the arithmetic weights,
and uniform continuity on the compact closure provide both error estimates.
No convergence or approximation-error assumption is imported.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

/-- Logarithmic coordinates of an actual tuple, retaining the target N. -/
def actualPrimeTupleLog {k : ℕ} (N : ℕ) (p : Fin k → ℕ) : Fin k → ℝ :=
  fun i => Real.log (p i : ℝ) / Real.log (N : ℝ)

/-- The weighted sum is over the actual finite arithmetic carrier. -/
def actualPrimeBoxTestSum {k : ℕ} (N : ℕ) (a b : Fin k → ℝ)
    (f : (Fin k → ℝ) → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N a b,
    (∏ i, 1 / ((p i : ℝ) - 1)) * f (actualPrimeTupleLog N p)

theorem actualPrimeTupleLog_rpow {k N : ℕ} (hN : 1 < N)
    (p : Fin k → ℕ) (hp : ∀ i, 0 < p i) (i : Fin k) :
    (N : ℝ) ^ (actualPrimeTupleLog N p i) = p i := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  apply (Real.mul_log_eq_log_iff (lt_trans zero_lt_one hN') (by exact_mod_cast hp i)).mp
  exact div_mul_cancel₀ _ (Real.log_pos hN').ne'

/-- The exact power endpoints are equivalent to half-open logarithmic
coordinates. Primality and target exclusion are retained separately. -/
theorem mem_actualPrimeBoxTuples_log_iff {k N : ℕ} (hN : 1 < N)
    (a b : Fin k → ℝ) (p : Fin k → ℕ) :
    p ∈ actualPrimeBoxTuples N a b ↔
      (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N) ∧ actualPrimeTupleLog N p ∈ logPrimeBox a b := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hp
    refine ⟨fun i => ⟨(hi i).1, (hi i).2.1⟩, mem_logPrimeBox.mpr (fun i => ?_)⟩
    have hpow := actualPrimeTupleLog_rpow hN p (fun j => (hi j).1.pos) i
    exact ⟨(Real.rpow_le_rpow_left_iff hN').mp (hpow.symm ▸ (hi i).2.2.1),
      (Real.rpow_lt_rpow_left_iff hN').mp (hpow.symm ▸ (hi i).2.2.2)⟩
  · rintro ⟨hp, hx⟩
    refine mem_actualPrimeBoxTuples_iff.mpr (fun i => ⟨(hp i).1, (hp i).2, ?_, ?_⟩)
    · rw [← actualPrimeTupleLog_rpow hN p (fun j => (hp j).1.pos) i]
      exact (Real.rpow_le_rpow_left_iff hN').mpr (mem_logPrimeBox.mp hx i).1
    · rw [← actualPrimeTupleLog_rpow hN p (fun j => (hp j).1.pos) i]
      exact (Real.rpow_lt_rpow_left_iff hN').mpr (mem_logPrimeBox.mp hx i).2

private theorem actualPrimeBox_mesh_partition {k N : ℕ} {a b : ℝ}
    (hN : 1 < N) (hab : a < b) (m : ℕ) :
    actualPrimeBoxTuples N (fun _ : Fin k => a) (fun _ => b) =
      Finset.univ.biUnion (fun j : Fin k → Fin (m + 1) =>
        actualPrimeBoxTuples N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j)) := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro hp
    obtain ⟨hprime, hx⟩ := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell a b m hx
    exact ⟨j, (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr ⟨hprime, hj⟩⟩
  · rintro ⟨j, hj⟩
    obtain ⟨hprime, hx⟩ := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hj
    exact (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
      ⟨hprime, logPrimeMeshCell_subset_box hab m j hx⟩

private theorem actualPrimeBox_mesh_disjoint {k N : ℕ} {a b : ℝ}
    (hN : 1 < N) (hab : a < b) (m : ℕ) :
    (Set.univ : Set (Fin k → Fin (m + 1))).Pairwise (fun j r =>
      Disjoint (actualPrimeBoxTuples N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j))
        (actualPrimeBoxTuples N (logPrimeMeshLo a b m r) (logPrimeMeshHi a b m r))) := by
  intro j _ r _ hne
  rw [Finset.disjoint_left]
  intro p hpj hpr
  exact hne (logPrimeMeshCell_unique hab.le
    ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hpj).2
    ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hpr).2)

/-- Exact finite subdivision, before any asymptotic argument. -/
theorem actualPrimeBoxTestSum_mesh {k N : ℕ} {a b : ℝ}
    (hN : 1 < N) (hab : a < b) (m : ℕ) (f : (Fin k → ℝ) → ℝ) :
    actualPrimeBoxTestSum N (fun _ : Fin k => a) (fun _ => b) f =
      ∑ j : Fin k → Fin (m + 1),
        actualPrimeBoxTestSum N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j) f := by
  unfold actualPrimeBoxTestSum
  rw [actualPrimeBox_mesh_partition hN hab m, Finset.sum_biUnion]
  simpa only [Finset.coe_univ, Set.PairwiseDisjoint, Function.onFun] using
    actualPrimeBox_mesh_disjoint (k := k) hN hab m

/-- The mass itself has the identical exact subdivision. -/
theorem actualPrimeBoxMass_mesh {k N : ℕ} {a b : ℝ}
    (hN : 1 < N) (hab : a < b) (m : ℕ) :
    actualPrimeBoxMass N (fun _ : Fin k => a) (fun _ => b) =
      ∑ j : Fin k → Fin (m + 1),
        actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j) := by
  unfold actualPrimeBoxMass
  rw [actualPrimeBox_mesh_partition hN hab m, Finset.sum_biUnion]
  simpa only [Finset.coe_univ, Set.PairwiseDisjoint, Function.onFun] using
    actualPrimeBox_mesh_disjoint (k := k) hN hab m

private theorem logPrimeMesh_lo_mem_closure {k : ℕ} {a b : ℝ} (hab : a < b)
    (m : ℕ) (j : Fin k → Fin (m + 1)) :
    logPrimeMeshLo a b m j ∈ Set.univ.pi (fun _ : Fin k => Set.Icc a b) := by
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]
  exact fun i => ⟨(logPrimeMeshLoHi_bounds hab m j i).1,
    (logPrimeMeshLoHi_bounds hab m j i).2.1.le.trans
      (logPrimeMeshLoHi_bounds hab m j i).2.2⟩

private theorem logPrimeBox_mem_closure {k : ℕ} {a b : ℝ} {x : Fin k → ℝ}
    (hx : x ∈ logPrimeBox (fun _ => a) (fun _ => b)) :
    x ∈ Set.univ.pi (fun _ : Fin k => Set.Icc a b) := by
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]
  exact fun i => ⟨(mem_logPrimeBox.mp hx i).1, (mem_logPrimeBox.mp hx i).2.le⟩

/-- Uniform continuity supplies one finite mesh with a uniform absolute
oscillation bound on every cell, also for signed test functions. -/
theorem exists_logPrimeMesh_test_oscillation {k : ℕ} {a b : ℝ} (hab : a < b)
    (f : (Fin k → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin k => Set.Icc a b)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, ∀ (j : Fin k → Fin (m + 1)) (x : Fin k → ℝ),
      x ∈ logPrimeMeshCell a b m j → |f x - f (logPrimeMeshLo a b m j)| ≤ epsilon := by
  have hc : IsCompact (Set.univ.pi (fun _ : Fin k => Set.Icc a b)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨delta, hdelta, hosc⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hf) epsilon hepsilon
  obtain ⟨m, hm⟩ := ((tendsto_logPrimeMeshStep a b).eventually (gt_mem_nhds hdelta)).exists
  refine ⟨m, fun j x hx => ?_⟩
  have hd : dist x (logPrimeMeshLo a b m j) ≤ logPrimeMeshStep a b m := by
    apply (dist_pi_le_iff (logPrimeMeshStep_pos hab m).le).mpr
    intro i
    have hi := mem_logPrimeMeshCell.mp hx i
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hi.1)]
    linarith [logPrimeMeshHi_eq_lo_add_step a b m j i]
  have hh := hosc x (logPrimeBox_mem_closure (logPrimeMeshCell_subset_box hab m j hx))
    (logPrimeMeshLo a b m j) (logPrimeMesh_lo_mem_closure hab m j) (hd.trans_lt hm)
  exact (by simpa only [Real.dist_eq] using hh.le)

private theorem actualPrimeBoxTestSum_cell_error {k N m : ℕ} {a b epsilon : ℝ}
    (hN : 1 < N) (f : (Fin k → ℝ) → ℝ) (j : Fin k → Fin (m + 1))
    (hosc : ∀ x ∈ logPrimeMeshCell a b m j,
      |f x - f (logPrimeMeshLo a b m j)| ≤ epsilon) :
    |actualPrimeBoxTestSum N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j) f -
      f (logPrimeMeshLo a b m j) *
        actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j)| ≤
      epsilon * actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j) := by
  unfold actualPrimeBoxTestSum actualPrimeBoxMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ actualPrimeBoxTuples N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j),
        |(∏ i, 1 / ((p i : ℝ) - 1)) * f (actualPrimeTupleLog N p) -
          f (logPrimeMeshLo a b m j) * (∏ i, 1 / ((p i : ℝ) - 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ actualPrimeBoxTuples N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j),
        epsilon * (∏ i, 1 / ((p i : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hw := actualPrimeBoxWeight_nonneg hp
      have he := hosc (actualPrimeTupleLog N p)
        ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
      calc
        _ = (∏ i, 1 / ((p i : ℝ) - 1)) *
            |f (actualPrimeTupleLog N p) - f (logPrimeMeshLo a b m j)| := by
          rw [mul_comm (f (logPrimeMeshLo a b m j)), ← mul_sub, abs_mul, abs_of_nonneg hw]
        _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left he hw
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The arithmetic mesh error is paid by the actual total box mass.
Its proof is a finite exact partition and positive weights, not an asymptotic assumption. -/
theorem actualPrimeBoxTestSum_mesh_error {k N : ℕ} {a b epsilon : ℝ}
    (hN : 1 < N) (hab : a < b) (m : ℕ) (f : (Fin k → ℝ) → ℝ)
    (hosc : ∀ (j : Fin k → Fin (m + 1)) x, x ∈ logPrimeMeshCell a b m j →
      |f x - f (logPrimeMeshLo a b m j)| ≤ epsilon) :
    |actualPrimeBoxTestSum N (fun _ : Fin k => a) (fun _ => b) f -
      ∑ j : Fin k → Fin (m + 1), f (logPrimeMeshLo a b m j) *
        actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j)| ≤
      epsilon * actualPrimeBoxMass N (fun _ : Fin k => a) (fun _ => b) := by
  rw [actualPrimeBoxTestSum_mesh hN hab m, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin k → Fin (m + 1),
        |actualPrimeBoxTestSum N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j) f -
          f (logPrimeMeshLo a b m j) *
            actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin k → Fin (m + 1), epsilon *
        actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j) :=
      Finset.sum_le_sum (fun j _ => actualPrimeBoxTestSum_cell_error hN f j (hosc j))
    _ = _ := by rw [← Finset.mul_sum, ← actualPrimeBoxMass_mesh hN hab m]

/-- For a fixed finite mesh the genuine arithmetic step sum tends to the
corresponding product-logarithm sum. -/
theorem tendsto_actualPrimeBoxTestMesh {k : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (m : ℕ) (f : (Fin k → ℝ) → ℝ) :
    Tendsto (fun N : ℕ => ∑ j : Fin k → Fin (m + 1), f (logPrimeMeshLo a b m j) *
      actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j)) atTop
      (𝓝 (∑ j : Fin k → Fin (m + 1), f (logPrimeMeshLo a b m j) *
        ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i))) := by
  apply tendsto_finsetSum
  intro j _
  exact (tendsto_actualPrimeBoxMass _ _
    (fun i => ha.trans_le (logPrimeMeshLoHi_bounds hab m j i).1)
    (fun i => (logPrimeMeshLoHi_bounds hab m j i).2.1)).const_mul _

/-- The signed continuous test function times the reciprocal-coordinate
density is integrable on the half-open cube, by its compact closure. -/
theorem integrableOn_logPrimeBox_test_cube {k : ℕ} {a b : ℝ} (ha : 0 < a)
    (f : (Fin k → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin k => Set.Icc a b))) :
    IntegrableOn (fun x => f x * ∏ i, 1 / x i)
      (logPrimeBox (fun _ : Fin k => a) (fun _ => b)) := by
  have hd : ContinuousOn (fun x : Fin k → ℝ => ∏ i, 1 / x i)
      (Set.univ.pi (fun _ : Fin k => Set.Icc a b)) := by
    apply continuousOn_finsetProd
    intro i _
    apply continuousOn_const.div (continuous_apply i).continuousOn
    intro x hx
    exact (ha.trans_le (hx i (Set.mem_univ _)).1).ne'
  apply ((hf.mul hd).integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
  exact fun _ hx => logPrimeBox_mem_closure hx

private theorem integral_logPrimeBox_mesh {k : ℕ} {a b : ℝ} (hab : a < b)
    (m : ℕ) (g : (Fin k → ℝ) → ℝ)
    (hg : IntegrableOn g (logPrimeBox (fun _ : Fin k => a) (fun _ => b))) :
    (∫ x in logPrimeBox (fun _ : Fin k => a) (fun _ => b), g x) =
      ∑ j : Fin k → Fin (m + 1), ∫ x in logPrimeMeshCell a b m j, g x := by
  calc
    _ = ∫ x in ⋃ j : Fin k → Fin (m + 1), logPrimeMeshCell a b m j, g x := by
      rw [logPrimeMeshCells_union hab m]
    _ = _ := integral_iUnion_fintype (measurableSet_logPrimeMeshCell a b m)
      (fun j r hjr => logPrimeMeshCell_pairwiseDisjoint hab.le m
        (Set.mem_univ j) (Set.mem_univ r) hjr)
      (fun j => hg.mono_set (logPrimeMeshCell_subset_box hab m j))

private theorem logPrimeBox_mesh_logMass {k : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) :
    (∑ j : Fin k → Fin (m + 1),
      ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i)) =
      ∏ _i : Fin k, Real.log (b / a) := by
  rw [← integral_logPrimeBox_one_div (fun _ : Fin k => a) (fun _ => b)
    (fun _ => ha) (fun _ => hab.le), integral_logPrimeBox_mesh hab m _
      (integrableOn_logPrimeBox_one_div _ _ (fun _ => ha))]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_logPrimeBox_one_div _ _
    (fun i => ha.trans_le (logPrimeMeshLoHi_bounds hab m j i).1)
    (fun i => (logPrimeMeshLoHi_bounds hab m j i).2.1.le)).symm

private theorem integral_logPrimeBox_test_cell_error {k m : ℕ} {a b epsilon : ℝ}
    (ha : 0 < a) (hab : a < b) (f : (Fin k → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin k => Set.Icc a b)))
    (j : Fin k → Fin (m + 1))
    (hosc : ∀ x ∈ logPrimeMeshCell a b m j,
      |f x - f (logPrimeMeshLo a b m j)| ≤ epsilon) :
    |(∫ x in logPrimeMeshCell a b m j, f x * ∏ i, 1 / x i) -
      f (logPrimeMeshLo a b m j) *
        ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i)| ≤
      epsilon * ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i) := by
  have hlo (i : Fin k) : 0 < logPrimeMeshLo a b m j i :=
    ha.trans_le (logPrimeMeshLoHi_bounds hab m j i).1
  have hd := integrableOn_logPrimeBox_one_div (logPrimeMeshLo a b m j)
    (logPrimeMeshHi a b m j) hlo
  change IntegrableOn (fun x : Fin k → ℝ => ∏ i, 1 / x i) (logPrimeMeshCell a b m j) at hd
  have hfc := (integrableOn_logPrimeBox_test_cube ha f hf).mono_set
    (logPrimeMeshCell_subset_box hab m j)
  have hmass : (∫ x in logPrimeMeshCell a b m j, ∏ i, 1 / x i) =
      ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i) :=
    integral_logPrimeBox_one_div _ _ hlo (fun i => (logPrimeMeshLoHi_bounds hab m j i).2.1.le)
  rw [← hmass, ← integral_const_mul, ← integral_sub hfc (hd.const_mul _)]
  have hh := norm_integral_le_of_norm_le (hd.const_mul epsilon) (show
      ∀ᵐ x ∂volume.restrict (logPrimeMeshCell a b m j),
        ‖f x * (∏ i, 1 / x i) - f (logPrimeMeshLo a b m j) * (∏ i, 1 / x i)‖ ≤
          epsilon * (∏ i, 1 / x i) from by
    filter_upwards [ae_restrict_mem (measurableSet_logPrimeMeshCell a b m j)] with x hx
    have hnonneg : 0 ≤ ∏ i, 1 / x i := Finset.prod_nonneg (fun i _ =>
      (one_div_pos.mpr ((hlo i).trans_le (mem_logPrimeMeshCell.mp hx i).1)).le)
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_right (hosc x hx) hnonneg)
  rw [Real.norm_eq_abs, integral_const_mul] at hh
  exact hh

/-- The same finite mesh approximates the genuine signed Lebesgue integral
with error at most epsilon times its exact positive box mass. -/
theorem integral_logPrimeBox_test_mesh_error {k : ℕ} {a b epsilon : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) (f : (Fin k → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin k => Set.Icc a b)))
    (hosc : ∀ (j : Fin k → Fin (m + 1)) x, x ∈ logPrimeMeshCell a b m j →
      |f x - f (logPrimeMeshLo a b m j)| ≤ epsilon) :
    |(∫ x in logPrimeBox (fun _ : Fin k => a) (fun _ => b), f x * ∏ i, 1 / x i) -
      ∑ j : Fin k → Fin (m + 1), f (logPrimeMeshLo a b m j) *
        ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i)| ≤
      epsilon * ∏ _i : Fin k, Real.log (b / a) := by
  rw [integral_logPrimeBox_mesh hab m _ (integrableOn_logPrimeBox_test_cube ha f hf),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin k → Fin (m + 1),
        |(∫ x in logPrimeMeshCell a b m j, f x * ∏ i, 1 / x i) -
          f (logPrimeMeshLo a b m j) *
            ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin k → Fin (m + 1), epsilon *
        ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i) :=
      Finset.sum_le_sum (fun j _ => integral_logPrimeBox_test_cell_error ha hab f hf j (hosc j))
    _ = _ := by rw [← Finset.mul_sum, logPrimeBox_mesh_logMass ha hab m]

/-- Every real continuous test function on the compact closure transfers
from the actual target-linked prime tuples to the true logarithmic-cube
Lebesgue integral. No sign condition on the function and no arithmetic
ordering of tuple coordinates is imposed. -/
theorem tendsto_actualPrimeBoxTestSum_cube {k : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (f : (Fin k → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.univ.pi (fun _ : Fin k => Set.Icc a b))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N (fun _ : Fin k => a) (fun _ => b) f)
      atTop (𝓝 (∫ x in logPrimeBox (fun _ : Fin k => a) (fun _ => b),
        f x * ∏ i, 1 / x i)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let M : ℝ := ∏ _i : Fin k, Real.log (b / a)
  have hM : 0 ≤ M := Finset.prod_nonneg (fun _ _ =>
    Real.log_nonneg ((one_le_div ha).mpr hab.le))
  let eta : ℝ := epsilon / (4 * (M + 1))
  have heta : 0 < eta := div_pos hepsilon (by positivity)
  have hbudget : eta * (M + 1) = epsilon / 4 := by
    dsimp [eta]
    field_simp
  obtain ⟨m, hosc⟩ := exists_logPrimeMesh_test_oscillation hab f hf heta
  have hmass : ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin k => a) (fun _ => b) < M + 1 :=
    (tendsto_actualPrimeBoxMass _ _ (fun _ => ha) (fun _ => hab)).eventually
      (gt_mem_nhds (lt_add_one M))
  have hstep : ∀ᶠ N : ℕ in atTop,
      |(∑ j : Fin k → Fin (m + 1), f (logPrimeMeshLo a b m j) *
        actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j)) -
        ∑ j : Fin k → Fin (m + 1), f (logPrimeMeshLo a b m j) *
          ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i)| < epsilon / 2 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_actualPrimeBoxTestMesh ha hab m f) (epsilon / 2) (by positivity)
  have hi := integral_logPrimeBox_test_mesh_error ha hab m f hf hosc
  filter_upwards [eventually_gt_atTop (1 : ℕ), hmass, hstep] with N hN hmassN hstepN
  have he := actualPrimeBoxTestSum_mesh_error hN hab m f hosc
  let A := actualPrimeBoxTestSum N (fun _ : Fin k => a) (fun _ => b) f
  let B := ∑ j : Fin k → Fin (m + 1), f (logPrimeMeshLo a b m j) *
    actualPrimeBoxMass N (logPrimeMeshLo a b m j) (logPrimeMeshHi a b m j)
  let C := ∑ j : Fin k → Fin (m + 1), f (logPrimeMeshLo a b m j) *
    ∏ i, Real.log (logPrimeMeshHi a b m j i / logPrimeMeshLo a b m j i)
  let I := ∫ x in logPrimeBox (fun _ : Fin k => a) (fun _ => b), f x * ∏ i, 1 / x i
  change |A - B| ≤ eta * actualPrimeBoxMass N (fun _ : Fin k => a) (fun _ => b) at he
  change |B - C| < epsilon / 2 at hstepN
  change |I - C| ≤ eta * M at hi
  have hic : |C - I| ≤ eta * M := by simpa only [abs_sub_comm] using hi
  have hm := mul_lt_mul_of_pos_left hmassN heta
  rw [Real.dist_eq]
  change |A - I| < epsilon
  have htriangle : |A - I| ≤ |A - B| + (|B - C| + |C - I|) :=
    (abs_sub_le A B I).trans (add_le_add le_rfl (abs_sub_le B C I))
  nlinarith only [htriangle, he, hstepN, hic, hm, hbudget, heta]

end

end ImbalancedChen
