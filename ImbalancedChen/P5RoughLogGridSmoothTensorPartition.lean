import ImbalancedChen.P5RoughLogGridSmoothPrimeWeights
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Group.Bounded

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual rank-r rough-label tensors, including r=0. Their finite sum is
exactly the product of the telescoped scalar partitions. Thus overlapping
enlarged labels have a proved subpartition, and the original-prime pullback
is multiplicatively separated. At fixed mesh/width all tensors share a
global full Frechet derivative budget chosen before N. Only literal carrier
endpoint strips can contribute to the tensor partition error.
-/
namespace ImbalancedChen.P5Z.RoughLogGridSmoothPartition
noncomputable section
open Set Classical
open scoped BigOperators

abbrev Labels (r n : ℕ) := Fin r → Fin (n + 1)

def tensor {r : ℕ} (a b : ℝ) (n : ℕ) (δ : ℝ) (j : Labels r n) (v : Fin r → ℝ) : ℝ :=
  ∏ i : Fin r, label a b n δ (j i) (v i)

def tensorLiteral {r : ℕ} (a b : ℝ) (v : Fin r → ℝ) : ℝ :=
  ∏ i : Fin r, literal a b (v i)

theorem tensor_nonneg {r : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (j : Labels r n) (v : Fin r → ℝ) : 0 ≤ tensor a b n δ j v :=
  Finset.prod_nonneg (fun i _ => (label_bounds hab hδ n (j i) (v i)).1)

/-- Exact finite POU tensorization, rather than an assumed family budget. -/
theorem sum_tensors {r : ℕ} (a b : ℝ) (n : ℕ) (δ : ℝ) (v : Fin r → ℝ) :
    (∑ j : Labels r n, tensor a b n δ j v) =
      ∏ i : Fin r, ∑ j : Fin (n + 1), label a b n δ j (v i) :=
  (Fintype.prod_sum (fun (i : Fin r) (j : Fin (n + 1)) => label a b n δ j (v i))).symm

theorem sum_tensors_subpartition {r : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (v : Fin r → ℝ) :
    0 ≤ ∑ j : Labels r n, tensor a b n δ j v ∧
      (∑ j : Labels r n, tensor a b n δ j v) ≤ 1 := by
  rw [sum_tensors]
  constructor
  · exact Finset.prod_nonneg (fun i _ => (sum_labels_bounds hab hδ n (v i)).1)
  · apply (Finset.prod_le_prod (fun i _ => (sum_labels_bounds hab hδ n (v i)).1)
      (fun i _ => (sum_labels_bounds hab hδ n (v i)).2)).trans_eq
    simp

theorem sum_tensors_eq_one {r : ℕ} {a b δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (v : Fin r → ℝ) (hinterior : ∀ i, a ≤ v i ∧ v i ≤ b - δ) :
    (∑ j : Labels r n, tensor a b n δ j v) = 1 := by
  rw [sum_tensors]
  calc
    (∏ i : Fin r, ∑ j : Fin (n + 1), label a b n δ j (v i)) = ∏ _i : Fin r, (1 : ℝ) :=
      Finset.prod_congr rfl (fun i _ => sum_labels_eq_one hδ (hinterior i).1 (hinterior i).2 n)
    _ = 1 := by simp

theorem tensor_error_supported {r : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (v : Fin r → ℝ)
    (he : (∑ j : Labels r n, tensor a b n δ j v) - tensorLiteral a b v ≠ 0) :
    ∃ i : Fin r, endpointReserve a b δ (v i) := by
  by_contra hn
  push_neg at hn
  have hcoord (i : Fin r) : (∑ j : Fin (n + 1), label a b n δ j (v i)) = literal a b (v i) := by
    apply eq_of_sub_eq_zero
    by_contra he'
    exact hn i (partition_error_supported hab hδ n (v i) he')
  apply he
  rw [sum_tensors]
  have hp := Finset.prod_congr rfl (fun (i : Fin r) _ => hcoord i)
  change (∏ i : Fin r, ∑ j : Fin (n + 1), label a b n δ j (v i)) -
    (∏ i : Fin r, literal a b (v i)) = 0
  rw [hp, sub_self]

theorem tensor_nonzero_support {r : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (j : Labels r n) (v : Fin r → ℝ) (hne : tensor a b n δ j v ≠ 0) :
    ∀ i, left a b n (j i) - δ < v i ∧ v i < right a b n (j i) := by
  intro i
  apply label_nonzero_support hab hδ n (j i)
  intro hz
  exact hne (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem contDiff_tensor {r : ℕ} (a b : ℝ) (n : ℕ) (δ : ℝ) (j : Labels r n) :
    ContDiff ℝ ∞ (tensor a b n δ j) := by
  unfold tensor
  apply contDiff_prod
  intro i _
  exact (contDiff_label a b n δ (j i)).comp (contDiff_apply ℝ ℝ i)

theorem hasCompactSupport_tensor {r : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (j : Labels r n) : HasCompactSupport (tensor a b n δ j) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi (fun i : Fin r => (isCompact_Icc : IsCompact
      (Icc (left a b n (j i) - δ) (right a b n (j i))))))
  intro v hv i _
  have hs := tensor_nonzero_support hab hδ n j v hv i
  exact ⟨hs.1.le, hs.2.le⟩

/-- Genuine operator-norm budget for the actual tensor, including all
mixed derivatives. Every parameter is fixed before the prime scale N. -/
theorem exists_tensor_derivative_budget {r : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (j : Labels r n) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin r → ℝ, ‖iteratedFDeriv ℝ k (tensor a b n δ j) v‖ ≤ C := by
  let f := iteratedFDeriv ℝ k (tensor a b n δ j)
  have hcont : Continuous f :=
    ((contDiff_tensor a b n δ j).of_le (by simp : (k : ℕ∞) ≤ ∞)).continuous_iteratedFDeriv'
  have hcompact : HasCompactSupport f := (hasCompactSupport_tensor hab hδ n j).iteratedFDeriv k
  obtain ⟨B, hB⟩ := (show IsCompact (tsupport f) from hcompact).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro v
  by_cases hv : v ∈ tsupport f
  · exact (hB v hv).trans (le_max_left _ _)
  · have hz : f v = 0 := by
      by_contra hn
      exact hv (subset_closure hn)
    simpa only [hz, norm_zero] using (le_max_right B 0)

/-- One fixed-grid budget for EVERY label, before N and every prime tuple. -/
theorem exists_all_tensor_derivative_budget (r : ℕ) {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Labels r n) (v : Fin r → ℝ),
      ‖iteratedFDeriv ℝ k (tensor a b n δ j) v‖ ≤ C := by
  choose C hC hb using (fun j : Labels r n => exists_tensor_derivative_budget hab hδ n j k)
  refine ⟨∑ j : Labels r n, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j v
  exact (hb j v).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ j))

def primeTensor {r : ℕ} (N : ℕ) (a b : ℝ) (n : ℕ) (δ : ℝ) (j : Labels r n)
    (p : Fin r → ℕ) : ℝ := tensor a b n δ j (actualPrimeTupleLog N p)

theorem primeTensor_separated {r : ℕ} (N : ℕ) (a b : ℝ) (n : ℕ) (δ : ℝ)
    (j : Labels r n) (p : Fin r → ℕ) :
    primeTensor N a b n δ j p = ∏ i : Fin r, primeLabel N a b n δ (j i) (p i) := rfl

theorem primeTensor_subpartition {r : ℕ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (N n : ℕ) (p : Fin r → ℕ) :
    (∀ j : Labels r n, 0 ≤ primeTensor N a b n δ j p) ∧
      (∑ j : Labels r n, primeTensor N a b n δ j p) ≤ 1 :=
  ⟨fun j => tensor_nonneg hab hδ n j _, (sum_tensors_subpartition hab hδ n _).2⟩

end
end ImbalancedChen.P5Z.RoughLogGridSmoothPartition
