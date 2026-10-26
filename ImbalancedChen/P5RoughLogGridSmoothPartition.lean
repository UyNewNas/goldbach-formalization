import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import ImbalancedChen.LogPrimeBoxMesh
import Mathlib.Topology.Algebra.Support

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual finite rough-log-grid label weights are consecutive differences
of ONE canonical monotone smooth step. Their sum telescopes exactly;
there is no bump normalization or assumed partition certificate. The
left enlargement and right endpoint strip are retained pointwise,
including every arithmetic prime on a literal endpoint.
-/
namespace ImbalancedChen.P5Z.RoughLogGridSmoothPartition
noncomputable section
open Set Classical
open scoped BigOperators
open P4B

def left (a b : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ := logPrimeMeshPoint a b n j.val
def right (a b : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ := logPrimeMeshPoint a b n (j.val + 1)

def label (a b : ℝ) (n : ℕ) (δ : ℝ) (j : Fin (n + 1)) (x : ℝ) : ℝ :=
  smoothGateUpperStep δ (x - left a b n j) - smoothGateUpperStep δ (x - right a b n j)

theorem left_le_right {a b : ℝ} (hab : a ≤ b) (n : ℕ) (j : Fin (n + 1)) :
    left a b n j ≤ right a b n j := logPrimeMeshPoint_mono hab n (Nat.le_succ _)

theorem label_bounds {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (n : ℕ) (j : Fin (n + 1)) (x : ℝ) :
    0 ≤ label a b n δ j x ∧ label a b n δ j x ≤ 1 := by
  have hlr := left_le_right hab n j
  have hmono := monotone_smoothGateUpperStep hδ (show x - right a b n j ≤ x - left a b n j by linarith)
  have hl := smoothGateUpperStep_bounds δ (x - left a b n j)
  have hr := smoothGateUpperStep_bounds δ (x - right a b n j)
  unfold label
  constructor <;> linarith

/-- EXACT finite telescoping, before any limiting measure or prime sum. -/
theorem sum_labels (a b : ℝ) (n : ℕ) (δ x : ℝ) :
    (∑ j : Fin (n + 1), label a b n δ j x) =
      smoothGateUpperStep δ (x - a) - smoothGateUpperStep δ (x - b) := by
  unfold label left right
  rw [Fin.sum_univ_eq_sum_range]
  simpa only [logPrimeMeshPoint_zero, logPrimeMeshPoint_last] using
    Finset.sum_range_sub' (fun k : ℕ => smoothGateUpperStep δ (x - logPrimeMeshPoint a b n k)) (n + 1)

theorem sum_labels_bounds {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (n : ℕ) (x : ℝ) :
    0 ≤ ∑ j : Fin (n + 1), label a b n δ j x ∧
      (∑ j : Fin (n + 1), label a b n δ j x) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => (label_bounds hab hδ n j x).1)
  · rw [sum_labels]
    linarith [(smoothGateUpperStep_bounds δ (x - a)).2, (smoothGateUpperStep_bounds δ (x - b)).1]

/-- Partition plateau on the ACTUAL interior carrier. The upper boundary
strip is not discarded; its endpoint x=b-delta is included in the plateau. -/
theorem sum_labels_eq_one {a b δ x : ℝ} (hδ : 0 < δ) (ha : a ≤ x) (hb : x ≤ b - δ) (n : ℕ) :
    (∑ j : Fin (n + 1), label a b n δ j x) = 1 := by
  have hl : smoothGateUpperStep δ (x - a) = 1 := smoothGateUpperStep_eq_one hδ (by linarith)
  have hr : smoothGateUpperStep δ (x - b) = 0 := smoothGateUpperStep_eq_zero hδ (by linarith)
  rw [sum_labels, hl, hr, sub_zero]

theorem label_zero_left {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (j : Fin (n + 1)) {x : ℝ} (hx : x ≤ left a b n j - δ) : label a b n δ j x = 0 := by
  have hlr := left_le_right hab n j
  have hl : smoothGateUpperStep δ (x - left a b n j) = 0 := smoothGateUpperStep_eq_zero hδ (by linarith)
  have hr : smoothGateUpperStep δ (x - right a b n j) = 0 := smoothGateUpperStep_eq_zero hδ (by linarith)
  rw [label, hl, hr, sub_self]

theorem label_zero_right {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (j : Fin (n + 1)) {x : ℝ} (hx : right a b n j ≤ x) : label a b n δ j x = 0 := by
  have hlr := left_le_right hab n j
  have hl : smoothGateUpperStep δ (x - left a b n j) = 1 := smoothGateUpperStep_eq_one hδ (by linarith)
  have hr : smoothGateUpperStep δ (x - right a b n j) = 1 := smoothGateUpperStep_eq_one hδ (by linarith)
  rw [label, hl, hr, sub_self]

/-- Nonzero label support is an ENLARGED original cell with exact strict
support endpoints. No arithmetic disjointness of labels is claimed. -/
theorem label_nonzero_support {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (j : Fin (n + 1)) {x : ℝ} (hx : label a b n δ j x ≠ 0) :
    left a b n j - δ < x ∧ x < right a b n j := by
  constructor
  · exact lt_of_not_ge (fun h => hx (label_zero_left hab hδ n j h))
  · exact lt_of_not_ge (fun h => hx (label_zero_right hab hδ n j h))

theorem contDiff_label (a b : ℝ) (n : ℕ) (δ : ℝ) (j : Fin (n + 1)) {k : ℕ∞} :
    ContDiff ℝ k (label a b n δ j) :=
  ((contDiff_smoothGateUpperStep δ).comp (contDiff_id.sub contDiff_const)).sub
    ((contDiff_smoothGateUpperStep δ).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_label {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (n : ℕ) (j : Fin (n + 1)) : HasCompactSupport (label a b n δ j) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (left a b n j - δ) (right a b n j)))
  intro x hx
  have h := label_nonzero_support hab hδ n j hx
  exact ⟨h.1.le, h.2.le⟩

def literal (a b x : ℝ) : ℝ := if a ≤ x ∧ x < b then 1 else 0

/-- Exact endpoint reserve for the telescoped partition versus the
literal inclusive-lower/strict-upper rough carrier. -/
def endpointReserve (a b δ x : ℝ) : Prop :=
  (a - δ < x ∧ x < a) ∨ (b - δ < x ∧ x < b)

theorem partition_error_supported {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (n : ℕ) (x : ℝ)
    (he : (∑ j : Fin (n + 1), label a b n δ j x) - literal a b x ≠ 0) : endpointReserve a b δ x := by
  by_cases ha : x < a
  · left
    refine ⟨?_, ha⟩
    by_contra hn
    have hx : x ≤ a - δ := le_of_not_gt hn
    have hl : smoothGateUpperStep δ (x - a) = 0 := smoothGateUpperStep_eq_zero hδ (by linarith)
    have hr : smoothGateUpperStep δ (x - b) = 0 := smoothGateUpperStep_eq_zero hδ (by linarith)
    exact he (by simp [sum_labels, literal, not_le.mpr ha, hl, hr])
  · have hax : a ≤ x := le_of_not_gt ha
    have hxb : x < b := by
      by_contra hn
      have hb : b ≤ x := le_of_not_gt hn
      have hl : smoothGateUpperStep δ (x - a) = 1 := smoothGateUpperStep_eq_one hδ (by linarith)
      have hr : smoothGateUpperStep δ (x - b) = 1 := smoothGateUpperStep_eq_one hδ (by linarith)
      exact he (by simp [sum_labels, literal, not_lt.mpr hb, hl, hr])
    right
    refine ⟨?_, hxb⟩
    by_contra hn
    have hx : x ≤ b - δ := le_of_not_gt hn
    exact he (by simp [sum_labels_eq_one hδ hax hx n, literal, hax, hxb])

end
end ImbalancedChen.P5Z.RoughLogGridSmoothPartition
