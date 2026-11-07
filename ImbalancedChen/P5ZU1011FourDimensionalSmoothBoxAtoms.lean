import ImbalancedChen.P5ZU1011CompactLogIntervalSmoothing
import ImbalancedChen.P5ZU1011OriginalFifteenNativeGridCells

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Separated smooth boxes in all FOUR original prime coordinates. The finite
inner and outer sums bracket the literal union of owned Ico mesh cells.
Their error is supported on the actual coordinate face reserves, including
arithmetic equality at a face. Every mixed derivative is computed, with a
constant independent of the mesh, row, N and smoothing width.
-/
namespace ImbalancedChen.P5Z.U1011FourDimensionalSmoothBoxAtoms
noncomputable section
open Set Classical
open scoped BigOperators
open U11Integral U1011OriginalFifteenNativeGridCells
open U1011CompactLogIntervalSmoothing

def boxAtom (inner : Bool) (δ : ℝ) (n : ℕ) (j : Grid n) (v : LogFour) : ℝ :=
  ∏ i : Fin 4, weight inner δ
    (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
    (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i) (v i)

def boxLiteral (n : ℕ) (j : Grid n) (v : LogFour) : ℝ :=
  ∏ i : Fin 4, literal
    (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
    (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i) (v i)

def smoothCover (inner : Bool) (δ : ℝ) {n : ℕ} (J : Finset (Grid n)) (v : LogFour) : ℝ :=
  ∑ j ∈ J, boxAtom inner δ n j v

def literalCover {n : ℕ} (J : Finset (Grid n)) (v : LogFour) : ℝ :=
  ∑ j ∈ J, boxLiteral n j v

def faceReserve (inner : Bool) (δ : ℝ) {n : ℕ} (J : Finset (Grid n)) (v : LogFour) : Prop :=
  ∃ j ∈ J, ∃ i : Fin 4,
    if inner then innerReserve δ
      (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
      (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i) (v i)
    else outerReserve δ
      (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
      (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i) (v i)

theorem boxLiteral_eq_indicator (n : ℕ) (j : Grid n) (v : LogFour) :
    boxLiteral n j v = if v ∈ cell n j then 1 else 0 := by
  by_cases hv : v ∈ cell n j
  · have h := mem_logPrimeMeshCell.mp hv
    simp [boxLiteral, literal, h, hv]
  · rw [if_neg hv]
    have hbad : ∃ i : Fin 4, ¬ (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i ≤ v i ∧
        v i < logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i) := by
      by_contra h
      push_neg at h
      exact hv (mem_logPrimeMeshCell.mpr h)
    obtain ⟨i, hi⟩ := hbad
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [literal, hi]

theorem boxAtom_bounds (inner : Bool) (δ : ℝ) (n : ℕ) (j : Grid n) (v : LogFour) :
    0 ≤ boxAtom inner δ n j v ∧ boxAtom inner δ n j v ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i hi => (bounds inner δ _ _ _).1)
  · apply (Finset.prod_le_prod (fun i hi => (bounds inner δ _ _ _).1)
      (fun i hi => (bounds inner δ _ _ _).2)).trans_eq
    simp

theorem inner_box_le_literal {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (j : Grid n) (v : LogFour) :
    boxAtom true δ n j v ≤ boxLiteral n j v := by
  apply Finset.prod_le_prod (fun i hi => (bounds true δ _ _ _).1)
  intro i hi
  exact inner_le_literal hδ _ _ _

theorem literal_le_outer_box {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (j : Grid n) (v : LogFour) :
    boxLiteral n j v ≤ boxAtom false δ n j v := by
  apply Finset.prod_le_prod
  · intro i hi
    unfold literal
    split_ifs <;> norm_num
  · intro i hi
    exact literal_le_outer hδ _ _ _

/-- This is a pointwise arithmetic sandwich; it does not identify any
boundary atom with a null set. -/
theorem finite_cover_sandwich {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (J : Finset (Grid n)) (v : LogFour) :
    smoothCover true δ J v ≤ literalCover J v ∧
      literalCover J v ≤ smoothCover false δ J v := by
  exact ⟨Finset.sum_le_sum (fun j hj => inner_box_le_literal hδ n j v),
    Finset.sum_le_sum (fun j hj => literal_le_outer_box hδ n j v)⟩

theorem literalCover_owned {n : ℕ} (J : Finset (Grid n)) {v : LogFour} (hv : v ∈ cube) :
    literalCover J v = if owner n v ∈ J then 1 else 0 := by
  unfold literalCover
  by_cases ho : owner n v ∈ J
  · rw [if_pos ho, Finset.sum_eq_single (owner n v)]
    · rw [boxLiteral_eq_indicator, if_pos (owner_mem n hv)]
    · intro j hj hne
      rw [boxLiteral_eq_indicator, if_neg]
      exact fun hjv => hne (owner_eq_of_mem n hjv).symm
    · exact fun hn => (hn ho).elim
  · rw [if_neg ho]
    apply Finset.sum_eq_zero
    intro j hj
    rw [boxLiteral_eq_indicator, if_neg]
    intro hjv
    exact ho ((owner_eq_of_mem n hjv).symm ▸ hj)

/-- No smoothing error occurs away from the genuine finite face reserve. -/
theorem cover_error_supported {δ : ℝ} (hδ : 0 < δ) (inner : Bool) {n : ℕ}
    (J : Finset (Grid n)) (v : LogFour)
    (he : smoothCover inner δ J v - literalCover J v ≠ 0) : faceReserve inner δ J v := by
  by_contra hn
  apply he
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro i hi
  have hnot : ¬ (if inner then innerReserve δ
      (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
      (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i) (v i)
    else outerReserve δ
      (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
      (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i) (v i)) :=
    fun h => hn ⟨j, hj, i, h⟩
  cases inner with
  | false =>
    apply eq_of_sub_eq_zero
    by_contra heq
    exact hnot (outer_error_support hδ heq)
  | true =>
    apply Eq.symm
    apply eq_of_sub_eq_zero
    by_contra heq
    exact hnot (inner_error_support hδ heq)

theorem contDiff_boxAtom (inner : Bool) (δ : ℝ) (n : ℕ) (j : Grid n) :
    ContDiff ℝ ∞ (boxAtom inner δ n j) := by
  apply contDiff_prod
  intro i hi
  exact (contDiff_weight inner δ _ _).comp (contDiff_apply ℝ ℝ i)

/-- The mixed derivative is an actual nested scalar derivative in the
four labelled original coordinates, with the labels held fixed. -/
def mixedJet (k : Fin 4 → ℕ) (inner : Bool) (δ : ℝ) (n : ℕ) (j : Grid n) (v : LogFour) : ℝ :=
  iteratedDeriv (k 3) (fun x3 => iteratedDeriv (k 2) (fun x2 =>
    iteratedDeriv (k 1) (fun x1 => iteratedDeriv (k 0)
      (fun x0 => boxAtom inner δ n j ![x0, x1, x2, x3]) (v 0)) (v 1)) (v 2)) (v 3)

theorem mixedJet_eq_product (k : Fin 4 → ℕ) (inner : Bool) (δ : ℝ)
    (n : ℕ) (j : Grid n) (v : LogFour) :
    mixedJet k inner δ n j v = ∏ i : Fin 4,
      iteratedDeriv (k i) (weight inner δ
        (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
        (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i)) (v i) := by
  simp only [mixedJet, boxAtom, Fin.prod_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field]

/-- The quantitative derivative budget is constructed from the actual
canonical scalar step; it is not a test-norm hypothesis. -/
theorem exists_mixedJet_budget (k : Fin 4 → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (inner : Bool) (δ : ℝ), 0 < δ →
      ∀ (n : ℕ) (j : Grid n) (v : LogFour),
        |mixedJet k inner δ n j v| ≤ C / δ ^ (∑ i : Fin 4, k i) := by
  choose C hC hbound using fun i : Fin 4 => exists_derivative_budget (k i)
  refine ⟨∏ i : Fin 4, C i, Finset.prod_nonneg (fun i hi => hC i), ?_⟩
  intro inner δ hδ n j v
  rw [mixedJet_eq_product, Finset.abs_prod]
  calc
    _ ≤ ∏ i : Fin 4, C i / δ ^ (k i) :=
      Finset.prod_le_prod (fun i hi => abs_nonneg _)
        (fun i hi => hbound i inner δ hδ _ _ _)
    _ = (∏ i : Fin 4, C i) / δ ^ (∑ i : Fin 4, k i) := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

/-- Substitution uses the actual original prime-log dictionary. Each
factor depends on ONE prime; no residual quotient is used as the scale. -/
theorem native_boxAtom_separated (inner : Bool) (δ : ℝ) (n N : ℕ)
    (j : Grid n) (p : Fin 4 → ℕ) :
    boxAtom inner δ n j (actualPrimeTupleLog N p) = ∏ i : Fin 4,
      weight inner δ (logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i)
        (logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i)
        (Real.log (p i : ℝ) / Real.log (N : ℝ)) := rfl

end
end ImbalancedChen.P5Z.U1011FourDimensionalSmoothBoxAtoms
