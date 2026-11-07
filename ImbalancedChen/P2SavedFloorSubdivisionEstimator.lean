import ImbalancedChen.P2SavedFloorSemantics

/-!
SOURCE_WRITTEN_UNCOMPILED / code-only, 2026-10-24.
The sibling draft P2SavedFloorSemantics.lean is the sole new dependency;
its directory must be on the module search path when compilation resumes.

This constructs a complete rectangular subdivision of an actual pair512
parent and a new finite lower estimator for its real ordinary integral.
The exact integral equals the sum of all subcell integrals. Every directed
Q80 corner floor has the analytic lower-bound semantics proved in the
sibling draft. The total decoded integer is a lower bound, and total floor
rounding loss, after the Chen /4, is at most M*N/(4*2^80).

The rounding bound compares the floored and unfloored CORNER estimators;
it does not bound the Darboux discretization error to the true integral.
No equality to the historical positive-row I80 evaluator is asserted.
-/

namespace ImbalancedChen.P2SavedFloorSubdivisionEstimator

noncomputable section

open MeasureTheory Set P2SavedFloorSemantics
open scoped Interval BigOperators

/-- Uniform points include both original endpoints. M>0 is explicit in
every subdivision theorem; M=0 is not silently treated as a partition. -/
def meshPoint (l r : ℝ) (M k : ℕ) : ℝ :=
  l + (r - l) * (k : ℝ) / (M : ℝ)

theorem meshPoint_zero (l r : ℝ) (M : ℕ) : meshPoint l r M 0 = l := by
  simp [meshPoint]

theorem meshPoint_end (l r : ℝ) {M : ℕ} (hM : 0 < M) :
    meshPoint l r M M = r := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [meshPoint, mul_div_cancel_right₀ _ hM0]
  ring

theorem meshPoint_mono {l r : ℝ} (hlr : l ≤ r) {M : ℕ} (hM : 0 < M)
    {i j : ℕ} (hij : i ≤ j) : meshPoint l r M i ≤ meshPoint l r M j := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hijr : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hijr (sub_nonneg.mpr hlr)) hMr.le
  exact add_le_add_left hm l

theorem meshPoint_mem {l r : ℝ} (hlr : l ≤ r) {M : ℕ} (hM : 0 < M)
    {i : ℕ} (hi : i ≤ M) : meshPoint l r M i ∈ Icc l r := by
  constructor
  · simpa only [meshPoint_zero] using meshPoint_mono hlr hM (Nat.zero_le i)
  · simpa only [meshPoint_end _ _ hM] using meshPoint_mono hlr hM hi

theorem meshPoint_pos {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    {M : ℕ} (hM : 0 < M) (i : ℕ) : 0 < meshPoint l r M i := by
  apply hl.trans_le
  simpa only [meshPoint_zero] using meshPoint_mono hlr hM (Nat.zero_le i)

def childIntegral (tl tr ul ur : ℝ) (M N i j : ℕ) : ℝ :=
  ordinaryCellIntegral (meshPoint tl tr M i) (meshPoint tl tr M (i + 1))
    (meshPoint ul ur N j) (meshPoint ul ur N (j + 1))

def childMass (tl tr ul ur : ℝ) (M N i j : ℕ) : ℝ :=
  ordinaryCornerMass (meshPoint tl tr M i) (meshPoint tl tr M (i + 1))
    (meshPoint ul ur N j) (meshPoint ul ur N (j + 1))

def childQ80 (tl tr ul ur : ℝ) (M N i j : ℕ) : ℕ :=
  directedCornerQ80 (meshPoint tl tr M i) (meshPoint tl tr M (i + 1))
    (meshPoint ul ur N j) (meshPoint ul ur N (j + 1))

def totalMass (tl tr ul ur : ℝ) (M N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, childMass tl tr ul ur M N i j

def totalQ80 (tl tr ul ur : ℝ) (M N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, childQ80 tl tr ul ur M N i j

/-- One t-strip is exactly the sum of its complete u-subdivision.
All cell and parameter integrability is supplied by the actual kernel. -/
theorem strip_integral_eq_sum {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    {N : ℕ} (hN : 0 < N) :
    ordinaryCellIntegral tl tr ul ur =
      ∑ j ∈ Finset.range N,
        ordinaryCellIntegral tl tr (meshPoint ul ur N j)
          (meshPoint ul ur N (j + 1)) := by
  have hinner : ∀ t ∈ Icc tl tr,
      (∫ u in ul..ur, ordinaryPairKernel t u) =
        ∑ j ∈ Finset.range N,
          ∫ u in meshPoint ul ur N j..meshPoint ul ur N (j + 1),
            ordinaryPairKernel t u := by
    intro t ht'
    have hs := intervalIntegral.sum_integral_adjacent_intervals
      (a := meshPoint ul ur N) (f := ordinaryPairKernel t) (μ := volume)
      (n := N) (fun j _hj => ordinaryPairKernel_intervalIntegrable
        (htl.trans_le ht'.1) (meshPoint_pos hul hu hN j)
        (meshPoint_mono hu hN (Nat.le_succ j)))
    simpa only [meshPoint_zero, meshPoint_end _ _ hN] using hs.symm
  unfold ordinaryCellIntegral
  calc
    (∫ t in tl..tr, ∫ u in ul..ur, ordinaryPairKernel t u) =
        ∫ t in tl..tr, ∑ j ∈ Finset.range N,
          ∫ u in meshPoint ul ur N j..meshPoint ul ur N (j + 1),
            ordinaryPairKernel t u := by
      apply intervalIntegral.integral_congr
      intro t ht'
      rw [Set.uIcc_of_le ht] at ht'
      exact hinner t ht'
    _ = ∑ j ∈ Finset.range N,
        ∫ t in tl..tr,
          ∫ u in meshPoint ul ur N j..meshPoint ul ur N (j + 1),
            ordinaryPairKernel t u := by
      apply intervalIntegral.integral_finsetSum
      intro j _hj
      exact ordinaryPairKernel_outer_intervalIntegrable htl
        (meshPoint_pos hul hu hN j) ht
        (meshPoint_mono hu hN (Nat.le_succ j))

/-- Complete two-dimensional additivity. The entire parent, rather than
only a selected collection of interior children, occurs in this equality. -/
theorem parent_integral_eq_sum_children {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    ordinaryCellIntegral tl tr ul ur =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
        childIntegral tl tr ul ur M N i j := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := meshPoint tl tr M)
    (f := fun t => ∫ u in ul..ur, ordinaryPairKernel t u) (μ := volume)
    (n := M) (fun i _hi => ordinaryPairKernel_outer_intervalIntegrable
      (meshPoint_pos htl ht hM i) hul
      (meshPoint_mono ht hM (Nat.le_succ i)) hu)
  have htSplit : ordinaryCellIntegral tl tr ul ur =
      ∑ i ∈ Finset.range M,
        ordinaryCellIntegral (meshPoint tl tr M i)
          (meshPoint tl tr M (i + 1)) ul ur := by
    simpa only [ordinaryCellIntegral, meshPoint_zero, meshPoint_end _ _ hM]
      using hs.symm
  rw [htSplit]
  apply Finset.sum_congr rfl
  intro i _hi
  exact strip_integral_eq_sum (meshPoint_pos htl ht hM i) hul
    (meshPoint_mono ht hM (Nat.le_succ i)) hu hN

theorem each_child_floor_lower {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (i j : ℕ) :
    savedQ80Value (childQ80 tl tr ul ur M N i j) ≤
      childIntegral tl tr ul ur M N i j := by
  exact directedCornerQ80_le_actual_integral
    (meshPoint_pos htl ht hM i) (meshPoint_pos hul hu hN j)
    (meshPoint_mono ht hM (Nat.le_succ i))
    (meshPoint_mono hu hN (Nat.le_succ j))

theorem decode_totalQ80 (tl tr ul ur : ℝ) (M N : ℕ) :
    savedQ80Value (totalQ80 tl tr ul ur M N) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
        savedQ80Value (childQ80 tl tr ul ur M N i j) := by
  simp [totalQ80, savedQ80Value, Finset.sum_div]

/-- The finite estimator is the decoded single natural integer obtained
by summing all children, and is below the true parent ordinary integral. -/
theorem totalQ80_lower_parent_integral {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    savedQ80Value (totalQ80 tl tr ul ur M N) ≤
      ordinaryCellIntegral tl tr ul ur := by
  rw [decode_totalQ80, parent_integral_eq_sum_children htl hul ht hu hM hN]
  exact Finset.sum_le_sum (fun i _hi => Finset.sum_le_sum
    (fun j _hj => each_child_floor_lower htl hul ht hu hM hN i j))

/-- A single directed floor loses less than one Q80 unit from the real
corner mass. This does not confuse corner quadrature error with rounding. -/
theorem cornerMass_lt_floor_add_unit (tl tr ul ur : ℝ) :
    ordinaryCornerMass tl tr ul ur <
      savedQ80Value (directedCornerQ80 tl tr ul ur) + 1 / q80 := by
  have hf := Nat.lt_floor_add_one (q80 * ordinaryCornerMass tl tr ul ur)
  calc
    ordinaryCornerMass tl tr ul ur =
        (q80 * ordinaryCornerMass tl tr ul ur) / q80 := by
      field_simp [q80_pos.ne']
      <;> ring
    _ < ((Nat.floor (q80 * ordinaryCornerMass tl tr ul ur) : ℝ) + 1) / q80 :=
      (div_lt_div_iff_of_pos_right q80_pos).mpr hf
    _ = savedQ80Value (directedCornerQ80 tl tr ul ur) + 1 / q80 := by
      rw [add_div]
      rfl

/-- Total flooring loss is nonnegative and at most M*N Q80 units.
Both sums include every child of the actual rectangular subdivision. -/
theorem totalQ80_rounding_loss {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    0 ≤ totalMass tl tr ul ur M N - savedQ80Value (totalQ80 tl tr ul ur M N) ∧
      totalMass tl tr ul ur M N - savedQ80Value (totalQ80 tl tr ul ur M N) ≤
        (M : ℝ) * (N : ℝ) / q80 := by
  have hlo : savedQ80Value (totalQ80 tl tr ul ur M N) ≤ totalMass tl tr ul ur M N := by
    rw [decode_totalQ80]
    exact Finset.sum_le_sum (fun i _hi => Finset.sum_le_sum (fun j _hj =>
      directedCornerQ80_le_mass (meshPoint_pos htl ht hM i)
        (meshPoint_pos hul hu hN j) (meshPoint_mono ht hM (Nat.le_succ i))
        (meshPoint_mono hu hN (Nat.le_succ j))))
  have hhi : totalMass tl tr ul ur M N ≤
      savedQ80Value (totalQ80 tl tr ul ur M N) + (M : ℝ) * (N : ℝ) / q80 := by
    have hsum := Finset.sum_le_sum (s := Finset.range M) (fun i _hi =>
      Finset.sum_le_sum (s := Finset.range N) (fun j _hj =>
        (cornerMass_lt_floor_add_unit (meshPoint tl tr M i)
          (meshPoint tl tr M (i + 1)) (meshPoint ul ur N j)
          (meshPoint ul ur N (j + 1))).le))
    rw [decode_totalQ80]
    simpa only [totalMass, childMass, childQ80, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_eq_mul_inv,
      one_mul, mul_assoc]
      using hsum
  exact ⟨sub_nonneg.mpr hlo, by linarith only [hhi]⟩

/-- Chen-unit lower semantics and its exact rounding budget. Division by
four is applied once, after summing the actual parent subdivision. -/
theorem totalQ80_chen_semantics {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    savedQ80Value (totalQ80 tl tr ul ur M N) / 4 ≤
        ordinaryCellIntegral tl tr ul ur / 4 ∧
      0 ≤ (totalMass tl tr ul ur M N - savedQ80Value (totalQ80 tl tr ul ur M N)) / 4 ∧
      (totalMass tl tr ul ur M N - savedQ80Value (totalQ80 tl tr ul ur M N)) / 4 ≤
        ((M : ℝ) * (N : ℝ)) / (4 * q80) := by
  have hround := totalQ80_rounding_loss htl hul ht hu hM hN
  refine ⟨div_le_div_of_nonneg_right
    (totalQ80_lower_parent_integral htl hul ht hu hM hN) (by norm_num),
    div_nonneg hround.1 (by norm_num), ?_⟩
  calc
    _ ≤ ((M : ℝ) * (N : ℝ) / q80) / 4 :=
      div_le_div_of_nonneg_right hround.2 (by norm_num)
    _ = ((M : ℝ) * (N : ℝ)) / (4 * q80) := by
      field_simp [q80_pos.ne']
      <;> ring

/-! The next definitions bind the parent rectangle to the actual imported
pair512 grid, not to fresh arbitrary coordinates or a replacement mesh. -/

open Certificates.PairedV2

def parentTL (i : Fin 512) : ℝ := (tLower i.val : ℝ)
def parentTR (i : Fin 512) : ℝ := (tUpper i.val : ℝ)
def parentUL (j : Fin 512) : ℝ := (uLower j.val : ℝ)
def parentUR (j : Fin 512) : ℝ := (uUpper j.val : ℝ)

theorem parent_coordinates (i j : Fin 512) :
    parentTL i = 25 / 128 + (651 / 8192000 : ℝ) * (i.val : ℝ) ∧
    parentTR i = 25 / 128 + (651 / 8192000 : ℝ) * ((i.val : ℝ) + 1) ∧
    parentUL j = 417 / 5000 + (343 / 2560000 : ℝ) * (j.val : ℝ) ∧
    parentUR j = 417 / 5000 + (343 / 2560000 : ℝ) * ((j.val : ℝ) + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  <;> norm_num [parentTL, parentTR, parentUL, parentUR, tLower, tUpper, uLower,
    uUpper, a, h, mu, d]
  <;> push_cast
  <;> ring

theorem parent_geometry (i j : Fin 512) :
    0 < parentTL i ∧ 0 < parentUL j ∧ parentTL i ≤ parentTR i ∧
      parentUL j ≤ parentUR j ∧ (25 / 128 : ℝ) ≤ parentTL i := by
  rcases parent_coordinates i j with ⟨htl, htr, hul, hur⟩
  simp only [htl, htr, hul, hur]
  have hi : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

/-- The parent coordinates lie on the actual high-t branch throughout,
so the real residual in every child has the literal ordinary-cap meaning. -/
theorem parent_original_cap_residual (i j : Fin 512) {t u : ℝ}
    (ht : t ∈ Icc (parentTL i) (parentTR i)) :
    ordinaryResidual t u = ordinaryPairCap t - t - u := by
  rcases parent_geometry i j with ⟨_htl, _hul, _hordt, _hordu, hmu⟩
  exact ordinaryResidual_eq_cap_residual (hmu.trans ht.1)

def savedParentSubdivisionQ80 (i j : Fin 512) (M N : ℕ) : ℕ :=
  totalQ80 (parentTL i) (parentTR i) (parentUL j) (parentUR j) M N

/-- Concrete actual-parent theorem: full integral identity, finite integer
lower estimator, and rounding loss in Chen units. The only inputs are
actual pair512 indices and positive subdivision sizes. -/
theorem savedParentSubdivision_semantics (i j : Fin 512)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    ordinaryCellIntegral (parentTL i) (parentTR i) (parentUL j) (parentUR j) =
        ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range N,
          childIntegral (parentTL i) (parentTR i) (parentUL j) (parentUR j) M N k l ∧
      savedQ80Value (savedParentSubdivisionQ80 i j M N) / 4 ≤
        ordinaryCellIntegral (parentTL i) (parentTR i) (parentUL j) (parentUR j) / 4 ∧
      (totalMass (parentTL i) (parentTR i) (parentUL j) (parentUR j) M N -
        savedQ80Value (savedParentSubdivisionQ80 i j M N)) / 4 ≤
          ((M : ℝ) * (N : ℝ)) / (4 * q80) := by
  rcases parent_geometry i j with ⟨htl, hul, ht, hu, _hmu⟩
  have hc := totalQ80_chen_semantics htl hul ht hu hM hN
  exact ⟨parent_integral_eq_sum_children htl hul ht hu hM hN, hc.1, hc.2.2⟩

end

end ImbalancedChen.P2SavedFloorSubdivisionEstimator
