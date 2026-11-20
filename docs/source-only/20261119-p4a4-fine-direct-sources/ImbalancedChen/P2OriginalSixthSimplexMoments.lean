import ImbalancedChen.P2Winner9ActualEightSimplexMoment
import ImbalancedChen.P2AffineSimplexMomentLaw
import Mathlib.Tactic

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The ORIGINAL G7 simplex dimension is SIX, with SEVEN barycentric vertices.
The inherited files are used only for their arbitrary-dimension Fubini and
arbitrary-list beta proofs. No eight-dimensional volume is imported.
Adapted from the static saving19 interpolation proof; all normalizations
are actual6D: 6! volume, 7! first moment and 8! second moment.
-/
namespace ImbalancedChen.P2OriginalSixthSimplexMoments
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2Winner9SimplexCoordinateSlice
open P2Winner9ActualEightSimplexMoment
open P2Winner9NestedEightSimplexMoment (factorialProduct nestedMoment nestedMoment_eq coefficient totalDegree)
open Certificates.P2AffineSimplexMomentLaw (integral_affine_image)
abbrev Point := Fin 6 → ℝ

def canonical : Set Point := P2Winner9SimplexCoordinateSlice.standardSimplex 6 1

theorem canonical_measurable : MeasurableSet canonical :=
  (isClosed_standardSimplex (1 : ℝ)).measurableSet

theorem canonical_compact : IsCompact canonical :=
  isCompact_standardSimplex (by norm_num)

def bary (i : Fin 7) (x : Point) : ℝ :=
  Fin.cases (1 - ∑ j : Fin 6, x j) (fun j => x j) i

def interpolate (v : Fin 7 → ℝ) (x : Point) : ℝ :=
  ∑ i : Fin 7, bary i x * v i

def pointInterpolate (v : Fin 7 → Point) (x : Point) : Point :=
  ∑ i : Fin 7, bary i x • v i

theorem bary_continuous (i : Fin 7) : Continuous (bary i) := by
  refine Fin.cases ?_ ?_ i
  · dsimp [bary]
    fun_prop
  · intro j
    simpa only [bary, Fin.cases_succ] using (continuous_apply j : Continuous (fun x : Point => x j))

theorem interpolate_continuous (v : Fin 7 → ℝ) : Continuous (interpolate v) := by
  apply continuous_finsetSum
  intro i _
  exact (bary_continuous i).mul continuous_const

theorem bary_sum (x : Point) : (∑ i : Fin 7, bary i x) = 1 := by
  simp [bary, Fin.sum_univ_succ]

theorem bary_nonneg {x : Point} (hx : x ∈ canonical) (i : Fin 7) : 0 ≤ bary i x := by
  refine Fin.cases ?_ ?_ i
  · exact sub_nonneg.mpr hx.2
  · intro j
    exact hx.1 j

theorem interpolate_const (c : ℝ) (x : Point) : interpolate (fun _ => c) x = c := by
  rw [interpolate, ← Finset.sum_mul, bary_sum, one_mul]

theorem interpolate_add (a b : Fin 7 → ℝ) (x : Point) :
    interpolate (fun i => a i + b i) x = interpolate a x + interpolate b x := by
  simp [interpolate, mul_add, Finset.sum_add_distrib]

theorem interpolate_sub (a b : Fin 7 → ℝ) (x : Point) :
    interpolate (fun i => a i - b i) x = interpolate a x - interpolate b x := by
  simp [interpolate, mul_sub, Finset.sum_sub_distrib]

theorem interpolate_div (a : Fin 7 → ℝ) (c : ℝ) (x : Point) :
    interpolate (fun i => a i / c) x = interpolate a x / c := by
  simp [interpolate, mul_div_assoc, Finset.sum_div]

theorem interpolate_sum (a : Fin 7 → Fin 6 → ℝ) (x : Point) :
    interpolate (fun i => ∑ j : Fin 6, a i j) x =
      ∑ j : Fin 6, interpolate (fun i => a i j) x := by
  simp only [interpolate, Finset.mul_sum]
  exact Finset.sum_comm

theorem pointInterpolate_apply (v : Fin 7 → Point) (x : Point) (j : Fin 6) :
    pointInterpolate v x j = interpolate (fun i => v i j) x := by
  simp [pointInterpolate, interpolate, Finset.sum_apply, smul_eq_mul]

theorem interpolate_bounds (v : Fin 7 → ℝ) {lo hi : ℝ}
    (hv : ∀ i, lo ≤ v i ∧ v i ≤ hi) {x : Point} (hx : x ∈ canonical) :
    lo ≤ interpolate v x ∧ interpolate v x ≤ hi := by
  constructor
  · calc
      lo = interpolate (fun _ => lo) x := (interpolate_const lo x).symm
      _ ≤ interpolate v x := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hv i).1 (bary_nonneg hx i)
  · calc
      interpolate v x ≤ interpolate (fun _ => hi) x := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hv i).2 (bary_nonneg hx i)
      _ = hi := interpolate_const hi x

/-- The actual six-dimensional integral follows from the existing arbitrary-n
Fubini theorem and arbitrary-list beta theorem, without an assumed moment law. -/
theorem actual_six_factorial (m0 : Nat) (ms : Fin 6 → Nat)
    {s : ℝ} (hs : 0 ≤ s) :
    actualMomentN 6 m0 ms s =
      (((m0.factorial * factorialProduct (List.ofFn ms) : Nat) : ℝ) /
        ((m0 + (List.ofFn ms).sum + 6).factorial : ℝ)) *
          s ^ (m0 + (List.ofFn ms).sum + 6) := by
  rw [actualMomentN_eq_nested 6 m0 ms hs, nestedMoment_eq]
  simp [coefficient, totalDegree]

def baryMoment (e : Fin 7 → ℕ) : ℝ :=
  ∫ x in canonical, ∏ i : Fin 7, bary i x ^ e i

/-- Actual unnormalized Lebesgue moments, inherited from Fubini plus
the elementary beta integral, with no Dirichlet-law premise. -/
theorem baryMoment_eq (e : Fin 7 → ℕ) :
    baryMoment e =
      (((e 0).factorial * factorialProduct (List.ofFn (fun i : Fin 6 => e i.succ)) : ℕ) : ℝ) /
        (((e 0) + (List.ofFn (fun i : Fin 6 => e i.succ)).sum + 6).factorial : ℝ) := by
  have he : baryMoment e = actualMomentN 6 (e 0) (fun i : Fin 6 => e i.succ) 1 := by
    unfold baryMoment actualMomentN
    apply setIntegral_congr_fun canonical_measurable
    intro x _
    simp [bary, Fin.prod_univ_succ]
  rw [he, actual_six_factorial (e 0) (fun i : Fin 6 => e i.succ) (by norm_num)]
  simp

def unitExponent (i r : Fin 7) : ℕ := if r = i then 1 else 0

theorem prod_unitExponent (i : Fin 7) (x : Point) :
    (∏ r : Fin 7, bary r x ^ unitExponent i r) = bary i x := by
  classical
  calc
    _ = ∏ r : Fin 7, if r = i then bary r x else 1 := by
      apply Finset.prod_congr rfl
      intro r _
      by_cases h : r = i <;> simp [unitExponent, h]
    _ = _ := by simp

theorem bary_first (i : Fin 7) :
    (∫ x in canonical, bary i x) = 1 / (7.factorial : ℝ) := by
  have he : (∫ x in canonical, bary i x) = baryMoment (unitExponent i) := by
    unfold baryMoment
    simp_rw [prod_unitExponent]
  rw [he, baryMoment_eq]
  fin_cases i <;> norm_num [unitExponent, factorialProduct, List.ofFn]

theorem bary_second (i j : Fin 7) :
    (∫ x in canonical, bary i x * bary j x) =
      (1 + if i = j then 1 else 0) / (8.factorial : ℝ) := by
  classical
  have he : (∫ x in canonical, bary i x * bary j x) =
      baryMoment (fun r => unitExponent i r + unitExponent j r) := by
    unfold baryMoment
    simp_rw [pow_add, Finset.prod_mul_distrib, prod_unitExponent]
  rw [he, baryMoment_eq]
  fin_cases i <;> fin_cases j <;>
    norm_num [unitExponent, factorialProduct, List.ofFn]

theorem canonical_volume : (∫ _x in canonical, (1 : ℝ)) = 1 / (6.factorial : ℝ) := by
  have h := actual_six_factorial 0 (fun _ : Fin 6 => 0) (s := 1) (by norm_num)
  simpa [actualMomentN, canonical,
    P2Winner9SimplexCoordinateSlice.standardSimplex, factorialProduct, List.ofFn] using h

theorem integral_interpolate (v : Fin 7 → ℝ) :
    (∫ x in canonical, interpolate v x) = (∑ i : Fin 7, v i) / (7.factorial : ℝ) := by
  unfold interpolate
  rw [integral_finsetSum]
  · simp only [integral_mul_const, bary_first]
    simp [div_eq_mul_inv, Finset.sum_mul, mul_comm]
  · intro i _
    exact ((bary_continuous i).mul continuous_const).continuousOn.integrableOn_compact
      canonical_compact

/-- The second barycentric moment is where the extra parameter 8
enters. Diagonal terms have multiplicity two, not one. -/
theorem integral_interpolate_mul (g l : Fin 7 → ℝ) :
    (∫ x in canonical, interpolate g x * interpolate l x) =
      ((∑ i : Fin 7, g i) * (∑ i : Fin 7, l i) + ∑ i : Fin 7, g i * l i) /
        (8.factorial : ℝ) := by
  classical
  let term (i j : Fin 7) (x : Point) := (g i * l j) * (bary i x * bary j x)
  have hi (i j : Fin 7) : IntegrableOn (term i j) canonical := by
    exact (continuous_const.mul ((bary_continuous i).mul
      (bary_continuous j))).continuousOn.integrableOn_compact canonical_compact
  have he : (fun x => interpolate g x * interpolate l x) =
      fun x => ∑ i : Fin 7, ∑ j : Fin 7, term i j x := by
    funext x
    simp only [interpolate, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [term]
    ring
  rw [he, integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j)]
  simp only [term, integral_const_mul, bary_second]
  simp [mul_div_assoc, mul_add, mul_ite, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul] <;> ring

def vertices (L : Point ≃L[ℝ] Point) (b : Point) : Fin 7 → Point :=
  Fin.cons b (fun i : Fin 6 => b + L (Pi.single i (1 : ℝ)))

def support (L : Point ≃L[ℝ] Point) (b : Point) : Set Point :=
  (fun x => b + L x) '' canonical

def jacobian (L : Point ≃L[ℝ] Point) : ℝ := |L.toContinuousLinearMap.det|

def physicalVolume (L : Point ≃L[ℝ] Point) : ℝ := jacobian L / (6.factorial : ℝ)

theorem jacobian_pos (L : Point ≃L[ℝ] Point) : 0 < jacobian L := by
  exact abs_pos.mpr L.toLinearEquiv.isUnit_det'.ne_zero

theorem physicalVolume_pos (L : Point ≃L[ℝ] Point) : 0 < physicalVolume L := by
  exact div_pos (jacobian_pos L) (by norm_num)

theorem vertices_interpolate (L : Point ≃L[ℝ] Point) (b x : Point) :
    pointInterpolate (vertices L b) x = b + L x := by
  classical
  have hx : (∑ i : Fin 6, x i • Pi.single i (1 : ℝ)) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  have hL : (∑ i : Fin 6, x i • L (Pi.single i (1 : ℝ))) = L x := by
    simp_rw [← map_smul]
    rw [← map_sum, hx]
  unfold pointInterpolate
  rw [Fin.sum_univ_succ]
  simp only [vertices, Fin.cons_zero,
    Fin.cons_succ, bary, Fin.cases_zero, Fin.cases_succ, smul_add, Finset.sum_add_distrib]
  rw [hL, ← Finset.sum_smul, ← add_assoc, ← add_smul]
  simp

theorem support_compact (L : Point ≃L[ℝ] Point) (b : Point) : IsCompact (support L b) :=
  canonical_compact.image (continuous_const.add L.continuous)

theorem support_measurable (L : Point ≃L[ℝ] Point) (b : Point) : MeasurableSet (support L b) :=
  (support_compact L b).isClosed.measurableSet

theorem integral_support (L : Point ≃L[ℝ] Point) (b : Point) (f : Point → ℝ) :
    (∫ t in support L b, f t) = jacobian L * ∫ x in canonical, f (b + L x) := by
  exact integral_affine_image volume L b canonical canonical_measurable f

theorem integral_volume (L : Point ≃L[ℝ] Point) (b : Point) :
    (∫ _t in support L b, (1 : ℝ)) = physicalVolume L := by
  rw [integral_support, canonical_volume]
  dsimp [physicalVolume]
  ring

end
end ImbalancedChen.P2OriginalSixthSimplexMoments
