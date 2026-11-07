import ImbalancedChen.P2OriginalSaving19SourceMeasure
import ImbalancedChen.P2Winner9ActualEightSimplexMoment
import ImbalancedChen.P2AffineSimplexMomentLaw
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Saving19 uses the original thirteen A23/s23_low cells and 28,918
eight-dimensional simplices. The two older simplex imports supply ONLY
the dimension-independent affine Jacobian and the actual canonical Δ8
monomial integral. No unequal-seed row, 11,026 index or floor is imported.

Here the actual R=A(t1+t4), M=A(t2+t4+t8)-10^-6, g=M-R and all ten
factors are interpolated from the SAME nine physical vertices. Their
physical mass and gap-weighted means are proved, not assumed. In
particular the original denominators 9 and 10 and the absolute Jacobian
are retained. This removes the mass/mean semantic ports in a future
original row checker. It does not assert a typed original row archive,
degree2..6 duplicated-node evaluator, source ownership or any endpoint.
-/

namespace ImbalancedChen.P2OriginalSaving19SimplexMoments

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SourceMeasure
open P2Winner9SimplexCoordinateSlice
open P2Winner9ActualEightSimplexMoment
open P2Winner9NestedEightSimplexMoment (factorialProduct actualMoment)
open Certificates.P2AffineSimplexMomentLaw (integral_affine_image)

def canonical : Set Point := P2Winner9SimplexCoordinateSlice.standardSimplex 8 1

theorem canonical_measurable : MeasurableSet canonical :=
  (isClosed_standardSimplex (1 : ℝ)).measurableSet

theorem canonical_compact : IsCompact canonical :=
  isCompact_standardSimplex (by norm_num)

def bary (i : Fin 9) (x : Point) : ℝ :=
  Fin.cases (1 - ∑ j : Fin 8, x j) (fun j => x j) i

def interpolate (v : Fin 9 → ℝ) (x : Point) : ℝ :=
  ∑ i : Fin 9, bary i x * v i

def pointInterpolate (v : Fin 9 → Point) (x : Point) : Point :=
  ∑ i : Fin 9, bary i x • v i

theorem bary_continuous (i : Fin 9) : Continuous (bary i) := by
  refine Fin.cases ?_ ?_ i
  · dsimp [bary]
    fun_prop
  · intro j
    simpa only [bary, Fin.cases_succ] using (continuous_apply j : Continuous (fun x : Point => x j))

theorem interpolate_continuous (v : Fin 9 → ℝ) : Continuous (interpolate v) := by
  apply continuous_finsetSum
  intro i _
  exact (bary_continuous i).mul continuous_const

theorem bary_sum (x : Point) : (∑ i : Fin 9, bary i x) = 1 := by
  simp [bary, Fin.sum_univ_succ]

theorem bary_nonneg {x : Point} (hx : x ∈ canonical) (i : Fin 9) : 0 ≤ bary i x := by
  refine Fin.cases ?_ ?_ i
  · exact sub_nonneg.mpr hx.2
  · intro j
    exact hx.1 j

theorem interpolate_const (c : ℝ) (x : Point) : interpolate (fun _ => c) x = c := by
  rw [interpolate, ← Finset.sum_mul, bary_sum, one_mul]

theorem interpolate_add (a b : Fin 9 → ℝ) (x : Point) :
    interpolate (fun i => a i + b i) x = interpolate a x + interpolate b x := by
  simp [interpolate, mul_add, Finset.sum_add_distrib]

theorem interpolate_sub (a b : Fin 9 → ℝ) (x : Point) :
    interpolate (fun i => a i - b i) x = interpolate a x - interpolate b x := by
  simp [interpolate, mul_sub, Finset.sum_sub_distrib]

theorem interpolate_div (a : Fin 9 → ℝ) (c : ℝ) (x : Point) :
    interpolate (fun i => a i / c) x = interpolate a x / c := by
  simp [interpolate, mul_div_assoc, Finset.sum_div]

theorem interpolate_sum (a : Fin 9 → Fin 8 → ℝ) (x : Point) :
    interpolate (fun i => ∑ j : Fin 8, a i j) x =
      ∑ j : Fin 8, interpolate (fun i => a i j) x := by
  simp only [interpolate, Finset.mul_sum]
  exact Finset.sum_comm

theorem pointInterpolate_apply (v : Fin 9 → Point) (x : Point) (j : Fin 8) :
    pointInterpolate v x j = interpolate (fun i => v i j) x := by
  simp [pointInterpolate, interpolate, Finset.sum_apply, smul_eq_mul]

theorem interpolate_bounds (v : Fin 9 → ℝ) {lo hi : ℝ}
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

def baryMoment (e : Fin 9 → ℕ) : ℝ :=
  ∫ x in canonical, ∏ i : Fin 9, bary i x ^ e i

/-- Actual unnormalized Lebesgue moments, inherited from Fubini plus
the elementary beta integral, with no Dirichlet-law premise. -/
theorem baryMoment_eq (e : Fin 9 → ℕ) :
    baryMoment e =
      (((e 0).factorial * factorialProduct (List.ofFn (fun i : Fin 8 => e i.succ)) : ℕ) : ℝ) /
        (((e 0) + (List.ofFn (fun i : Fin 8 => e i.succ)).sum + 8).factorial : ℝ) := by
  have he : baryMoment e = actualMoment (e 0) (fun i : Fin 8 => e i.succ) 1 := by
    unfold baryMoment actualMoment
    apply setIntegral_congr_fun canonical_measurable
    intro x _
    simp [bary, Fin.prod_univ_succ]
  rw [he, actual_eight_factorial (e 0) (fun i : Fin 8 => e i.succ) (by norm_num)]
  simp

def unitExponent (i r : Fin 9) : ℕ := if r = i then 1 else 0

theorem prod_unitExponent (i : Fin 9) (x : Point) :
    (∏ r : Fin 9, bary r x ^ unitExponent i r) = bary i x := by
  classical
  calc
    _ = ∏ r : Fin 9, if r = i then bary r x else 1 := by
      apply Finset.prod_congr rfl
      intro r _
      by_cases h : r = i <;> simp [unitExponent, h]
    _ = _ := by simp

theorem bary_first (i : Fin 9) :
    (∫ x in canonical, bary i x) = 1 / (9.factorial : ℝ) := by
  have he : (∫ x in canonical, bary i x) = baryMoment (unitExponent i) := by
    unfold baryMoment
    simp_rw [prod_unitExponent]
  rw [he, baryMoment_eq]
  fin_cases i <;> norm_num [unitExponent, factorialProduct, List.ofFn]

theorem bary_second (i j : Fin 9) :
    (∫ x in canonical, bary i x * bary j x) =
      (1 + if i = j then 1 else 0) / (10.factorial : ℝ) := by
  classical
  have he : (∫ x in canonical, bary i x * bary j x) =
      baryMoment (fun r => unitExponent i r + unitExponent j r) := by
    unfold baryMoment
    simp_rw [pow_add, Finset.prod_mul_distrib, prod_unitExponent]
  rw [he, baryMoment_eq]
  fin_cases i <;> fin_cases j <;>
    norm_num [unitExponent, factorialProduct, List.ofFn]

theorem canonical_volume : (∫ _x in canonical, (1 : ℝ)) = 1 / (8.factorial : ℝ) := by
  have h := actual_eight_factorial 0 (fun _ : Fin 8 => 0) (s := 1) (by norm_num)
  simpa [actualMoment, canonical, P2Winner9NestedEightSimplexMoment.standardSimplex,
    P2Winner9SimplexCoordinateSlice.standardSimplex, factorialProduct, List.ofFn] using h

theorem integral_interpolate (v : Fin 9 → ℝ) :
    (∫ x in canonical, interpolate v x) = (∑ i : Fin 9, v i) / (9.factorial : ℝ) := by
  unfold interpolate
  rw [integral_finsetSum]
  · simp only [integral_mul_const, bary_first]
    simp [div_eq_mul_inv, Finset.sum_mul, mul_comm]
  · intro i _
    exact ((bary_continuous i).mul continuous_const).continuousOn.integrableOn_compact
      canonical_compact

/-- The second barycentric moment is where the extra parameter 10
enters. Diagonal terms have multiplicity two, not one. -/
theorem integral_interpolate_mul (g l : Fin 9 → ℝ) :
    (∫ x in canonical, interpolate g x * interpolate l x) =
      ((∑ i : Fin 9, g i) * (∑ i : Fin 9, l i) + ∑ i : Fin 9, g i * l i) /
        (10.factorial : ℝ) := by
  classical
  let term (i j : Fin 9) (x : Point) := (g i * l j) * (bary i x * bary j x)
  have hi (i j : Fin 9) : IntegrableOn (term i j) canonical := by
    exact (continuous_const.mul ((bary_continuous i).mul
      (bary_continuous j))).continuousOn.integrableOn_compact canonical_compact
  have he : (fun x => interpolate g x * interpolate l x) =
      fun x => ∑ i : Fin 9, ∑ j : Fin 9, term i j x := by
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

/-- Original physical formulas commute with barycentric interpolation.
The constant -10^-6 is preserved because the weights sum to one. -/
theorem comparisonCap_interpolate (v : Fin 9 → Point) (x : Point) :
    comparisonCap (pointInterpolate v x) = interpolate (fun i => comparisonCap (v i)) x := by
  simp only [comparisonCap, VariableEnvelope.A, interpolate_div,
    interpolate_add, interpolate_const, pointInterpolate_apply]

theorem newCap_interpolate (v : Fin 9 → Point) (x : Point) :
    newCap (pointInterpolate v x) = interpolate (fun i => newCap (v i)) x := by
  simp only [newCap, selectedSum, VariableEnvelope.A, interpolate_sub, interpolate_div,
    interpolate_add, interpolate_const, pointInterpolate_apply]

theorem total_interpolate (v : Fin 9 → Point) (x : Point) :
    total (pointInterpolate v x) = interpolate (fun i => total (v i)) x := by
  simp only [total, pointInterpolate_apply, interpolate_sum]

theorem gap_interpolate (v : Fin 9 → Point) (x : Point) :
    gap (pointInterpolate v x) = interpolate (fun i => gap (v i)) x := by
  simp only [gap, newCap_interpolate, comparisonCap_interpolate, interpolate_sub]

theorem factors_interpolate (v : Fin 9 → Point) (x : Point) (j : Fin 10) :
    factors (pointInterpolate v x) j = interpolate (fun i => factors (v i) j) x := by
  fin_cases j <;>
    simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · rw [comparisonCap_interpolate, total_interpolate, interpolate_sub]
  · rw [newCap_interpolate, total_interpolate, interpolate_sub]
  all_goals exact pointInterpolate_apply v x _

def vertices (L : Point ≃L[ℝ] Point) (b : Point) : Fin 9 → Point :=
  Fin.cons b (fun i : Fin 8 => b + L (Pi.single i (1 : ℝ)))

def support (L : Point ≃L[ℝ] Point) (b : Point) : Set Point :=
  (fun x => b + L x) '' canonical

def jacobian (L : Point ≃L[ℝ] Point) : ℝ := |L.toContinuousLinearMap.det|

def physicalVolume (L : Point ≃L[ℝ] Point) : ℝ := jacobian L / (8.factorial : ℝ)

def gapTotal (v : Fin 9 → Point) : ℝ := ∑ i : Fin 9, gap (v i)

def factorMean (v : Fin 9 → Point) (j : Fin 10) : ℝ :=
  ((∑ i : Fin 9, factors (v i) j) +
    (∑ i : Fin 9, gap (v i) * factors (v i) j) / gapTotal v) / 10

theorem jacobian_pos (L : Point ≃L[ℝ] Point) : 0 < jacobian L := by
  exact abs_pos.mpr L.toLinearEquiv.isUnit_det'.ne_zero

theorem physicalVolume_pos (L : Point ≃L[ℝ] Point) : 0 < physicalVolume L := by
  exact div_pos (jacobian_pos L) (by norm_num)

theorem vertices_interpolate (L : Point ≃L[ℝ] Point) (b x : Point) :
    pointInterpolate (vertices L b) x = b + L x := by
  classical
  have hx : (∑ i : Fin 8, x i • Pi.single i (1 : ℝ)) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  have hL : (∑ i : Fin 8, x i • L (Pi.single i (1 : ℝ))) = L x := by
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

/-- Genuine physical mass of the original saving19 affine gap. -/
theorem integral_gap (L : Point ≃L[ℝ] Point) (b : Point) :
    (∫ t in support L b, gap t) = physicalVolume L * gapTotal (vertices L b) / 9 := by
  rw [integral_support]
  simp_rw [← vertices_interpolate L b, gap_interpolate]
  rw [integral_interpolate]
  norm_num [physicalVolume, gapTotal]
  ring

theorem integral_gap_factor (L : Point ≃L[ℝ] Point) (b : Point) (j : Fin 10) :
    (∫ t in support L b, gap t * factors t j) =
      jacobian L *
        (gapTotal (vertices L b) * (∑ i : Fin 9, factors (vertices L b i) j) +
          ∑ i : Fin 9, gap (vertices L b i) * factors (vertices L b i) j) /
          (10.factorial : ℝ) := by
  rw [integral_support]
  simp_rw [← vertices_interpolate L b, gap_interpolate, factors_interpolate]
  rw [integral_interpolate_mul]
  dsimp [gapTotal]
  ring

/-- The exact mean used by both original producers. Neither mass nor
weighted mean is a hypothesis; both come from the two polynomial integrals. -/
theorem normalized_factor_mean (L : Point ≃L[ℝ] Point) (b : Point) (j : Fin 10)
    (hG : 0 < gapTotal (vertices L b)) :
    (∫ t in support L b, gap t * factors t j) / (∫ t in support L b, gap t) =
      factorMean (vertices L b) j := by
  rw [integral_gap_factor, integral_gap]
  have hJ := (jacobian_pos L).ne'
  norm_num [physicalVolume, factorMean]
  field_simp [hJ, hG.ne']
  ring

theorem gap_mass_pos (L : Point ≃L[ℝ] Point) (b : Point)
    (hG : 0 < gapTotal (vertices L b)) :
    0 < ∫ t in support L b, gap t := by
  rw [integral_gap]
  exact div_pos (mul_pos (physicalVolume_pos L) hG) (by norm_num)

theorem factorMean_pos (v : Fin 9 → Point)
    (hv : ∀ i, PhysicalRows (v i)) (hG : 0 < gapTotal v) (j : Fin 10) :
    0 < factorMean v j := by
  have hsum : 0 < ∑ i : Fin 9, factors (v i) j :=
    Finset.sum_pos (fun i _ => factors_pos (hv i) j) Finset.univ_nonempty
  have hdot : 0 ≤ ∑ i : Fin 9, gap (v i) * factors (v i) j :=
    Finset.sum_nonneg (fun i _ => mul_nonneg
      (physical_gap_bounds (hv i)).1 (factors_pos (hv i) j).le)
  exact div_pos (add_pos_of_pos_of_nonneg hsum (div_nonneg hdot hG.le)) (by norm_num)

/-- Directly eliminates the original old-Jensen numerator/mean
normalization ports. This is an identity, not a lower-bound assumption. -/
theorem original_jensen_normalization (L : Point ≃L[ℝ] Point) (b : Point)
    (hG : 0 < gapTotal (vertices L b)) :
    4 * (∫ t in support L b, gap t) /
      (∏ j : Fin 10, (∫ t in support L b, gap t * factors t j) /
        (∫ t in support L b, gap t)) =
      4 * physicalVolume L * gapTotal (vertices L b) /
        (9 * ∏ j : Fin 10, factorMean (vertices L b) j) := by
  simp_rw [normalized_factor_mean L b _ hG]
  rw [integral_gap]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def vertexTop (v : Fin 9 → Point) (j : Fin 10) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 9 => factors (v i) j)

theorem factor_le_vertexTop (v : Fin 9 → Point) (i : Fin 9) (j : Fin 10) :
    factors (v i) j ≤ vertexTop v j :=
  Finset.le_sup' (f := fun i : Fin 9 => factors (v i) j) (Finset.mem_univ i)

theorem vertexTop_pos (v : Fin 9 → Point) (hv : ∀ i, PhysicalRows (v i)) (j : Fin 10) :
    0 < vertexTop v j :=
  (factors_pos (hv 0) j).trans_le (factor_le_vertexTop v 0 j)

/-- The top is the original maximum of the NINE physical vertex
values. The global cutoff only supplies a valid strict range margin. -/
theorem support_factor_bounds (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) {t : Point} (ht : t ∈ support L b)
    (j : Fin 10) : cutoff ≤ factors t j ∧ factors t j ≤ vertexTop (vertices L b) j := by
  obtain ⟨x, hx, rfl⟩ := ht
  rw [← vertices_interpolate L b x, factors_interpolate]
  exact interpolate_bounds (fun i => factors (vertices L b i) j)
    (fun i => ⟨(physical_factor_bounds (hv i) j).1,
      factor_le_vertexTop (vertices L b) i j⟩) hx

theorem support_gap_bounds (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) {t : Point} (ht : t ∈ support L b) :
    0 ≤ gap t ∧ gap t ≤ 2 * VariableEnvelope.mu := by
  obtain ⟨x, hx, rfl⟩ := ht
  rw [← vertices_interpolate L b x, gap_interpolate]
  exact interpolate_bounds (fun i => gap (vertices L b i))
    (fun i => physical_gap_bounds (hv i)) hx

theorem support_factor_pos (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) {t : Point} (ht : t ∈ support L b)
    (j : Fin 10) : 0 < factors t j :=
  cutoff_pos.trans_le (support_factor_bounds L b hv ht j).1

end

end ImbalancedChen.P2OriginalSaving19SimplexMoments
