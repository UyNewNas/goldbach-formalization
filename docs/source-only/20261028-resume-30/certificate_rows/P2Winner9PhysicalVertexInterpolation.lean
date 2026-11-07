import ImbalancedChen.P2Winner9PhysicalAffineTransfer
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The PhaseB4 transport left the original physical polynomial unrelated to
its vertex interpolation. This file proves that relation directly for an
arbitrary ordered list of nine actual physical vertices. All ten physical
factors, the physical gap, Y and signed deviations commute with the same
barycentric map. In particular the actual physical mixed integrand pulls
back to the product of its true vertex interpolants. No mixed-moment law,
vertex-value equality, positive row floor or final certificate is assumed.
-/

namespace ImbalancedChen.P2Winner9PhysicalVertexInterpolation

noncomputable section

open scoped BigOperators
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne

/-- The actual ordered-edge affine map of the nine physical vertices. -/
def vertexMap (v : Fin 9 → Ambient) (x : Ambient) : Ambient :=
  fun i => v 0 i + ∑ j : Fin 8, (v j.succ i - v 0 i) * x j

/-- Ordered-edge coordinates and barycentric interpolation are equal. -/
theorem vertexMap_coordinate (v : Fin 9 → Ambient)
    (x : Ambient) (i : Fin 8) :
    vertexMap v x i = affine (fun k => v k i) x := by
  simp only [vertexMap, affine, Fin.sum_univ_succ, barycentric,
    Fin.cases_zero, Fin.cases_succ]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem affine_constant (a : ℝ) (x : Ambient) :
    affine (fun _ : Fin 9 => a) x = a := by
  simp only [affine, Fin.sum_univ_succ, barycentric,
    Fin.cases_zero, Fin.cases_succ]
  rw [← Finset.mul_sum]
  ring

theorem affine_add (a b : Fin 9 → ℝ) (x : Ambient) :
    affine (fun k => a k + b k) x = affine a x + affine b x := by
  simp [affine, add_mul, Finset.sum_add_distrib]

theorem affine_sub (a b : Fin 9 → ℝ) (x : Ambient) :
    affine (fun k => a k - b k) x = affine a x - affine b x := by
  simp [affine, sub_mul, Finset.sum_sub_distrib]

theorem affine_div (a : Fin 9 → ℝ) (c : ℝ) (x : Ambient) :
    affine (fun k => a k / c) x = affine a x / c := by
  unfold affine
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem affine_sum {ι : Type*} [Fintype ι] (a : ι → Fin 9 → ℝ)
    (x : Ambient) :
    affine (fun k => ∑ i, a i k) x = ∑ i, affine (a i) x := by
  classical
  simp only [affine, Finset.sum_mul]
  exact Finset.sum_comm

theorem vertexMap_zero (v : Fin 9 → Ambient) : vertexMap v 0 = v 0 := by
  ext i
  simp [vertexMap]

theorem vertexMap_single (v : Fin 9 → Ambient) (j : Fin 8) :
    vertexMap v (Pi.single j (1 : ℝ)) = v j.succ := by
  ext i
  simp [vertexMap]

/-- The true physical R retains its constant term under the affine map. -/
theorem physicalR_vertexMap (v : Fin 9 → Ambient) (x : Ambient) :
    physicalR (vertexMap v x) = affine (fun k => physicalR (v k)) x := by
  change (1 + vertexMap v x 0 + vertexMap v x 3) / 2 =
    affine (fun k => (1 + v k 0 + v k 3) / 2) x
  simp only [vertexMap_coordinate, affine_div, affine_add, affine_constant]

/-- The exact -10^-6 shift in M is interpolated as a constant; it is
neither dropped nor merged into R. -/
theorem physicalM_vertexMap (v : Fin 9 → Ambient) (x : Ambient) :
    physicalM (vertexMap v x) = affine (fun k => physicalM (v k)) x := by
  change (1 + vertexMap v x 1 + vertexMap v x 3 + vertexMap v x 7) / 2 -
    1 / 1000000 =
      affine (fun k => (1 + v k 1 + v k 3 + v k 7) / 2 -
        1 / 1000000) x
  simp only [vertexMap_coordinate, affine_sub, affine_div,
    affine_add, affine_constant]

theorem physicalGap_vertexMap (v : Fin 9 → Ambient) (x : Ambient) :
    physicalGap (vertexMap v x) = affine (fun k => physicalGap (v k)) x := by
  rw [physicalGap, physicalM_vertexMap, physicalR_vertexMap, ← affine_sub]
  rfl

theorem coordinateSum_vertexMap (v : Fin 9 → Ambient) (x : Ambient) :
    coordinateSum (vertexMap v x) =
      affine (fun k => coordinateSum (v k)) x := by
  simp only [coordinateSum, vertexMap_coordinate]
  exact (affine_sum (fun i k => v k i) x).symm

/-- All ten original factors, including R-s and M-s, share this map. -/
theorem physicalFactor_vertexMap (v : Fin 9 → Ambient) (x : Ambient)
    (j : Fin 10) :
    physicalFactor j (vertexMap v x) =
      affine (fun k => physicalFactor j (v k)) x := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [physicalFactor_zero]
    rw [physicalR_vertexMap, coordinateSum_vertexMap, ← affine_sub]
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [physicalFactor_one]
      rw [physicalM_vertexMap, coordinateSum_vertexMap, ← affine_sub]
    · simpa only [physicalFactor_succ_succ] using vertexMap_coordinate v x i

theorem normalizedFactor_vertexMap (v : Fin 9 → Ambient)
    (means : Fin 10 → ℝ) (x : Ambient) (j : Fin 10) :
    normalizedFactor means j (vertexMap v x) =
      affine (fun k => normalizedFactor means j (v k)) x := by
  rw [normalizedFactor, physicalFactor_vertexMap, ← affine_div]
  rfl

theorem physicalP_vertexMap (v : Fin 9 → Ambient)
    (means : Fin 10 → ℝ) (x : Ambient) :
    physicalP means (vertexMap v x) =
      affine (fun k => physicalP means (v k)) x := by
  simp only [physicalP, normalizedFactor_vertexMap, affine_div, affine_sum]

theorem physicalY_vertexMap (v : Fin 9 → Ambient)
    (means : Fin 10 → ℝ) (U : ℝ) (x : Ambient) :
    physicalY means U (vertexMap v x) =
      affine (fun k => physicalY means U (v k)) x := by
  simp only [physicalY, physicalP_vertexMap, affine_sub, affine_div,
    affine_constant]

/-- The transverse deviation remains signed throughout interpolation. -/
theorem physicalDeviation_vertexMap (v : Fin 9 → Ambient)
    (means : Fin 10 → ℝ) (x : Ambient) (j : Fin 10) :
    physicalDeviation means j (vertexMap v x) =
      affine (fun k => physicalDeviation means j (v k)) x := by
  rw [physicalDeviation, normalizedFactor_vertexMap, physicalP_vertexMap,
    ← affine_sub]
  rfl

/-- The original mixed polynomial is exactly its three vertex
interpolants on the same physical map. This equality requires no
positivity, nondegeneracy or asserted moment law. -/
theorem physicalMixedIntegrand_vertexMap (v : Fin 9 → Ambient)
    (means : Fin 10 → ℝ) (U : ℝ) (j : Fin 10) (x : Ambient) :
    physicalMixedIntegrand means U j (vertexMap v x) =
      affine (fun k => physicalGap (v k)) x *
      affine (fun k => physicalY means U (v k)) x *
      (affine (fun k => physicalDeviation means j (v k)) x)^2 := by
  rw [physicalMixedIntegrand, physicalGap_vertexMap, physicalY_vertexMap,
    physicalDeviation_vertexMap]

/-- The full physical upper integrand also keeps factor four and all ten
factors after the same vertex interpolation. -/
theorem physicalUpperIntegrand_vertexMap (v : Fin 9 → Ambient)
    (x : Ambient) :
    physicalUpperIntegrand (vertexMap v x) =
      4 * affine (fun k => physicalGap (v k)) x /
        ∏ j : Fin 10, affine (fun k => physicalFactor j (v k)) x := by
  simp only [physicalUpperIntegrand, physicalGap_vertexMap,
    physicalFactor_vertexMap]

end

end ImbalancedChen.P2Winner9PhysicalVertexInterpolation
