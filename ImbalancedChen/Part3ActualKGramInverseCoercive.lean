import ImbalancedChen.Part3ActualKStrictGram
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
The actual finite K0(q_i+q_j) matrix is positive definite and invertible.
Compactness of the coefficient unit sphere supplies a strictly positive
uniform lower bound for its complex Hermitian form. This is a finite
sampling statement, not an automorphic spectral decomposition.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualKGramInverseCoerciveSourceOnly

open Matrix
open scoped BigOperators ComplexInnerProductSpace ComplexConjugate
open ImaginaryOrderKBesselSourceOnly EvenFourierHilbertSourceOnly
open ActualKStrictGramSourceOnly

section CompactSphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The compact unit sphere supplies the lower constant; the empty sphere
case is included by the extreme-value theorem used here. -/
theorem exists_pos_norm_sq_lower_bound (T : E →ₗ[ℝ] F)
    (hcont : Continuous T) (hinj : Function.Injective T) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
  have hpos : ∀ x ∈ Metric.sphere (0 : E) 1, 0 < ‖T x‖ ^ 2 := by
    intro x hx
    have hnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
    have hx0 : x ≠ 0 := by intro hz; simpa [hz] using hnorm
    have hTx : T x ≠ 0 := by
      intro hz
      exact hx0 (hinj (hz.trans T.map_zero.symm))
    exact sq_pos_of_pos (norm_pos_iff.mpr hTx)
  obtain ⟨a, ha, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    (hcont.norm.pow 2).continuousOn hpos
  refine ⟨a, ha, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let z : E := ‖x‖⁻¹ • x
  have hz : z ∈ Metric.sphere (0 : E) 1 := by
    simp [Metric.mem_sphere, dist_zero_right, z, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), hn]
  have hxz : x = ‖x‖ • z := by simp [z, smul_smul, hn]
  have hscale : ‖T x‖ ^ 2 = ‖x‖ ^ 2 * ‖T z‖ ^ 2 := by
    calc
      ‖T x‖ ^ 2 = ‖T (‖x‖ • z)‖ ^ 2 := congrArg (fun y => ‖T y‖ ^ 2) hxz
      _ = _ := by
        rw [T.map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg x), mul_pow]
  rw [hscale]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hmin z hz) (sq_nonneg ‖x‖)

end CompactSphere

section ActualMatrix

variable {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i)

/-- The actual unnormalized K0 sum-kernel matrix. -/
def kGramMatrix : Matrix ι ι ℝ := fun i j => imaginaryOrderK 0 (q i + q j)

theorem kGramMatrix_isHermitian : (kGramMatrix q).IsHermitian := by
  change (kGramMatrix q)ᴴ = kGramMatrix q
  ext i j
  simp [kGramMatrix, Matrix.conjTranspose_apply, add_comm]

theorem kGramMatrix_posDef (hinj : Function.Injective q) :
    (kGramMatrix q).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (kGramMatrix_isHermitian q)
  intro c hc
  simpa [dotProduct, mulVec, kGramMatrix, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm] using kZeroGram_real_pos q hq hinj c hc

variable [DecidableEq ι]

theorem kGramMatrix_det_pos (hinj : Function.Injective q) :
    0 < (kGramMatrix q).det := by
  exact (kGramMatrix_posDef q hq hinj).det_pos

theorem kGramMatrix_det_ne_zero (hinj : Function.Injective q) :
    (kGramMatrix q).det ≠ 0 := by
  exact ne_of_gt (kGramMatrix_det_pos q hq hinj)

theorem kGramMatrix_isUnit (hinj : Function.Injective q) : IsUnit (kGramMatrix q) := by
  exact (kGramMatrix_posDef q hq hinj).isUnit

theorem kGramMatrix_inv_posDef (hinj : Function.Injective q) :
    ((kGramMatrix q)⁻¹).PosDef := by
  exact (kGramMatrix_posDef q hq hinj).inv

theorem kGramMatrix_mul_inv (hinj : Function.Injective q) :
    kGramMatrix q * (kGramMatrix q)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    (kGramMatrix_det_ne_zero q hq hinj))

theorem kGramMatrix_inv_mul (hinj : Function.Injective q) :
    (kGramMatrix q)⁻¹ * kGramMatrix q = 1 := by
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
    (kGramMatrix_det_ne_zero q hq hinj))

/-- The inverse supplies an actual solution for every finite sample vector. -/
theorem kGramMatrix_solve (hinj : Function.Injective q) (b : ι → ℝ) :
    kGramMatrix q *ᵥ ((kGramMatrix q)⁻¹ *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, kGramMatrix_mul_inv q hq hinj, Matrix.one_mulVec]

theorem kGramMatrix_solution_unique (hinj : Function.Injective q)
    (b c : ι → ℝ) (hc : kGramMatrix q *ᵥ c = b) :
    c = (kGramMatrix q)⁻¹ *ᵥ b := by
  rw [← hc, Matrix.mulVec_mulVec, kGramMatrix_inv_mul q hq hinj, Matrix.one_mulVec]

end ActualMatrix

section Coercivity

variable {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i)

/-- Synthesis of the actual spatial profiles with Euclidean coefficients. -/
def profileSynthesis : EuclideanSpace ℂ ι →ₗ[ℂ] ComplexL2 where
  toFun x := ∑ i, x i • (evenKProfile (q i) (hq i) : ComplexL2)
  map_add' x y := by
    change (∑ i, (x i + y i) • (evenKProfile (q i) (hq i) : ComplexL2)) = _
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, (a * x i) • (evenKProfile (q i) (hq i) : ComplexL2)) = _
    simp only [mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem profileSynthesis_injective (hinj : Function.Injective q) :
    Function.Injective (profileSynthesis q hq) := by
  intro x y hxy
  have hz : profileSynthesis q hq (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hc : ∀ i, (x - y) i = 0 :=
    (Fintype.linearIndependent_iff.1 (evenKProfile_L2_linearIndependent q hq hinj))
      (fun i => (x - y) i) hz
  ext i
  exact sub_eq_zero.mp (hc i)

/-- Uniform strict lower bound for every complex coefficient vector.
The constant depends on the finite distinct positive parameter family. -/
theorem kZeroGramForm_uniform_lower_bound (hinj : Function.Injective q) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ι → ℂ,
      a * (∑ i, ‖c i‖ ^ 2) ≤ (kZeroGramForm q c).re := by
  let T := (profileSynthesis q hq).restrictScalars ℝ
  have hcont : Continuous T := (profileSynthesis q hq).continuous_of_finiteDimensional
  have hinjT : Function.Injective T := profileSynthesis_injective q hq hinj
  obtain ⟨a, ha, hbound⟩ := exists_pos_norm_sq_lower_bound T hcont hinjT
  refine ⟨a / 2, by positivity, ?_⟩
  intro c
  have hb := hbound (WithLp.toLp 2 c : EuclideanSpace ℂ ι)
  have hn : ‖(WithLp.toLp 2 c : EuclideanSpace ℂ ι)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  have hs : ‖T (WithLp.toLp 2 c)‖ ^ 2 = 2 * (kZeroGramForm q c).re := by
    exact evenKProfile_combination_norm_sq q hq c
  rw [hn, hs] at hb
  linarith

/-- The same lower bound in the genuine full-axis height L2 norm, with
the Plancherel normalization pi/2 retained explicitly. -/
theorem evenKHeight_uniform_lower_bound (hinj : Function.Injective q) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ι → ℂ,
      (Real.pi / 2) * a * (∑ i, ‖c i‖ ^ 2) ≤
        ‖∑ i, c i • (evenKHeight (q i) (hq i) : ComplexL2)‖ ^ 2 := by
  obtain ⟨a, ha, hb⟩ := kZeroGramForm_uniform_lower_bound q hq hinj
  refine ⟨a, ha, ?_⟩
  intro c
  rw [evenKHeight_combination_norm_sq q hq c, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb c) (by positivity)

end Coercivity

end ImbalancedChen.Part3.ActualKGramInverseCoerciveSourceOnly
