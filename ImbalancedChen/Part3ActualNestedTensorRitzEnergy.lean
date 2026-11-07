import ImbalancedChen.Part3ActualFiniteTensorWeakResolvent

/-!
Nested finite Galerkin energy for the actual coordinate Maass graph.

Every solution below is chosen from the proved unique actual finite-span
weak resolver. Orthogonality, Pythagoras and best approximation are derived
from its weak equations and the proved actual graph symmetry/coercivity.
No Ritz map, orthogonality or best-approximation supplier is assumed.
No density, infinite-dimensional closure or self-adjointness is asserted.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualNestedTensorRitzEnergy20261025a

noncomputable section

open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2Symmetry20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.ActualFiniteTensorWeakResolvent20261025a

/-- The real shifted Dirichlet pairing of the actual coordinate graph. -/
def shiftedDirichlet (u v : actualTensorDomain) : ℝ :=
  (inner ℂ (u : HyperbolicL2) ((v : HyperbolicL2) + actualTensorLaplacian v)).re

def shiftedEnergy (u : actualTensorDomain) : ℝ := shiftedDirichlet u u

/-- On every concrete finite tensor presentation this is precisely its
canonical L2 mass plus the existing actual Dirichlet integral energy. -/
theorem shiftedEnergy_finiteCore {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    shiftedEnergy ⟨finiteCoreL2 s T, finiteCoreL2_mem_actualTensorDomain s T⟩ =
      ‖finiteCoreL2 s T‖ ^ 2 + (finiteCoreEnergy s T s T).re := by
  unfold shiftedEnergy shiftedDirichlet
  rw [actualTensorLaplacian_finiteCoreL2, inner_add_right, Complex.add_re,
    finiteCoreL2_inner_Laplacian_eq_energy]
  congr 1
  rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem shiftedDirichlet_symm (u v : actualTensorDomain) :
    shiftedDirichlet u v = shiftedDirichlet v u := by
  have hm := inner_re_symm (𝕜 := ℂ) (u : HyperbolicL2) (v : HyperbolicL2)
  have hg := congrArg Complex.re (finiteTensorL2Graph_symmetric
    (actualTensorLaplacian_mem_graph u) (actualTensorLaplacian_mem_graph v))
  have hi := inner_re_symm (𝕜 := ℂ) (actualTensorLaplacian u) (v : HyperbolicL2)
  simp only [shiftedDirichlet, inner_add_right, Complex.add_re]
  linarith only [hm, hg, hi]

theorem shiftedDirichlet_add_left (u v w : actualTensorDomain) :
    shiftedDirichlet (u + v) w = shiftedDirichlet u w + shiftedDirichlet v w := by
  simp only [shiftedDirichlet, Submodule.coe_add, inner_add_left, Complex.add_re]

theorem shiftedDirichlet_add_right (u v w : actualTensorDomain) :
    shiftedDirichlet u (v + w) = shiftedDirichlet u v + shiftedDirichlet u w := by
  simp only [shiftedDirichlet, Submodule.coe_add, map_add,
    inner_add_right, Complex.add_re]
  ring

theorem shiftedDirichlet_sub_left (u v w : actualTensorDomain) :
    shiftedDirichlet (u - v) w = shiftedDirichlet u w - shiftedDirichlet v w := by
  simp only [shiftedDirichlet, Submodule.coe_sub, inner_sub_left, Complex.sub_re]

theorem shiftedDirichlet_sub_right (u v w : actualTensorDomain) :
    shiftedDirichlet u (v - w) = shiftedDirichlet u v - shiftedDirichlet u w := by
  simp only [shiftedDirichlet, Submodule.coe_sub, map_sub,
    inner_add_right, inner_sub_right, Complex.add_re, Complex.sub_re]
  ring

theorem norm_sq_le_shiftedEnergy (u : actualTensorDomain) :
    ‖(u : HyperbolicL2)‖ ^ 2 ≤ shiftedEnergy u :=
  finiteTensorL2Graph_shifted_coercive (actualTensorLaplacian_mem_graph u)

theorem shiftedEnergy_nonneg (u : actualTensorDomain) : 0 ≤ shiftedEnergy u :=
  (sq_nonneg _).trans (norm_sq_le_shiftedEnergy u)

theorem shiftedEnergy_add (u v : actualTensorDomain) :
    shiftedEnergy (u + v) = shiftedEnergy u + shiftedEnergy v +
      2 * shiftedDirichlet u v := by
  simp only [shiftedEnergy, shiftedDirichlet_add_left, shiftedDirichlet_add_right]
  rw [shiftedDirichlet_symm v u]
  ring

theorem shiftedEnergy_sub (u v : actualTensorDomain) :
    shiftedEnergy (u - v) = shiftedEnergy u + shiftedEnergy v -
      2 * shiftedDirichlet u v := by
  simp only [shiftedEnergy, shiftedDirichlet_sub_left, shiftedDirichlet_sub_right]
  rw [shiftedDirichlet_symm v u]
  ring

/-- Lift a literal finite tensor trial vector into the actual graph domain. -/
def trialLift (n : ℕ) (T : Fin n → CompactTensor) :
    actualFiniteTensorSpan n T →ₗ[ℂ] actualTensorDomain :=
  Submodule.inclusion (actualFiniteTensorSpan_le_domain n T)

/-- A canonical solution constructed from actual unique solvability. -/
def ritzSolution (n : ℕ) (T : Fin n → CompactTensor) (f : HyperbolicL2) :
    actualFiniteTensorSpan n T :=
  Classical.choose (existsUnique_actualFiniteTensor_weak_resolvent n T f).exists

def ritzVector (n : ℕ) (T : Fin n → CompactTensor) (f : HyperbolicL2) :
    actualTensorDomain := trialLift n T (ritzSolution n T f)

theorem ritzSolution_weak (n : ℕ) (T : Fin n → CompactTensor) (f : HyperbolicL2) :
    ∀ v : actualFiniteTensorSpan n T,
      inner ℂ (v : HyperbolicL2)
          ((ritzSolution n T f : HyperbolicL2) +
            actualFiniteTensorLaplacian n T (ritzSolution n T f)) =
        inner ℂ (v : HyperbolicL2) f :=
  (Classical.choose_spec (existsUnique_actualFiniteTensor_weak_resolvent n T f).exists).1

theorem ritzSolution_norm_le (n : ℕ) (T : Fin n → CompactTensor) (f : HyperbolicL2) :
    ‖(ritzSolution n T f : HyperbolicL2)‖ ≤ ‖f‖ :=
  (Classical.choose_spec (existsUnique_actualFiniteTensor_weak_resolvent n T f).exists).2

theorem shiftedDirichlet_trial_ritz
    (n : ℕ) (T : Fin n → CompactTensor) (f : HyperbolicL2)
    (v : actualFiniteTensorSpan n T) :
    shiftedDirichlet (trialLift n T v) (ritzVector n T f) =
      (inner ℂ (v : HyperbolicL2) f).re := by
  change (inner ℂ (v : HyperbolicL2)
    ((ritzSolution n T f : HyperbolicL2) +
      actualFiniteTensorLaplacian n T (ritzSolution n T f))).re = _
  rw [ritzSolution_weak]

/-- The actual weak equation bounds every finite trial energy using only
the ambient L2 forcing, uniformly over all finite tensor families. -/
theorem shiftedEnergy_ritz_le_forcing (n : ℕ) (T : Fin n → CompactTensor)
    (f : HyperbolicL2) : shiftedEnergy (ritzVector n T f) ≤ ‖f‖ ^ 2 := by
  change shiftedDirichlet (trialLift n T (ritzSolution n T f)) (ritzVector n T f) ≤ _
  rw [shiftedDirichlet_trial_ritz]
  calc
    _ ≤ ‖(ritzSolution n T f : HyperbolicL2)‖ * ‖f‖ :=
      re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_right (ritzSolution_norm_le n T f) (norm_nonneg _)
    _ = _ := by ring

/-- Nested Galerkin orthogonality is derived by subtracting the two
actual weak equations tested against the same small-span vector. -/
theorem nested_ritz_orthogonality
    {n m : ℕ} (T : Fin n → CompactTensor) (U : Fin m → CompactTensor)
    (hTU : actualFiniteTensorSpan n T ≤ actualFiniteTensorSpan m U)
    (f : HyperbolicL2) (v : actualFiniteTensorSpan n T) :
    shiftedDirichlet (trialLift n T v) (ritzVector m U f - ritzVector n T f) = 0 := by
  rw [shiftedDirichlet_sub_right, shiftedDirichlet_trial_ritz]
  have hbig := shiftedDirichlet_trial_ritz m U f (Submodule.inclusion hTU v)
  have hlift : trialLift m U (Submodule.inclusion hTU v) = trialLift n T v := by
    apply Subtype.ext
    rfl
  rw [hlift] at hbig
  rw [hbig, sub_self]

/-- Exact energy Pythagoras for two actual nested finite tensor trials. -/
theorem nested_ritz_pythagoras
    {n m : ℕ} (T : Fin n → CompactTensor) (U : Fin m → CompactTensor)
    (hTU : actualFiniteTensorSpan n T ≤ actualFiniteTensorSpan m U)
    (f : HyperbolicL2) :
    shiftedEnergy (ritzVector m U f) = shiftedEnergy (ritzVector n T f) +
      shiftedEnergy (ritzVector m U f - ritzVector n T f) := by
  have ho := nested_ritz_orthogonality T U hTU f (ritzSolution n T f)
  change shiftedDirichlet (ritzVector n T f) (ritzVector m U f - ritzVector n T f) = 0 at ho
  rw [shiftedDirichlet_sub_right] at ho
  have he := shiftedEnergy_sub (ritzVector m U f) (ritzVector n T f)
  rw [shiftedDirichlet_symm (ritzVector m U f) (ritzVector n T f)] at he
  change shiftedDirichlet (ritzVector n T f) (ritzVector m U f) -
    shiftedEnergy (ritzVector n T f) = 0 at ho
  linarith only [he, ho]

theorem nested_ritz_energy_mono
    {n m : ℕ} (T : Fin n → CompactTensor) (U : Fin m → CompactTensor)
    (hTU : actualFiniteTensorSpan n T ≤ actualFiniteTensorSpan m U)
    (f : HyperbolicL2) :
    shiftedEnergy (ritzVector n T f) ≤ shiftedEnergy (ritzVector m U f) := by
  rw [nested_ritz_pythagoras T U hTU f]
  exact le_add_of_nonneg_right (shiftedEnergy_nonneg _)

/-- Best approximation is an equality with an explicit nonnegative
defect, not an assumed projection property. -/
theorem nested_ritz_bestApprox_identity
    {n m : ℕ} (T : Fin n → CompactTensor) (U : Fin m → CompactTensor)
    (hTU : actualFiniteTensorSpan n T ≤ actualFiniteTensorSpan m U)
    (f : HyperbolicL2) (v : actualFiniteTensorSpan n T) :
    shiftedEnergy (ritzVector m U f - trialLift n T v) =
      shiftedEnergy (ritzVector m U f - ritzVector n T f) +
        shiftedEnergy (ritzVector n T f - trialLift n T v) := by
  have ho := nested_ritz_orthogonality T U hTU f (ritzSolution n T f - v)
  have hmap : trialLift n T (ritzSolution n T f - v) =
      ritzVector n T f - trialLift n T v := map_sub (trialLift n T) _ _
  rw [hmap, shiftedDirichlet_symm] at ho
  have hsplit : ritzVector m U f - trialLift n T v =
      (ritzVector m U f - ritzVector n T f) +
        (ritzVector n T f - trialLift n T v) := by abel
  rw [hsplit, shiftedEnergy_add, ho, mul_zero, add_zero]

/-- Energy Céa bound with constant one for the actual nested weak
solutions, together with coercive control of their physical L2 error. -/
theorem nested_ritz_bestApprox_bound
    {n m : ℕ} (T : Fin n → CompactTensor) (U : Fin m → CompactTensor)
    (hTU : actualFiniteTensorSpan n T ≤ actualFiniteTensorSpan m U)
    (f : HyperbolicL2) (v : actualFiniteTensorSpan n T) :
    shiftedEnergy (ritzVector m U f - ritzVector n T f) ≤
        shiftedEnergy (ritzVector m U f - trialLift n T v) ∧
      ‖((ritzVector m U f - ritzVector n T f : actualTensorDomain) : HyperbolicL2)‖ ^ 2 ≤
        shiftedEnergy (ritzVector m U f - trialLift n T v) := by
  have he : shiftedEnergy (ritzVector m U f - ritzVector n T f) ≤
      shiftedEnergy (ritzVector m U f - trialLift n T v) := by
    rw [nested_ritz_bestApprox_identity T U hTU f v]
    exact le_add_of_nonneg_right (shiftedEnergy_nonneg _)
  exact ⟨he, (norm_sq_le_shiftedEnergy _).trans he⟩

/-- Future completion arguments can use the actual energy increment to
control the physical L2 difference, with no assumed Cauchy property. -/
theorem nested_ritz_L2_error_le_energy_increment
    {n m : ℕ} (T : Fin n → CompactTensor) (U : Fin m → CompactTensor)
    (hTU : actualFiniteTensorSpan n T ≤ actualFiniteTensorSpan m U)
    (f : HyperbolicL2) :
    ‖((ritzVector m U f - ritzVector n T f : actualTensorDomain) : HyperbolicL2)‖ ^ 2 ≤
      shiftedEnergy (ritzVector m U f) - shiftedEnergy (ritzVector n T f) := by
  have hc := norm_sq_le_shiftedEnergy (ritzVector m U f - ritzVector n T f)
  have hp := nested_ritz_pythagoras T U hTU f
  linarith only [hc, hp]

/-- Three actual nested trials have exactly additive energy increments.
This preserves the actual differences needed by later completion work. -/
theorem nested_ritz_three_space_pythagoras
    {n m r : ℕ} (T : Fin n → CompactTensor) (U : Fin m → CompactTensor)
    (V : Fin r → CompactTensor)
    (hTU : actualFiniteTensorSpan n T ≤ actualFiniteTensorSpan m U)
    (hUV : actualFiniteTensorSpan m U ≤ actualFiniteTensorSpan r V)
    (f : HyperbolicL2) :
    shiftedEnergy (ritzVector r V f - ritzVector n T f) =
      shiftedEnergy (ritzVector r V f - ritzVector m U f) +
        shiftedEnergy (ritzVector m U f - ritzVector n T f) := by
  have hTV := nested_ritz_pythagoras T V (hTU.trans hUV) f
  have hTU' := nested_ritz_pythagoras T U hTU f
  have hUV' := nested_ritz_pythagoras U V hUV f
  linarith only [hTV, hTU', hUV']

end

end ImbalancedChen.Part3.ActualNestedTensorRitzEnergy20261025a
