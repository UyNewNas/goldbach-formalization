import ImbalancedChen.Part3ActualNestedTensorRitzEnergy
import ImbalancedChen.Part3MaassGradientUpperSupportClosure

/-!
Presentation-independent actual planar first-gradient maps on the actual
finite tensor L2 domain. Equality in canonical hyperbolic L2 gives equality
of the continuous finite functions, hence of their zero-extended chart
functions and their coordinate first derivatives. The output is the actual
planar L2 gradient, not an assumed derivative-map supplier.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualTensorGradientLinearMaps20261025a

noncomputable section

open MeasureTheory Filter
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzEnergy20261025a

def chartFirstGradient (vertical : Bool) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if vertical then deriv (fun y => F (p.1, y)) p.2
  else deriv (fun x => F (x, p.2)) p.1

theorem chartFirstGradient_finiteChartFunction {ι : Type*}
    (vertical : Bool) (s : Finset ι) (T : ι → CompactTensor) :
    chartFirstGradient vertical (finiteChartFunction s T) = finiteGradient vertical s T := by
  funext p
  cases vertical
  · change deriv (fun x : ℝ => ∑ i ∈ s, (T i).horizontal x * (T i).vertical p.2) p.1 =
      ∑ i ∈ s, deriv (T i).horizontal p.1 * (T i).vertical p.2
    rw [deriv_fun_sum (fun i _ =>
      ((T i).horizontal_smooth.differentiable (by norm_num) p.1).mul_const _)]
    simp only [deriv_mul_const_field]
  · change deriv (fun y : ℝ => ∑ i ∈ s, (T i).horizontal p.1 * (T i).vertical y) p.2 =
      ∑ i ∈ s, (T i).horizontal p.1 * deriv (T i).vertical p.2
    rw [deriv_fun_sum (fun i _ =>
      ((T i).vertical_smooth.differentiable (by norm_num) p.2).const_mul _)]
    simp only [deriv_const_mul_field]

/-- Equality of actual input L2 classes determines both actual first
derivatives, including their zero extension below the upper chart. -/
theorem gradientL2_eq_of_input_eq {ι κ : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (hinput : finiteCoreL2 s T = finiteCoreL2 t U) :
    gradientL2 vertical s T = gradientL2 vertical t U := by
  have hae := (MemLp.toLp_eq_toLp_iff (finiteCoreFunction_memLp s T)
    (finiteCoreFunction_memLp t U)).mp hinput
  have hchart := finiteChartFunction_eq_of_finiteCoreFunction_eq s T t U
    (finiteCoreFunction_eq_of_ae_eq s T t U hae)
  have hgrad : finiteGradient vertical s T = finiteGradient vertical t U := by
    rw [← chartFirstGradient_finiteChartFunction, ← chartFirstGradient_finiteChartFunction, hchart]
  unfold gradientL2
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun p => congrFun hgrad p)

theorem finiteGradient_append {n m : ℕ} (vertical : Bool)
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) :
    finiteGradient vertical Finset.univ (appendTensors T U) =
      finiteGradient vertical Finset.univ T + finiteGradient vertical Finset.univ U := by
  funext p
  change (∑ i : Fin (n + m), tensorGradient vertical (appendTensors T U i) p) =
    (∑ i : Fin n, tensorGradient vertical (T i) p) +
      ∑ i : Fin m, tensorGradient vertical (U i) p
  rw [Fin.sum_univ_add]
  simp [appendTensors]

theorem finiteGradient_scale {ι : Type*} (vertical : Bool) (s : Finset ι)
    (T : ι → CompactTensor) (c : ℂ) :
    finiteGradient vertical s (fun i => scaleTensorHorizontal c (T i)) =
      c • finiteGradient vertical s T := by
  funext p
  cases vertical <;>
    simp only [finiteGradient, tensorGradient, if_false, if_true,
      tensorDx, tensorDy, scaleTensorHorizontal, deriv_const_mul_field',
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;> ring

private theorem toLp_add_of_eq {f g k : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure (ℝ × ℝ)))
    (hg : MemLp g 2 (volume : Measure (ℝ × ℝ)))
    (hk : MemLp k 2 (volume : Measure (ℝ × ℝ))) (h : k = f + g) :
    hk.toLp k = hf.toLp f + hg.toLp g := by
  calc
    _ = (hf.add hg).toLp (f + g) :=
      MemLp.toLp_congr _ _ (Eventually.of_forall fun p => congrFun h p)
    _ = _ := MemLp.toLp_add hf hg

private theorem toLp_smul_of_eq {f k : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure (ℝ × ℝ)))
    (hk : MemLp k 2 (volume : Measure (ℝ × ℝ))) (c : ℂ) (h : k = c • f) :
    hk.toLp k = c • hf.toLp f := by
  calc
    _ = (hf.const_smul c).toLp (c • f) :=
      MemLp.toLp_congr _ _ (Eventually.of_forall fun p => congrFun h p)
    _ = _ := MemLp.toLp_const_smul c hf

theorem gradientL2_append {n m : ℕ} (vertical : Bool)
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) :
    gradientL2 vertical Finset.univ (appendTensors T U) =
      gradientL2 vertical Finset.univ T + gradientL2 vertical Finset.univ U :=
  toLp_add_of_eq _ _ _ (finiteGradient_append vertical T U)

theorem gradientL2_scale {ι : Type*} (vertical : Bool) (s : Finset ι)
    (T : ι → CompactTensor) (c : ℂ) :
    gradientL2 vertical s (fun i => scaleTensorHorizontal c (T i)) =
      c • gradientL2 vertical s T :=
  toLp_smul_of_eq _ _ c (finiteGradient_scale vertical s T c)

def actualGradientGraph (vertical : Bool) : Set (HyperbolicL2 × PlaneL2) :=
  {p | ∃ (n : ℕ) (T : Fin n → CompactTensor),
    p.1 = finiteCoreL2 Finset.univ T ∧ p.2 = gradientL2 vertical Finset.univ T}

theorem actualGradientGraph_right_unique (vertical : Bool)
    {f : HyperbolicL2} {g k : PlaneL2}
    (hg : (f, g) ∈ actualGradientGraph vertical)
    (hk : (f, k) ∈ actualGradientGraph vertical) : g = k := by
  rcases hg with ⟨n, T, hf, hg⟩
  rcases hk with ⟨m, U, hf', hk⟩
  rw [hg, hk]
  exact gradientL2_eq_of_input_eq vertical Finset.univ T Finset.univ U (hf.symm.trans hf')

theorem actualGradientGraph_add (vertical : Bool)
    {f u : HyperbolicL2} {g v : PlaneL2}
    (hfg : (f, g) ∈ actualGradientGraph vertical)
    (huv : (u, v) ∈ actualGradientGraph vertical) :
    (f + u, g + v) ∈ actualGradientGraph vertical := by
  rcases hfg with ⟨n, T, hf, hg⟩
  rcases huv with ⟨m, U, hu, hv⟩
  refine ⟨n + m, appendTensors T U, ?_, ?_⟩
  · rw [finiteCoreL2_append, hf, hu]
  · rw [gradientL2_append, hg, hv]

theorem actualGradientGraph_smul (vertical : Bool) (c : ℂ)
    {f : HyperbolicL2} {g : PlaneL2} (hfg : (f, g) ∈ actualGradientGraph vertical) :
    (c • f, c • g) ∈ actualGradientGraph vertical := by
  rcases hfg with ⟨n, T, hf, hg⟩
  refine ⟨n, fun i => scaleTensorHorizontal c (T i), ?_, ?_⟩
  · rw [finiteCoreL2_scale, hf]
  · rw [gradientL2_scale, hg]

private theorem actualGradient_exists (vertical : Bool) (u : actualTensorDomain) :
    ∃ G : PlaneL2, ((u : HyperbolicL2), G) ∈ actualGradientGraph vertical := by
  rcases u.property with ⟨g, n, T, hf, hg⟩
  exact ⟨gradientL2 vertical Finset.univ T, n, T, hf, rfl⟩

private def actualGradientValue (vertical : Bool) (u : actualTensorDomain) : PlaneL2 :=
  Classical.choose (actualGradient_exists vertical u)

private theorem actualGradientValue_mem_graph (vertical : Bool) (u : actualTensorDomain) :
    ((u : HyperbolicL2), actualGradientValue vertical u) ∈ actualGradientGraph vertical :=
  Classical.choose_spec (actualGradient_exists vertical u)

/-- The two actual coordinate first derivatives as complex linear maps
from the actual finite hyperbolic tensor domain to planar Lebesgue L2. -/
def actualGradient (vertical : Bool) : actualTensorDomain →ₗ[ℂ] PlaneL2 where
  toFun := actualGradientValue vertical
  map_add' u v := actualGradientGraph_right_unique vertical
    (actualGradientValue_mem_graph vertical (u + v))
    (actualGradientGraph_add vertical (actualGradientValue_mem_graph vertical u)
      (actualGradientValue_mem_graph vertical v))
  map_smul' c u := actualGradientGraph_right_unique vertical
    (actualGradientValue_mem_graph vertical (c • u))
    (actualGradientGraph_smul vertical c (actualGradientValue_mem_graph vertical u))

theorem actualGradient_mem_graph (vertical : Bool) (u : actualTensorDomain) :
    ((u : HyperbolicL2), actualGradient vertical u) ∈ actualGradientGraph vertical :=
  actualGradientValue_mem_graph vertical u

theorem actualGradient_finiteCore {ι : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) :
    actualGradient vertical ⟨finiteCoreL2 s T, finiteCoreL2_mem_actualTensorDomain s T⟩ =
      gradientL2 vertical s T := by
  rcases actualGradient_mem_graph vertical
      ⟨finiteCoreL2 s T, finiteCoreL2_mem_actualTensorDomain s T⟩ with ⟨n, U, hf, hg⟩
  rw [hg]
  exact gradientL2_eq_of_input_eq vertical Finset.univ U s T hf.symm

theorem actualGradient_upperSupported (vertical : Bool) (u : actualTensorDomain) :
    actualGradient vertical u ∈ upperSupportedSubmodule := by
  rcases actualGradient_mem_graph vertical u with ⟨n, T, hf, hg⟩
  rw [hg]
  exact gradientL2_mem_upperSupportedSubmodule vertical Finset.univ T

private theorem gradientL2_inner_self_integral {ι : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) :
    inner ℂ (gradientL2 vertical s T) (gradientL2 vertical s T) =
      ∫ p : ℝ × ℝ, star (finiteGradient vertical s T p) * finiteGradient vertical s T p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(finiteGradient_memLp vertical s T).coeFn_toLp] with p hp
  change gradientL2 vertical s T p = finiteGradient vertical s T p at hp
  rw [hp]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem finiteCoreEnergy_eq_gradientL2_norms {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    (finiteCoreEnergy s T s T).re =
      ‖gradientL2 false s T‖ ^ 2 + ‖gradientL2 true s T‖ ^ 2 := by
  have hnorm (vertical : Bool) :
      (inner ℂ (gradientL2 vertical s T) (gradientL2 vertical s T)).re =
        ‖gradientL2 vertical s T‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [finiteCoreEnergy_eq_gradient_integrals, Complex.add_re,
    ← gradientL2_inner_self_integral false s T, ← gradientL2_inner_self_integral true s T,
    hnorm false, hnorm true]

/-- Exact actual energy decomposition, now independent of every tensor
presentation and retaining the two true planar derivative norms. -/
theorem shiftedEnergy_eq_gradient_norms (u : actualTensorDomain) :
    shiftedEnergy u = ‖(u : HyperbolicL2)‖ ^ 2 +
      ‖actualGradient false u‖ ^ 2 + ‖actualGradient true u‖ ^ 2 := by
  rcases actualTensorLaplacian_mem_graph u with ⟨n, T, hf, hg⟩
  have hu : u = ⟨finiteCoreL2 Finset.univ T, finiteCoreL2_mem_actualTensorDomain Finset.univ T⟩ :=
    Subtype.ext hf
  rw [hu, shiftedEnergy_finiteCore, actualGradient_finiteCore, actualGradient_finiteCore,
    finiteCoreEnergy_eq_gradientL2_norms]
  ring

end

end ImbalancedChen.Part3.ActualTensorGradientLinearMaps20261025a
