import ImbalancedChen.Part3MaassFiniteCoreL2Symmetry
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual finite tensor L² graph is closed under zero, addition and complex
scalar multiplication. Its actual input domain is therefore a submodule,
and right uniqueness produces an actual Laplacian linear map on that domain.
Restriction to any subspace of this domain is constructed without an operator
supplier premise. No topological closure or density assertion is made.
-/

namespace ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreResolventCoercivity20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a

def scaleTensorHorizontal (c : ℂ) (T : CompactTensor) : CompactTensor where
  horizontal := fun x => c * T.horizontal x
  vertical := T.vertical
  horizontal_smooth := contDiff_const.mul T.horizontal_smooth
  vertical_smooth := T.vertical_smooth
  horizontal_compact := T.horizontal_compact.mul_left
  vertical_compact := T.vertical_compact
  vertical_positive := T.vertical_positive

def appendTensors {n m : ℕ} (T : Fin n → CompactTensor)
    (U : Fin m → CompactTensor) : Fin (n + m) → CompactTensor :=
  Fin.addCases T U

theorem finiteCoreFunction_append {n m : ℕ}
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) :
    finiteCoreFunction Finset.univ (appendTensors T U) =
      finiteCoreFunction Finset.univ T + finiteCoreFunction Finset.univ U := by
  funext z
  change (∑ i : Fin (n + m),
    tensorFunctionH (appendTensors T U i).horizontal (appendTensors T U i).vertical z) =
    (∑ i : Fin n, tensorFunctionH (T i).horizontal (T i).vertical z) +
      ∑ i : Fin m, tensorFunctionH (U i).horizontal (U i).vertical z
  rw [Fin.sum_univ_add]
  simp [appendTensors]

theorem finiteCoreLaplacian_append {n m : ℕ}
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) :
    finiteCoreLaplacian Finset.univ (appendTensors T U) =
      finiteCoreLaplacian Finset.univ T + finiteCoreLaplacian Finset.univ U := by
  funext z
  change (∑ i : Fin (n + m), tensorHyperbolicLaplacianH
    (appendTensors T U i).horizontal (appendTensors T U i).vertical z) =
    (∑ i : Fin n, tensorHyperbolicLaplacianH (T i).horizontal (T i).vertical z) +
      ∑ i : Fin m, tensorHyperbolicLaplacianH (U i).horizontal (U i).vertical z
  rw [Fin.sum_univ_add]
  simp [appendTensors]

theorem finiteCoreFunction_scale {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (c : ℂ) :
    finiteCoreFunction s (fun i => scaleTensorHorizontal c (T i)) =
      c • finiteCoreFunction s T := by
  funext z
  simp only [finiteCoreFunction, scaleTensorHorizontal, tensorFunctionH,
    tensorFunction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finiteCoreLaplacian_scale {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (c : ℂ) :
    finiteCoreLaplacian s (fun i => scaleTensorHorizontal c (T i)) =
      c • finiteCoreLaplacian s T := by
  funext z
  simp only [finiteCoreLaplacian, scaleTensorHorizontal, tensorHyperbolicLaplacianH,
    tensorHyperbolicLaplacian, deriv_const_mul_field', deriv_const_mul_field,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem toLp_add_of_eq {f g k : UpperHalfPlane → ℂ}
    (hf : MemLp f 2 (volume : Measure UpperHalfPlane))
    (hg : MemLp g 2 (volume : Measure UpperHalfPlane))
    (hk : MemLp k 2 (volume : Measure UpperHalfPlane)) (h : k = f + g) :
    hk.toLp k = hf.toLp f + hg.toLp g := by
  calc
    _ = (hf.add hg).toLp (f + g) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => congrFun h z)
    _ = _ := MemLp.toLp_add hf hg

private theorem toLp_smul_of_eq {f k : UpperHalfPlane → ℂ}
    (hf : MemLp f 2 (volume : Measure UpperHalfPlane))
    (hk : MemLp k 2 (volume : Measure UpperHalfPlane)) (c : ℂ) (h : k = c • f) :
    hk.toLp k = c • hf.toLp f := by
  calc
    _ = (hf.const_smul c).toLp (c • f) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => congrFun h z)
    _ = _ := MemLp.toLp_const_smul c hf

theorem finiteCoreL2_append {n m : ℕ}
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) :
    finiteCoreL2 Finset.univ (appendTensors T U) =
      finiteCoreL2 Finset.univ T + finiteCoreL2 Finset.univ U :=
  toLp_add_of_eq _ _ _ (finiteCoreFunction_append T U)

theorem finiteCoreLaplacianL2_append {n m : ℕ}
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) :
    finiteCoreLaplacianL2 Finset.univ (appendTensors T U) =
      finiteCoreLaplacianL2 Finset.univ T + finiteCoreLaplacianL2 Finset.univ U :=
  toLp_add_of_eq _ _ _ (finiteCoreLaplacian_append T U)

theorem finiteCoreL2_scale {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (c : ℂ) :
    finiteCoreL2 s (fun i => scaleTensorHorizontal c (T i)) = c • finiteCoreL2 s T :=
  toLp_smul_of_eq _ _ c (finiteCoreFunction_scale s T c)

theorem finiteCoreLaplacianL2_scale {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (c : ℂ) :
    finiteCoreLaplacianL2 s (fun i => scaleTensorHorizontal c (T i)) =
      c • finiteCoreLaplacianL2 s T :=
  toLp_smul_of_eq _ _ c (finiteCoreLaplacian_scale s T c)

theorem finiteTensorL2Graph_zero : ((0 : HyperbolicL2), 0) ∈ finiteTensorL2Graph := by
  refine ⟨0, Fin.elim0, ?_, ?_⟩
  · simp [finiteCoreL2, finiteCoreFunction]
  · simp [finiteCoreLaplacianL2, finiteCoreLaplacian]

theorem finiteTensorL2Graph_add {f g u v : HyperbolicL2}
    (hfg : (f, g) ∈ finiteTensorL2Graph) (huv : (u, v) ∈ finiteTensorL2Graph) :
    (f + u, g + v) ∈ finiteTensorL2Graph := by
  rcases hfg with ⟨n, T, hf, hg⟩
  rcases huv with ⟨m, U, hu, hv⟩
  refine ⟨n + m, appendTensors T U, ?_, ?_⟩
  · rw [finiteCoreL2_append, hf, hu]
  · rw [finiteCoreLaplacianL2_append, hg, hv]

theorem finiteTensorL2Graph_smul (c : ℂ) {f g : HyperbolicL2}
    (hfg : (f, g) ∈ finiteTensorL2Graph) : (c • f, c • g) ∈ finiteTensorL2Graph := by
  rcases hfg with ⟨n, T, hf, hg⟩
  refine ⟨n, fun i => scaleTensorHorizontal c (T i), ?_, ?_⟩
  · rw [finiteCoreL2_scale, hf]
  · rw [finiteCoreLaplacianL2_scale, hg]

/-- The actual domain of the actual finite tensor graph. -/
def actualTensorDomain : Submodule ℂ HyperbolicL2 where
  carrier := {f | ∃ g, (f, g) ∈ finiteTensorL2Graph}
  zero_mem' := ⟨0, finiteTensorL2Graph_zero⟩
  add_mem' := by
    rintro f u ⟨g, hfg⟩ ⟨v, huv⟩
    exact ⟨g + v, finiteTensorL2Graph_add hfg huv⟩
  smul_mem' := by
    rintro c f ⟨g, hfg⟩
    exact ⟨c • g, finiteTensorL2Graph_smul c hfg⟩

private def actualTensorLaplacianValue (u : actualTensorDomain) : HyperbolicL2 :=
  Classical.choose u.property

private theorem actualTensorLaplacianValue_mem_graph (u : actualTensorDomain) :
    ((u : HyperbolicL2), actualTensorLaplacianValue u) ∈ finiteTensorL2Graph :=
  Classical.choose_spec u.property

/-- The actual Laplacian linear map, obtained from graph closure and
proved right uniqueness, rather than an assumed operator supplier. -/
def actualTensorLaplacian : actualTensorDomain →ₗ[ℂ] HyperbolicL2 where
  toFun := actualTensorLaplacianValue
  map_add' u v := finiteTensorL2Graph_right_unique
    (actualTensorLaplacianValue_mem_graph (u + v))
    (finiteTensorL2Graph_add (actualTensorLaplacianValue_mem_graph u)
      (actualTensorLaplacianValue_mem_graph v))
  map_smul' c u := finiteTensorL2Graph_right_unique
    (actualTensorLaplacianValue_mem_graph (c • u))
    (finiteTensorL2Graph_smul c (actualTensorLaplacianValue_mem_graph u))

theorem actualTensorLaplacian_mem_graph (u : actualTensorDomain) :
    ((u : HyperbolicL2), actualTensorLaplacian u) ∈ finiteTensorL2Graph :=
  actualTensorLaplacianValue_mem_graph u

theorem actualTensorLaplacian_eq_of_mem_graph (u : actualTensorDomain) {v : HyperbolicL2}
    (h : ((u : HyperbolicL2), v) ∈ finiteTensorL2Graph) : actualTensorLaplacian u = v :=
  finiteTensorL2Graph_right_unique (actualTensorLaplacian_mem_graph u) h

private theorem reindex_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i : Fin (Fintype.card s), f ((Fintype.equivFin s).symm i)) = ∑ i ∈ s, f i := by
  classical
  calc
    _ = ∑ j : s, f j := Equiv.sum_comp (Fintype.equivFin s).symm (fun j : s => f j)
    _ = _ := Finset.sum_coe_sort s f

/-- Every existing finite tensor presentation gives a pair in the actual
graph, even when its index set is an arbitrary finite subset of a type. -/
theorem finiteCoreL2_pair_mem_graph {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) :
    (finiteCoreL2 s T, finiteCoreLaplacianL2 s T) ∈ finiteTensorL2Graph := by
  classical
  let U : Fin (Fintype.card s) → CompactTensor :=
    fun i => T ((Fintype.equivFin s).symm i)
  have hf : finiteCoreFunction Finset.univ U = finiteCoreFunction s T := by
    funext z
    exact reindex_sum s (fun i => tensorFunctionH (T i).horizontal (T i).vertical z)
  have hg : finiteCoreLaplacian Finset.univ U = finiteCoreLaplacian s T := by
    funext z
    exact reindex_sum s (fun i =>
      tensorHyperbolicLaplacianH (T i).horizontal (T i).vertical z)
  refine ⟨Fintype.card s, U, ?_, ?_⟩
  · exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => (congrFun hf z).symm)
  · exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => (congrFun hg z).symm)

theorem finiteCoreL2_mem_actualTensorDomain {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) : finiteCoreL2 s T ∈ actualTensorDomain :=
  ⟨finiteCoreLaplacianL2 s T, finiteCoreL2_pair_mem_graph s T⟩

theorem actualTensorLaplacian_finiteCoreL2 {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    actualTensorLaplacian ⟨finiteCoreL2 s T, finiteCoreL2_mem_actualTensorDomain s T⟩ =
      finiteCoreLaplacianL2 s T :=
  actualTensorLaplacian_eq_of_mem_graph _ (finiteCoreL2_pair_mem_graph s T)

/-- Restriction of the actual operator to an actual subspace, ready for
finite-dimensional Ritz/Galerkin arguments. -/
def restrictActualTensorLaplacian (V : Submodule ℂ HyperbolicL2)
    (hV : V ≤ actualTensorDomain) : V →ₗ[ℂ] HyperbolicL2 :=
  actualTensorLaplacian.comp (Submodule.inclusion hV)

theorem restrictActualTensorLaplacian_mem_graph (V : Submodule ℂ HyperbolicL2)
    (hV : V ≤ actualTensorDomain) (u : V) :
    ((u : HyperbolicL2), restrictActualTensorLaplacian V hV u) ∈ finiteTensorL2Graph :=
  actualTensorLaplacian_mem_graph (Submodule.inclusion hV u)

theorem span_range_le_actualTensorDomain {ι : Type*} (u : ι → actualTensorDomain) :
    Submodule.span ℂ (Set.range (fun i => (u i : HyperbolicL2))) ≤ actualTensorDomain := by
  apply Submodule.span_le.mpr
  rintro f ⟨i, rfl⟩
  exact (u i).property

end

end ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
