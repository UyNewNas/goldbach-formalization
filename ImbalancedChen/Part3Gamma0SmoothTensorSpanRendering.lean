import ImbalancedChen.Part3Gamma0CompactWeightedTensorApproximation
import ImbalancedChen.Part3Gamma0SmoothCompactTensorCore
import Mathlib.Algebra.BigOperators.Fin

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Every element of the actual smooth positive planar tensor span is rendered
as one LITERAL finite family of the actual SmoothCompactTensor interface.
Complex coefficients are absorbed into horizontal factors; addition is an
actual Fin(n+m) concatenation. Both C-infinity fields remain proved.

If the total approximant has support in the actual reduced-carrier chart,
the total finite seed on H has support in that SAME actual carrier, even
when individual summands cancel. This is the exact support input required
by the genuine effective Poincare reconstruction and quotient L2 interface.
-/

namespace ImbalancedChen.Part3.Gamma0SmoothTensorSpanRendering20261025a

noncomputable section
open Set
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a

def promotePositiveTensor (T : SmoothPositiveTensor) : SmoothCompactTensor where
  toCompactTensor := toMaassTensor T
  horizontal_cinfty := Complex.ofRealCLM.contDiff.comp T.horizontal_smooth
  vertical_cinfty := Complex.ofRealCLM.contDiff.comp T.vertical_smooth

def scaleSmoothTensor (c : ℂ) (T : SmoothCompactTensor) : SmoothCompactTensor where
  horizontal x := c*T.horizontal x
  vertical := T.vertical
  horizontal_smooth := contDiff_const.mul T.horizontal_smooth
  vertical_smooth := T.vertical_smooth
  horizontal_compact := T.horizontal_compact.mul_left
  vertical_compact := T.vertical_compact
  vertical_positive := T.vertical_positive
  horizontal_cinfty := contDiff_const.mul T.horizontal_cinfty
  vertical_cinfty := T.vertical_cinfty

def appendSmoothTensors {n m : ℕ} (T : Fin n→SmoothCompactTensor)
    (U : Fin m→SmoothCompactTensor) : Fin (n+m)→SmoothCompactTensor := Fin.addCases T U

def smoothChartFinite {n : ℕ} (T : Fin n→SmoothCompactTensor) : (ℝ×ℝ)→ℂ :=
  finiteChartFunction Finset.univ (fun i => (T i).toCompactTensor)

theorem smoothChartFinite_append {n m : ℕ} (T : Fin n→SmoothCompactTensor)
    (U : Fin m→SmoothCompactTensor) :
    smoothChartFinite (appendSmoothTensors T U)=smoothChartFinite T+smoothChartFinite U := by
  funext p
  change (∑ i : Fin (n+m),
      (appendSmoothTensors T U i).horizontal p.1*(appendSmoothTensors T U i).vertical p.2)=
    (∑ i : Fin n,(T i).horizontal p.1*(T i).vertical p.2)+
    ∑ i : Fin m,(U i).horizontal p.1*(U i).vertical p.2
  rw [Fin.sum_univ_add]
  simp [appendSmoothTensors]

theorem smoothChartFinite_scale {n : ℕ} (c : ℂ) (T : Fin n→SmoothCompactTensor) :
    smoothChartFinite (fun i => scaleSmoothTensor c (T i))=c•smoothChartFinite T := by
  funext p
  simp only [smoothChartFinite,finiteChartFunction,scaleSmoothTensor,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A source-level finite family is constructed by span induction; no
finite representation or smoothness is a hypothesis. -/
theorem exists_finite_smooth_tensor_representation {H : (ℝ×ℝ)→ℂ}
    (hH : H∈planeTensorSpan) :
    ∃ (n : ℕ) (T : Fin n→SmoothCompactTensor),H=smoothChartFinite T := by
  induction hH using Submodule.span_induction with
  | mem H hH =>
      obtain ⟨T,rfl⟩ := hH
      refine ⟨1,fun _ => promotePositiveTensor T,?_⟩
      funext p
      simp only [smoothChartFinite,finiteChartFunction,Fin.sum_univ_one,
        promotePositiveTensor,toMaassTensor,planeTensor,Function.comp_apply]
      exact Complex.ofReal_mul _ _
  | zero =>
      refine ⟨0,Fin.elim0,?_⟩
      funext p
      simp [smoothChartFinite,finiteChartFunction]
  | add F G hF hG ihF ihG =>
      obtain ⟨n,T,hT⟩ := ihF
      obtain ⟨m,U,hU⟩ := ihG
      exact ⟨n+m,appendSmoothTensors T U,by rw [smoothChartFinite_append,hT,hU]⟩
  | smul c G hG ih =>
      obtain ⟨n,T,hT⟩ := ih
      exact ⟨n,fun i => scaleSmoothTensor c (T i),by rw [smoothChartFinite_scale,hT]⟩

theorem finiteCoreFunction_eq_smoothChartFinite {n : ℕ}
    (T : Fin n→SmoothCompactTensor) (z : UpperHalfPlane) :
    finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor) z=
      smoothChartFinite T (z.re,z.im) := by
  simp only [finiteCoreFunction,smoothChartFinite,finiteChartFunction,tensorFunctionH_eq]

/-- The support condition for the actual finite H seed follows from the
proved TOTAL planar approximant support, retaining possible cancellations. -/
theorem finite_seed_support_inside_of_chart_support
    (N : ℕ) [NeZero N] {n : ℕ} (T : Fin n→SmoothCompactTensor)
    (hsupp : ∀ p∈tsupport (smoothChartFinite T),
      0<p.2 ∧ chartLift p∈reducedCarrier N) :
    Function.support (finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor))⊆
      reducedCarrier N := by
  intro z hz
  have hn : smoothChartFinite T (z.re,z.im)≠0 := by
    simpa only [finiteCoreFunction_eq_smoothChartFinite] using hz
  have hh := (hsupp (z.re,z.im) (subset_tsupport _ hn)).2
  have heq : chartLift (z.re,z.im)=z := by
    rw [chartLift_of_positive z.im_pos]
    apply UpperHalfPlane.ext
    ext <;> rfl
  simpa only [heq] using hh

end
end ImbalancedChen.Part3.Gamma0SmoothTensorSpanRendering20261025a
