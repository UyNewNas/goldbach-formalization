import ImbalancedChen.Part3UpperSupportedTensorL2Closure

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual proved density theorem removes the remaining obstruction from
the preceding weak-gradient and support-limit modules. An actual core
input tending to zero has no nonzero planar L² gradient limit. Moreover
the topological closure of each actual finite-gradient graph is right
unique. No density, closedness, or self-adjointness hypothesis is supplied.

This establishes closability of each first-gradient graph. It does not
assert a self-adjoint Maass operator, spectral expansion, or Kuznetsov formula.
-/

namespace ImbalancedChen.Part3.MaassFirstGradientClosability20261025a

noncomputable section
open MeasureTheory Filter Set
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a
open ImbalancedChen.Part3.UpperSupportedTensorL2Closure20261025a

/-- Actual tensor density detects every upper-supported planar L² vector.
The density used in this proof is the previously constructed theorem. -/
theorem upperSupported_eq_zero_of_test_pairings (G : PlaneL2)
    (hG : G ∈ upperSupportedSubmodule)
    (htest : ∀ U : CompactTensor, inner ℂ G (testL2 U) = 0) : G = 0 := by
  have hspan : ∀ V ∈ smoothTensorL2Span, inner ℂ G V = 0 := by
    intro V hV
    change V ∈ Submodule.span ℂ
      (Set.range (fun T : SmoothPositiveTensor => testL2 (toMaassTensor T))) at hV
    induction hV using Submodule.span_induction with
    | mem V hV =>
        obtain ⟨T, rfl⟩ := hV
        exact htest (toMaassTensor T)
    | zero => simp
    | add V W _ _ hV hW => simp only [inner_add_right, hV, hW, add_zero]
    | smul c V _ hV => simp only [inner_smul_right, hV, mul_zero]
  have hclosed : IsClosed {V : PlaneL2 | inner ℂ G V = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hGG : G ∈ closure (smoothTensorL2Span : Set PlaneL2) := by
    change G ∈ smoothTensorL2Span.topologicalClosure
    rw [smoothTensorL2Span_topologicalClosure_eq_upperSupported]
    exact hG
  have hself : inner ℂ G G = 0 := closure_minimal hspan hclosed hGG
  exact inner_self_eq_zero.mp hself

/-- Sequential closability for either actual coordinate derivative. The
input and gradient convergence take place in their actual different L² spaces. -/
theorem gradient_limit_eq_zero (vertical : Bool)
    (k : ℕ → ℕ) (T : (n : ℕ) → Fin (k n) → CompactTensor) (G : PlaneL2)
    (hinput : Tendsto (fun n => finiteCoreL2 Finset.univ (T n)) atTop (nhds 0))
    (hgradient : Tendsto (fun n => gradientL2 vertical Finset.univ (T n))
      atTop (nhds G)) : G = 0 := by
  apply upperSupported_eq_zero_of_test_pairings G
    (gradient_limit_mem_upperSupportedSubmodule vertical k T G hgradient)
  intro U
  exact gradient_limit_annihilates_compact_tests vertical k T G hinput hgradient U

/-- The actual finite first-gradient graph, without an abstract supplier. -/
def finiteGradientGraph (vertical : Bool) : Set (HyperbolicL2 × PlaneL2) :=
  {p | ∃ (n : ℕ) (T : Fin n → CompactTensor),
    p.1 = finiteCoreL2 Finset.univ T ∧ p.2 = gradientL2 vertical Finset.univ T}

/-- Closed graph limits inherit the actual supported target subspace. -/
theorem closure_finiteGradientGraph_supported (vertical : Bool)
    {p : HyperbolicL2 × PlaneL2}
    (hp : p ∈ closure (finiteGradientGraph vertical)) :
    p.2 ∈ upperSupportedSubmodule := by
  have hclosed : IsClosed {q : HyperbolicL2 × PlaneL2 |
      q.2 ∈ upperSupportedSubmodule} :=
    isClosed_upperSupportedSubmodule.preimage continuous_snd
  apply closure_minimal (t := {q : HyperbolicL2 × PlaneL2 |
    q.2 ∈ upperSupportedSubmodule}) ?_ hclosed hp
  rintro q ⟨n, T, _, hgrad⟩
  change q.2 ∈ upperSupportedSubmodule
  rw [hgrad]
  exact gradientL2_mem_upperSupportedSubmodule vertical Finset.univ T

/-- The genuine first-order Green test also survives topological graph closure. -/
theorem closure_finiteGradientGraph_green (vertical : Bool)
    {p : HyperbolicL2 × PlaneL2}
    (hp : p ∈ closure (finiteGradientGraph vertical)) (U : CompactTensor) :
    inner ℂ p.2 (testL2 U) = -inner ℂ p.1 (liftedGradientL2 vertical U) := by
  have hclosed : IsClosed {q : HyperbolicL2 × PlaneL2 |
      inner ℂ q.2 (testL2 U) = -inner ℂ q.1 (liftedGradientL2 vertical U)} :=
    isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_fst.inner continuous_const).neg
  apply closure_minimal (t := {q : HyperbolicL2 × PlaneL2 |
    inner ℂ q.2 (testL2 U) = -inner ℂ q.1 (liftedGradientL2 vertical U)}) ?_ hclosed hp
  rintro q ⟨n, T, hin, hgrad⟩
  change inner ℂ q.2 (testL2 U) = -inner ℂ q.1 (liftedGradientL2 vertical U)
  rw [hin, hgrad]
  exact gradientL2_green vertical Finset.univ T U

/-- The whole closed graph has at most one gradient for each input. This
uses actual density and Green identities, rather than assuming a closed operator. -/
theorem closure_finiteGradientGraph_right_unique (vertical : Bool)
    {f : HyperbolicL2} {G H : PlaneL2}
    (hG : (f, G) ∈ closure (finiteGradientGraph vertical))
    (hH : (f, H) ∈ closure (finiteGradientGraph vertical)) : G = H := by
  have hsG : G ∈ upperSupportedSubmodule :=
    closure_finiteGradientGraph_supported vertical hG
  have hsH : H ∈ upperSupportedSubmodule :=
    closure_finiteGradientGraph_supported vertical hH
  have hzero : G - H = 0 := by
    apply upperSupported_eq_zero_of_test_pairings (G - H)
      (upperSupportedSubmodule.sub_mem hsG hsH)
    intro U
    rw [inner_sub_left, closure_finiteGradientGraph_green vertical hG U,
      closure_finiteGradientGraph_green vertical hH U, sub_self]
  exact sub_eq_zero.mp hzero

end
end ImbalancedChen.Part3.MaassFirstGradientClosability20261025a
