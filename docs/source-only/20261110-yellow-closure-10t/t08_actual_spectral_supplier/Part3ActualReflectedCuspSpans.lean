import ImbalancedChen.Part3ActualCharacterScatteringReflection
import ImbalancedChen.Part3ActualContinuousClassFourier

/-! The actual forward character expansion at the continued parameters
and equality of the two reflected native spans. Every column comes from
the actual physical functions at the original level. -/
namespace ImbalancedChen.Part3.ActualReflectedCuspSpans20261110

noncomputable section
open Set Filter Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualCharacterScatteringReflection20261110 ActualCriticalScatteringReciprocity20261110
open ActualCriticalCuspEvaluation20261110 ActualCharacterCuspExpansion20261110
open ActualYoungCriticalCusps20261110 ActualYoungCriticalD20261110 ActualYoungFormalClass20261110
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open ActualYoungCriticalProjection20261110 ActualYoungDilationInverse20261110
open ActualCharacterCuspRowReduction20261110 OriginalCharacterPairDilation20261102s
open Gamma0DegeneracyMapSourceOnly

local instance (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩

theorem continued_forward_dilation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (B : ℕ+) (N : ℕ) [NeZero N] (hle : q^2*(B : ℕ) ∣ N)
    (s : ℂ) (hs : 1/2 ≤ s.re) (h1 : s ≠ 1) (z : ℍ) :
    ordinary χ s (degeneracyDiagonal B B.pos • z) =
      ∑ a : CuspRowClass N, cuspCoefficient (NeZero.pos q) χ B N (classFrame a) s *
        cuspFamily N (nativeCuspEquiv N a) s z := by
  classical
  let C := fun a : CuspRowClass N => cuspCoefficient (NeZero.pos q) χ B N (classFrame a)
  let F := fun a : CuspRowClass N => fun w : ℂ => cuspFamily N (nativeCuspEquiv N a) w z
  have hc (a) : Differentiable ℂ (C a) := by
    dsimp [C,cuspCoefficient,rowWeight]
    fun_prop
  have hf (a : CuspRowClass N) := cuspFamily_meromorphic N (nativeCuspEquiv N a) z
  have H : Meromorphic (fun w => ∑ a : CuspRowClass N, C a w*F a w) := by
    apply Meromorphic.fun_sum
    intro a _
    have hc' : Meromorphic (C a) := fun w =>
      ((analyticOnNhd_univ_iff_differentiable.mpr (hc a)) w (mem_univ _)).meromorphicAt
    exact hc'.fun_mul (hf a)
  have hD (a) : DifferentiableAt ℂ (F a) s := parameterFamily_differentiable _ z s hs h1
  apply eq_at_regular_of_initial (fun w _ => ordinary_meromorphic χ _ w) (fun w _ => H w) _
    (fun he => by simp [he] at hs) h1 (ordinary_differentiable χ _ s hs h1).continuousAt
    (DifferentiableAt.fun_sum (fun a _ => ((hc a) s).mul (hD a))).continuousAt
  intro w hw
  rw [ordinary_initial (NeZero.pos q) χ hχ w hw]
  change characterLatticeOldform (NeZero.pos q) χ B w z = _
  simp only [F,C,show ∀ a : CuspRowClass N, nativeCuspEquiv N a = nativeFrameOrbit N (classFrame a)
    from fun _ => rfl,cuspFamily_initial N _ w hw]
  exact actual_oldform_eq_finite_cusp_sum (NeZero.pos q) χ B N hle w hw z

def nativeColumn (N : ℕ) [NeZero N] (t : ℝ) (a : CuspRowClass N) : ℍ → ℂ :=
  cuspFamily N (nativeCuspEquiv N a) (criticalPoint t)

private theorem finite_sum_mem {ι : Type*} [Fintype ι] (S : Submodule ℂ (ℍ → ℂ))
    (F : ι → ℍ → ℂ) (c : ι → ℂ) {H : ℍ → ℂ}
    (he : ∀ z, H z = ∑ i, c i*F i z) (hf : ∀ i, F i ∈ S) : H ∈ S := by
  have he' : H = ∑ i, c i • F i := funext (fun z => by
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he z)
  rw [he']
  exact S.sum_mem (fun i _ => S.smul_mem (c i) (hf i))

/-- At nonzero critical height each actual native cusp column at t is a
finite combination of the native columns at -t. The existence is proved
using both original changes and physical primitive reflection. -/
theorem reflected_columns (N : ℕ) [NeZero N] (t : ℝ) (ht : t ≠ 0) (a : CuspRowClass N) :
    ∃ u : CuspRowClass N → ℂ, ∀ z : ℍ,
      nativeColumn N t a z = ∑ b : CuspRowClass N, u b*nativeColumn N (-t) b z := by
  classical
  let S := Submodule.span ℂ (Set.range (nativeColumn N (-t)))
  have hsr : 1/2 ≤ (criticalPoint (-t)).re := by norm_num [criticalPoint,Complex.mul_re]
  have hs1 : criticalPoint (-t) ≠ 1 := by
    intro e
    have H := congrArg Complex.re e
    norm_num [criticalPoint,Complex.mul_re] at H
  have HD {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
      (B : ℕ+) (hlevel : q^2*(B : ℕ) ∣ N) :
      (fun z : ℍ => ordinary χ (criticalPoint t) (degeneracyDiagonal B B.pos • z)) ∈ S := by
    let r := ordinaryScale χ (criticalPoint t)/ordinaryScale χ⁻¹ (criticalPoint (-t))
    apply finite_sum_mem S (nativeColumn N (-t)) (fun b => r*
      cuspCoefficient (NeZero.pos q) χ⁻¹ B N (classFrame b) (criticalPoint (-t)))
    · intro z
      rw [ordinary_critical_reflection χ hχ ht,
        continued_forward_dilation χ⁻¹ (inverse_primitive χ hχ) B N hlevel _ hsr hs1,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [r,nativeColumn]
      ring
    · intro b
      exact Submodule.subset_span ⟨b,rfl⟩
  have HC (i : CharacterSlots N) : channelFunction i.1 i.2 (criticalPoint t) ∈ S := by
    letI : NeZero i.2.conductor := ⟨i.2.conductor_ne_zero⟩
    let j := originalSlot i
    apply finite_sum_mem S (fun b : Div j.L => dilationFunction i.2.primitiveCharacter j.pos b (criticalPoint t))
      (fun b => dilationCoefficient i.2.primitiveCharacter (criticalPoint t) j.j b)
    · intro z
      rw [j.realized,D_as_dilations]
    · intro b
      exact HD i.2.primitiveCharacter i.2.primitiveCharacter_isPrimitive (dilation j.pos b) (legal j b)
  have hcol : nativeColumn N t a ∈ S := by
    change parameterFamily ((youngCuspEquiv N).symm (nativeCuspEquiv N a)) (criticalPoint t) ∈ S
    generalize (youngCuspEquiv N).symm (nativeCuspEquiv N a) = p
    rcases p with ⟨f,u⟩
    apply finite_sum_mem S (fun ξ : DirichletCharacter ℂ (band N f.1) => channelFunction f ξ (criticalPoint t))
      (fun ξ => ((band N f.1).totient : ℂ)⁻¹*star (ξ (-(u : ZMod (band N f.1)))))
    · intro z
      rw [inverse_cusp,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    · intro ξ
      exact HC ⟨f,ξ⟩
  obtain ⟨u,hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hcol
  exact ⟨u,fun z => by simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using (congrFun hu z).symm⟩

end
end ImbalancedChen.Part3.ActualReflectedCuspSpans20261110
