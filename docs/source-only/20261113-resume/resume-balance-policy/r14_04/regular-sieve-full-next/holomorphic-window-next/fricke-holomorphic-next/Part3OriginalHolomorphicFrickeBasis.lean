import ImbalancedChen.Part3OriginalHolomorphicPeterssonSpace
import ImbalancedChen.Part3ActualFrickeQuotientMeasure

/-! The true determinant-one Fricke action on the original weight-2r
space at its own level, with the native unscaled Petersson norm. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicFrickeBasis20261113
open Set Complex Matrix SpecialLinearGroup MeasureTheory UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane ModularForm InnerProductSpace Pointwise ComplexConjugate
open FrickeNormalizer ActualFrickeQuotientMeasure20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0FiniteMeasureCarrier20261024z
open OriginalHolomorphicPeterssonSpace20261112 OriginalHolomorphicCuspFrames20261110
open scoped OriginalHolomorphicPeterssonSpace20261112

def W (N : ℕ) [NeZero N] : GL (Fin 2) ℝ := mapGL ℝ (frickeSL N (NeZero.pos N))

theorem mapGL_realSL (g : SL(2,ℤ)) : mapGL ℝ (realSL g)=mapGL ℝ g := by
  apply Units.ext
  ext i j
  simp [realSL,mapGL_coe_matrix,SpecialLinearGroup.map_apply_coe]

private theorem gl_conjugate (N : ℕ) [NeZero N] (u : CongruenceSubgroup.Gamma0 N) :
    (W N)⁻¹*mapGL ℝ (u:SL(2,ℤ))*W N=mapGL ℝ (frickeGamma0 N u:SL(2,ℤ)) := by
  have q := congrArg (mapGL ℝ) (frickeSL_conjugate_gamma0 N (NeZero.pos N) u)
  simpa only [W,map_mul,map_inv,mapGL_realSL] using q

theorem normalizes (N : ℕ) [NeZero N] :
    ConjAct.toConjAct (W N)⁻¹ • levelGroup N=levelGroup N := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨g,hg,rfl⟩ := Subgroup.mem_map.mp hy
    let u : CongruenceSubgroup.Gamma0 N := ⟨g,hg⟩
    rw [ConjAct.toConjAct_smul,inv_inv,gl_conjugate N u]
    exact Subgroup.mem_map.mpr ⟨_,(frickeGamma0 N u).property,rfl⟩
  · intro hx
    obtain ⟨g,hg,rfl⟩ := Subgroup.mem_map.mp hx
    let u : CongruenceSubgroup.Gamma0 N := ⟨g,hg⟩
    let v := frickeGamma0 N u
    refine ⟨mapGL ℝ (v:SL(2,ℤ)),Subgroup.mem_map.mpr ⟨_,v.property,rfl⟩,?_⟩
    rw [ConjAct.toConjAct_smul,inv_inv,gl_conjugate]
    change mapGL ℝ ((frickeGamma0 N (frickeGamma0 N u)):SL(2,ℤ))=_
    rw [frickeGamma0_involutive N (NeZero.pos N) u]

def action (N r : ℕ) [NeZero N] (f : Forms N r) : Forms N r :=
  (normalizes N) ▸ CuspForm.translate f (W N)

theorem action_function (N r : ℕ) [NeZero N] (f : Forms N r) :
    (⇑(action N r f):ℍ → ℂ)=(⇑f ∣[2*(r:ℤ)] W N) := by
  have transport {A B : Subgroup (GL (Fin 2) ℝ)} (H : A=B) (g : CuspForm A (2*(r:ℤ))) :
      (⇑(H ▸ g : CuspForm B (2*(r:ℤ))) : ℍ → ℂ)=⇑g := by subst B; rfl
  exact transport (normalizes N) (CuspForm.translate f (W N))

theorem action_apply (N r : ℕ) [NeZero N] (f : Forms N r) (w : ℍ) :
    action N r f w=f (W N • w)*denom (W N) w^(-(2*(r:ℤ))) := by
  rw [show action N r f w=(⇑f ∣[2*(r:ℤ)] W N) w from congrFun (action_function N r f) w]
  simp [ModularForm.slash_apply,W,UpperHalfPlane.σ]

def actionLinear (N r : ℕ) [NeZero N] : Forms N r →ₗ[ℂ] Forms N r where
  toFun := action N r
  map_add' f g := by
    ext w
    simp [action_apply,add_mul]
  map_smul' c f := by
    ext w
    simp [action_apply,mul_assoc]

private theorem measurable_square {N r : ℕ} (f : Forms N r) : Measurable (quotientSquare f) :=
  measurable_from_quotient.mpr
    (petersson_continuous _ (ModularFormClass.holo f).continuous (ModularFormClass.holo f).continuous).measurable

private theorem integral_square (N r : ℕ) [NeZero N] (f : Forms N r) :
    (∫ q,quotientSquare f q ∂carrierPushforward N)=inner ℂ f f := by
  rw [carrierPushforward,cellPushforward,integral_map (orbitProjection_measurable N).aemeasurable
    (measurable_square f).aestronglyMeasurable,inner_integral] <;> rfl

private theorem density (N r : ℕ) [NeZero N] (f : Forms N r) :
    quotientSquare (action N r f)=quotientSquare f ∘ quotientFricke N (NeZero.pos N) := by
  funext q
  refine Quotient.inductionOn q (fun w => ?_)
  change petersson (2*(r:ℤ)) (action N r f) (action N r f) w =
    petersson (2*(r:ℤ)) f f (frickeSL N (NeZero.pos N) • w)
  rw [action_function,petersson_slash]
  simp [W,UpperHalfPlane.σ]

theorem action_norm (N r : ℕ) [NeZero N] (f : Forms N r) : ‖action N r f‖=‖f‖ := by
  have I : inner ℂ (action N r f) (action N r f)=inner ℂ f f := by
    rw [←integral_square N r (action N r f),←integral_square N r f,density]
    have T := integral_map (μ:=carrierPushforward N)
      (quotientFricke_measurable N (NeZero.pos N)).aemeasurable (measurable_square f).aestronglyMeasurable
    rw [quotientFricke_map_measure] at T
    exact T.symm
  have sq := congrArg Complex.re I
  simp only [inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow,Complex.ofReal_re] at sq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp sq

def frickeIsometry (N r : ℕ) [NeZero N] : Forms N r →ₗᵢ[ℂ] Forms N r where
  toLinearMap := actionLinear N r
  norm_map' := action_norm N r

def frickeEquiv (N r : ℕ) [NeZero N] : Forms N r ≃ₗᵢ[ℂ] Forms N r :=
  LinearIsometryEquiv.ofSurjective (frickeIsometry N r)
    (LinearMap.surjective_of_injective (f:=(frickeIsometry N r).toLinearMap) (frickeIsometry N r).injective)

end ImbalancedChen.Part3.OriginalHolomorphicFrickeBasis20261113
end
