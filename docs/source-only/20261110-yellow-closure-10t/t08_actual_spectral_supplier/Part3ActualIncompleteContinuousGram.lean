import ImbalancedChen.Part3ActualIncompleteCriticalColumns

/-! The exact double-cover factor on the physical critical line. Curve
pairings are conjugate linear in their spatial Poincaré tests. Both
halves of the t-line and every native incoming cusp are retained. -/
namespace ImbalancedChen.Part3.ActualIncompleteContinuousGram20261110

noncomputable section
open Set MeasureTheory Complex Matrix
open scoped UpperHalfPlane MatrixGroups BigOperators Classical
open ActualCharacterCuspExpansion20261110 ActualCriticalScatteringUnitarity20261110
open SmoothZeroHeightSeedProfiles20261026b ActualIncompleteEisensteinGram20261110
open ActualIncompleteCriticalColumns20261110

private theorem reflected_test (N : ℕ) [NeZero N] (h : SL(2,ℤ)) (ψ : SmoothHeightSeed)
    (c : CuspRowClass N) (t : ℝ) :
    (∑ a,star (scatteringMatrix N t a c)*boundaryColumn N h ψ a t) = boundaryColumn N h ψ c (-t) := by
  classical
  let S := scatteringMatrix N t
  let b := frameIndex N h
  have Z : ∑ a, star (S a c)*S a b = if c=b then (1 : ℂ) else 0 := by
    simpa only [S,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using
      congrArg (fun M : Matrix (CuspRowClass N) (CuspRowClass N) ℂ => M c b)
        (actual_critical_scattering_unitary N t).2
  have C : star (S b c) = scatteringMatrix N (-t) c b :=
    (congrArg (fun M : Matrix (CuspRowClass N) (CuspRowClass N) ℂ => M c b) (reflected_adjoint N t)).symm
  calc
    _ = star (S b c)*star (wave ψ t) + (∑ a,star (S a c)*S a b)*star (wave ψ (-t)) := by
      simp only [boundaryColumn,mul_add,Finset.sum_add_distrib,mul_ite,mul_zero]
      rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ _),Finset.sum_mul]
      apply congrArg₂ (·+·) rfl
      exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)
    _ = _ := by rw [Z,C]; by_cases e : c=b <;> simp [boundaryColumn,b,e,ite_mul,add_comm]

def physicalProduct (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (t : ℝ) : ℂ :=
  ∑ a : CuspRowClass N,boundaryColumn N h ψ a t*star (boundaryColumn N g φ a t)

theorem physicalProduct_integrable (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    Integrable (physicalProduct N h g ψ φ) :=
  integrable_finsetSum _ (fun a _ => (boundaryColumn_L2 N h ψ a).integrable_mul (boundaryColumn_L2 N g φ a).star)

theorem two_heights (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (t : ℝ) :
    physicalProduct N h g ψ φ t = gramIntegrand N g h ψ φ (1/2) t + gramIntegrand N g h ψ φ (1/2) (-t) := by
  classical
  let c := frameIndex N g
  let V := fun a => boundaryColumn N h ψ a t
  have q (a : CuspRowClass N) : star (boundaryColumn N g φ a t) =
      (if a=c then wave φ t else 0) + star (scatteringMatrix N t a c)*wave φ (-t) := by
    by_cases e : a=c <;> simp [boundaryColumn,c,e,Complex.star_def]
  calc
    _ = V c*wave φ t + (∑ a,star (scatteringMatrix N t a c)*V a)*wave φ (-t) := by
      simp only [physicalProduct,q,mul_add,Finset.sum_add_distrib,mul_ite,mul_zero,Finset.sum_ite_eq',
        Finset.mem_univ,if_true,Finset.sum_mul]
      apply congrArg₂ (·+·) rfl
      exact Finset.sum_congr rfl (fun a _ => by dsimp [V]; ring)
    _ = _ := by
      dsimp only [V]
      rw [reflected_test,gram_critical_eq,gram_critical_eq]
      dsimp only [c]
      ring

/-- With the manuscript's physical pair orientation, the full two-sided
continuous product has density dt/(4π). It equals the one-sided-in-the-
functional-equation Mellin integrand on the full line with dt/(2π). -/
theorem full_line_normalization (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    (4*Real.pi)⁻¹ • (∫ t : ℝ,physicalProduct N h g ψ φ t) =
      (2*Real.pi)⁻¹ • ∫ t : ℝ,gramIntegrand N g h ψ φ (1/2) t := by
  let G := gramIntegrand N g h ψ φ (1/2)
  have H : Integrable G := gram_critical_integrable N g h ψ φ
  have J : Integrable (fun t : ℝ => G (-t)) := H.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have K : (∫ t : ℝ,G (-t)) = ∫ t : ℝ,G t :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp (Homeomorph.neg ℝ).measurableEmbedding G
  have E : (∫ t : ℝ,physicalProduct N h g ψ φ t) = (∫ t,G t)+(∫ t,G t) := by
    simp_rw [two_heights]
    change (∫ t : ℝ,G t+G (-t)) = _
    rw [integral_add H J,K]
  rw [E]
  simp only [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end
end ImbalancedChen.Part3.ActualIncompleteContinuousGram20261110
