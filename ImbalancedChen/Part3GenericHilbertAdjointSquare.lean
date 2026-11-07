import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# Generic Hilbert adjoint-square weak resolvent

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

For any continuous complex-linear map J from a complete energy Hilbert
space E into a complete physical Hilbert space H, the actual adjoint
constructs the weak Riesz lift and R = J J*. Positivity, self-adjointness,
the mixed quadratic identity, contraction and firmness are proved, not
assumed. Dense range of J already suffices for injectivity and dense range
of R; injectivity of J additionally gives dense range of the Riesz lift.

This is generic Hilbert mathematics, with no fixed whole-plane space or
actual Gamma0 completion silently substituted for either E or H. Actual
Gamma0 energy-completion instantiation and unbounded-operator/spectral
constructions are separate modules.
-/

namespace ImbalancedChen.Part3.GenericHilbertAdjointSquare20261025a
noncomputable section

variable {E H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine Hilbert Riesz lift, already a bounded complex-linear map. -/
def rieszLift (J : E →L[ℂ] H) : H →L[ℂ] E := J.adjoint

/-- The genuine bounded complex-linear adjoint square on the physical
space; none of its positivity or self-adjointness properties are inputs. -/
def adjointSquare (J : E →L[ℂ] H) : H →L[ℂ] H := J.comp J.adjoint

@[simp] theorem rieszLift_apply (J : E →L[ℂ] H) (f : H) :
    rieszLift J f = J.adjoint f := rfl

@[simp] theorem adjointSquare_apply (J : E →L[ℂ] H) (f : H) :
    adjointSquare J f = J (rieszLift J f) := rfl

/-- Weak Riesz identity, with the conventional inner product linear in
the second variable. -/
theorem rieszLift_weak (J : E →L[ℂ] H) (f : H) (v : E) :
    inner ℂ v (rieszLift J f) = inner ℂ (J v) f :=
  J.adjoint_inner_right v f

theorem rieszLift_weak_left (J : E →L[ℂ] H) (f : H) (v : E) :
    inner ℂ (rieszLift J f) v = inner ℂ f (J v) :=
  J.adjoint_inner_left v f

/-- The weak problem has the constructed lift as its UNIQUE solution;
there is no Riesz-solution supplier premise. -/
theorem rieszLift_weak_unique (J : E →L[ℂ] H) (f : H) (u : E)
    (hu : ∀ v : E, inner ℂ v u = inner ℂ (J v) f) : u = rieszLift J f := by
  apply ext_inner_left ℂ
  intro v
  exact (hu v).trans (rieszLift_weak J f v).symm

theorem existsUnique_weakSolution (J : E →L[ℂ] H) (f : H) :
    ∃! u : E, ∀ v : E, inner ℂ v u = inner ℂ (J v) f := by
  refine ⟨rieszLift J f, rieszLift_weak J f, ?_⟩
  intro u hu
  exact rieszLift_weak_unique J f u hu

theorem adjointSquare_positive (J : E →L[ℂ] H) : (adjointSquare J).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint J

theorem adjointSquare_selfAdjoint (J : E →L[ℂ] H) : IsSelfAdjoint (adjointSquare J) :=
  (adjointSquare_positive J).isSelfAdjoint

theorem adjointSquare_adjoint (J : E →L[ℂ] H) :
    (adjointSquare J).adjoint = adjointSquare J :=
  (adjointSquare_selfAdjoint J).adjoint_eq

/-- The full mixed identity, not only a real diagonal quadratic form. -/
theorem adjointSquare_inner (J : E →L[ℂ] H) (f g : H) :
    inner ℂ f (adjointSquare J g) = inner ℂ (rieszLift J f) (rieszLift J g) :=
  (J.adjoint_inner_left (rieszLift J g) f).symm

theorem adjointSquare_symmetric (J : E →L[ℂ] H) (f g : H) :
    inner ℂ (adjointSquare J f) g = inner ℂ f (adjointSquare J g) :=
  (adjointSquare_positive J).inner_left_eq_inner_right f g

theorem adjointSquare_quadratic (J : E →L[ℂ] H) (f : H) :
    (inner ℂ f (adjointSquare J f)).re = ‖rieszLift J f‖ ^ 2 := by
  rw [adjointSquare_inner, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_pow, Complex.ofReal_re]

theorem adjointSquare_quadratic_nonneg (J : E →L[ℂ] H) (f : H) :
    0 ≤ (inner ℂ f (adjointSquare J f)).re := by
  rw [adjointSquare_quadratic]
  exact sq_nonneg _

theorem rieszLift_opNorm (J : E →L[ℂ] H) : ‖rieszLift J‖ = ‖J‖ :=
  ContinuousLinearMap.adjoint.norm_map J

theorem map_norm_le_of_opNorm_le_one (J : E →L[ℂ] H) (hJ : ‖J‖ ≤ 1) (u : E) :
    ‖J u‖ ≤ ‖u‖ := by
  calc
    _ ≤ ‖J‖ * ‖u‖ := J.le_opNorm u
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg u)
    _ = _ := one_mul _

theorem rieszLift_norm_le (J : E →L[ℂ] H) (hJ : ‖J‖ ≤ 1) (f : H) :
    ‖rieszLift J f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖rieszLift J‖ * ‖f‖ := (rieszLift J).le_opNorm f
    _ = ‖J‖ * ‖f‖ := by rw [rieszLift_opNorm]
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg f)
    _ = _ := one_mul _

theorem adjointSquare_norm_le_rieszLift (J : E →L[ℂ] H) (hJ : ‖J‖ ≤ 1) (f : H) :
    ‖adjointSquare J f‖ ≤ ‖rieszLift J f‖ :=
  map_norm_le_of_opNorm_le_one J hJ (rieszLift J f)

theorem adjointSquare_norm_le (J : E →L[ℂ] H) (hJ : ‖J‖ ≤ 1) (f : H) :
    ‖adjointSquare J f‖ ≤ ‖f‖ :=
  (adjointSquare_norm_le_rieszLift J hJ f).trans (rieszLift_norm_le J hJ f)

theorem adjointSquare_opNorm_le_one (J : E →L[ℂ] H) (hJ : ‖J‖ ≤ 1) :
    ‖adjointSquare J‖ ≤ 1 := by
  apply (adjointSquare J).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using adjointSquare_norm_le J hJ f

/-- Firmness follows from the contraction J on the CONSTRUCTED energy
lift, not from an assumed resolvent or spectral property. -/
theorem adjointSquare_firm (J : E →L[ℂ] H) (hJ : ‖J‖ ≤ 1) (f : H) :
    ‖adjointSquare J f‖ ^ 2 ≤ (inner ℂ f (adjointSquare J f)).re := by
  rw [adjointSquare_quadratic]
  exact pow_le_pow_left₀ (norm_nonneg _) (adjointSquare_norm_le_rieszLift J hJ f) 2

theorem adjointSquare_firm_difference (J : E →L[ℂ] H) (hJ : ‖J‖ ≤ 1) (f g : H) :
    ‖adjointSquare J f - adjointSquare J g‖ ^ 2 ≤
      (inner ℂ (f - g) (adjointSquare J f - adjointSquare J g)).re := by
  simpa only [map_sub] using adjointSquare_firm J hJ (f - g)

theorem rieszLift_eq_zero_iff (J : E →L[ℂ] H) (hJdense : DenseRange J) (f : H) :
    rieszLift J f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (show Dense (Set.range J) from hJdense).eq_zero_of_inner_left ℂ
    rintro _ ⟨u,rfl⟩
    rw [← J.adjoint_inner_left u f]
    change inner ℂ (rieszLift J f) u = 0
    rw [hf, inner_zero_left]
  · intro hf
    simp [hf]

theorem rieszLift_injective (J : E →L[ℂ] H) (hJdense : DenseRange J) :
    Function.Injective (rieszLift J) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (rieszLift_eq_zero_iff J hJdense (f - g)).mp
  rw [map_sub,hfg,sub_self]

/-- Dense range of J alone suffices: J J* and J* have the same kernel.
No injectivity premise on the original embedding is needed for R. -/
theorem adjointSquare_injective (J : E →L[ℂ] H) (hJdense : DenseRange J) :
    Function.Injective (adjointSquare J) := by
  change Function.Injective (J ∘ J.adjoint)
  exact J.self_comp_adjoint_injective_iff.mpr (rieszLift_injective J hJdense)

theorem adjointSquare_ker (J : E →L[ℂ] H) (hJdense : DenseRange J) :
    (adjointSquare J).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (adjointSquare_injective J hJdense)

/-- The actual range is dense, proved by the orthogonal range/kernel
identity and the self-adjointness already derived from J J*. -/
theorem adjointSquare_denseRange (J : E →L[ℂ] H) (hJdense : DenseRange J) :
    DenseRange (adjointSquare J) := by
  change Dense ((adjointSquare J).range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply (adjointSquare J).range.topologicalClosure_eq_top_iff.mpr
  rw [ContinuousLinearMap.orthogonal_range, adjointSquare_adjoint,
    adjointSquare_ker J hJdense]

/-- Injectivity of the energy embedding additionally gives a dense range
for its adjoint, hence dense approximation by constructed Riesz lifts. -/
theorem rieszLift_denseRange (J : E →L[ℂ] H) (hJinj : Function.Injective J) :
    DenseRange (rieszLift J) := by
  change Dense (J.adjoint.range : Set E)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply J.adjoint.range.topologicalClosure_eq_top_iff.mpr
  rw [ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.adjoint_adjoint,
    show J.ker = ⊥ from LinearMap.ker_eq_bot.mpr hJinj]

end
end ImbalancedChen.Part3.GenericHilbertAdjointSquare20261025a
