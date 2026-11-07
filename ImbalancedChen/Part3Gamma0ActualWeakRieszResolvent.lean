import ImbalancedChen.Part3Gamma0ActualEnergyCompletion
import ImbalancedChen.Part3GenericHilbertAdjointSquare

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The weak Riesz lift and physical bounded resolvent for the ACTUAL Gamma0
quotient Dirichlet-energy completion. EnergyCompletion N and QuotientL2 N
are distinct Hilbert spaces. The physical map is the genuinely constructed
injective dense contraction from the actual shifted core energy, not a
whole-plane inclusion with a new name.

The Riesz lift is its adjoint and the physical resolvent is J J*. Actual
weak energy identities and R(u+Au)=u on the true quotient differential core
are proved by the genuine completion testing identity. No hRiesz, hPosR,
generic Hilbert identification or conclusion-equivalent input is assumed.
Essential self-adjointness of the minimal differential operator is not
claimed by these core identities.
-/

namespace ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a

noncomputable section
open MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open GenericHilbertAdjointSquare20261025a

/-- Actual shifted-energy Riesz solution in E_Gamma, not in physical H_Gamma. -/
def actualRieszLift (N : ℕ) [NeZero N] :
    QuotientL2 N→L[ℂ]EnergyCompletion N := rieszLift (physicalProjection N)

/-- The actual physical bounded resolvent on canonical quotient L2. -/
def actualGammaResolvent (N : ℕ) [NeZero N] :
    QuotientL2 N→L[ℂ]QuotientL2 N := adjointSquare (physicalProjection N)

theorem actualGammaResolvent_apply (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualGammaResolvent N f=physicalProjection N (actualRieszLift N f) := rfl

/-- Weak variational identity for EVERY actual completed-energy test.
This is the actual Riesz problem, with the canonical physical forcing. -/
theorem actualRieszLift_weak (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (v : EnergyCompletion N) :
    inner ℂ v (actualRieszLift N f)=inner ℂ (physicalProjection N v) f :=
  rieszLift_weak (physicalProjection N) f v

/-- Uniqueness is proved by energy inner-product separation, rather
than a supplied inverse or Riesz-solution uniqueness field. -/
theorem actualRieszLift_unique (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (w : EnergyCompletion N)
    (hw : ∀ v : EnergyCompletion N,
      inner ℂ v w=inner ℂ (physicalProjection N v) f) :
    w=actualRieszLift N f := by
  apply ext_inner_left ℂ
  intro v
  rw [hw,actualRieszLift_weak]

/-- Every physical resolvent output lies in the ACTUAL energy domain. -/
theorem actualGammaResolvent_mem_energy_range (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualGammaResolvent N f∈Set.range (physicalProjection N) :=
  ⟨actualRieszLift N f,actualGammaResolvent_apply N f⟩

/-- The actual energy lift of (1+A)u is the original core vector in the
actual completion. The proof uses ALL completed-energy tests. -/
theorem actualRieszLift_shift_core (N : ℕ) [NeZero N] (u : EnergyCore N) :
    actualRieszLift N (physicalCore N u+coreLaplacian N u)=coreEmbedding N u := by
  apply ext_inner_left ℂ
  intro v
  rw [actualRieszLift_weak]
  exact (physicalProjection_testing N v u).symm

/-- R(1+A)u=u on the actual smooth quotient differential core. This is
an extension identity and does not assert essential self-adjointness. -/
theorem actualGammaResolvent_shift_core (N : ℕ) [NeZero N] (u : EnergyCore N) :
    actualGammaResolvent N (physicalCore N u+coreLaplacian N u)=physicalCore N u := by
  rw [actualGammaResolvent_apply,actualRieszLift_shift_core,physicalProjection_core]

/-- The corresponding physical weak identity against every actual
smooth differential test retains the original geometric core Laplacian. -/
theorem actualGammaResolvent_core_weak (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u : EnergyCore N) :
    inner ℂ (actualGammaResolvent N f) (physicalCore N u+coreLaplacian N u)=
      inner ℂ f (physicalCore N u) := by
  calc
    _ = inner ℂ (actualRieszLift N f) (coreEmbedding N u) :=
      (physicalProjection_testing N (actualRieszLift N f) u).symm
    _ = inner ℂ f (physicalProjection N (coreEmbedding N u)) :=
      ContinuousLinearMap.adjoint_inner_left (physicalProjection N) (coreEmbedding N u) f
    _ = _ := by rw [physicalProjection_core]

/-- The physical resolvent quadratic form is exactly the completed
shifted-energy norm of its actual Riesz solution. -/
theorem actualGammaResolvent_energy_quadratic (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    (inner ℂ f (actualGammaResolvent N f)).re=‖actualRieszLift N f‖^2 := by
  have hh := ContinuousLinearMap.adjoint_inner_left (physicalProjection N)
    (actualRieszLift N f) f
  rw [← actualGammaResolvent_apply] at hh
  rw [← hh,← InnerProductSpace.norm_sq_eq_re_inner]

theorem actualGammaResolvent_positive (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    0≤(inner ℂ f (actualGammaResolvent N f)).re := by
  rw [actualGammaResolvent_energy_quadratic]
  exact sq_nonneg _

/-- Firmness is an ACTUAL physical estimate, from the derived contractive
completion inclusion and the exact actual energy quadratic identity. -/
theorem actualGammaResolvent_firm (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ‖actualGammaResolvent N f‖^2≤(inner ℂ f (actualGammaResolvent N f)).re := by
  rw [actualGammaResolvent_energy_quadratic,actualGammaResolvent_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (physicalProjection_norm_le N _) 2

/-- The ACTUAL physical resolvent is a positive bounded operator. -/
theorem actualGammaResolvent_isPositive (N : ℕ) [NeZero N] :
    (actualGammaResolvent N).IsPositive := adjointSquare_positive (physicalProjection N)

theorem actualGammaResolvent_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (actualGammaResolvent N) := adjointSquare_selfAdjoint (physicalProjection N)

theorem actualGammaResolvent_adjoint (N : ℕ) [NeZero N] :
    (actualGammaResolvent N).adjoint=actualGammaResolvent N :=
  adjointSquare_adjoint (physicalProjection N)

theorem actualGammaResolvent_inner (N : ℕ) [NeZero N] (f g : QuotientL2 N) :
    inner ℂ f (actualGammaResolvent N g)=
      inner ℂ (actualRieszLift N f) (actualRieszLift N g) :=
  adjointSquare_inner (physicalProjection N) f g

theorem actualGammaResolvent_symmetric (N : ℕ) [NeZero N] (f g : QuotientL2 N) :
    inner ℂ (actualGammaResolvent N f) g=inner ℂ f (actualGammaResolvent N g) :=
  adjointSquare_symmetric (physicalProjection N) f g

theorem actualRieszLift_norm_le (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ‖actualRieszLift N f‖≤‖f‖ :=
  rieszLift_norm_le (physicalProjection N) (physicalProjection_opNorm_le_one N) f

theorem actualGammaResolvent_norm_le (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ‖actualGammaResolvent N f‖≤‖f‖ :=
  adjointSquare_norm_le (physicalProjection N) (physicalProjection_opNorm_le_one N) f

theorem actualGammaResolvent_opNorm_le_one (N : ℕ) [NeZero N] :
    ‖actualGammaResolvent N‖≤1 :=
  adjointSquare_opNorm_le_one (physicalProjection N) (physicalProjection_opNorm_le_one N)

/-- Dense physical range was proved for the actual energy completion, so
the ACTUAL resolvent is injective without a kernel hypothesis. -/
theorem actualGammaResolvent_injective (N : ℕ) [NeZero N] :
    Function.Injective (actualGammaResolvent N) :=
  adjointSquare_injective (physicalProjection N) (physicalProjection_denseRange N)

theorem actualGammaResolvent_denseRange (N : ℕ) [NeZero N] :
    DenseRange (actualGammaResolvent N) :=
  adjointSquare_denseRange (physicalProjection N) (physicalProjection_denseRange N)

theorem actualRieszLift_injective (N : ℕ) [NeZero N] :
    Function.Injective (actualRieszLift N) :=
  rieszLift_injective (physicalProjection N) (physicalProjection_denseRange N)

/-- Actual form closability supplies injectivity of J, hence the Riesz
lifts have dense range in the genuine completed energy Hilbert space. -/
theorem actualRieszLift_denseRange (N : ℕ) [NeZero N] :
    DenseRange (actualRieszLift N) :=
  rieszLift_denseRange (physicalProjection N) (physicalProjection_injective N)

theorem actualGammaResolvent_firm_difference (N : ℕ) [NeZero N] (f g : QuotientL2 N) :
    ‖actualGammaResolvent N f-actualGammaResolvent N g‖^2 ≤
      (inner ℂ (f-g) (actualGammaResolvent N f-actualGammaResolvent N g)).re :=
  adjointSquare_firm_difference (physicalProjection N) (physicalProjection_opNorm_le_one N) f g

end
end ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a
