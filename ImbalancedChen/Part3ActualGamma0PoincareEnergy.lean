import ImbalancedChen.Part3ActualGamma0PoincareGreen
import ImbalancedChen.Part3OneCompactDirichletGreen
import ImbalancedChen.Part3ActualPoincareDirichletTrace
import ImbalancedChen.Part3Gamma0SmoothCoreFinitePoincareRepresentation

/-!
# Actual Gamma0 quotient Dirichlet energy and core nonnegativity

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The literal hyperbolic first-gradient density of two actual Poincare
functions descends to the actual orbit quotient. Its L1 property and
integral are derived from the compact first-gradient seed, actual trace
identity, and complex L1 unfolding. One-compact Dirichlet Green therefore
identifies the actual quotient operator pairing with this density.

For a whole finite family the diagonal density is a sum of gradient
squares, retaining all cross terms of the family. The proved simultaneous
finite-family input/output representation then gives nonnegativity on
EVERY vector of the actual smoothCore, without a positivity premise.
-/

namespace ImbalancedChen.Part3.ActualGamma0PoincareEnergy20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.ActualTensorPoincareMaassJoin20261025a
open ImbalancedChen.Part3.ActualGamma0PoincareGreen20261025a
open ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a
open ImbalancedChen.Part3.ActualPoincareDirichletTrace20261025a
open ImbalancedChen.Part3.OneCompactDirichletGreen20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0SmoothCoreFinitePoincareRepresentation20261025a

/-- The actual compact first-gradient seed paired with the full, generally
noncompact, second automorphic function. -/
def compactEnergySeed (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (z : UpperHalfPlane) : ℂ :=
  hyperbolicChartDirichlet (extendUpper (finiteCoreFunction s T))
    (extendUpper (finiteCompactTensorPoincare N t U)) (z.re,z.im)

/-- The literal hyperbolic gradient density of the two actual Poincare
functions, before quotient descent. -/
def poincareEnergyH (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (z : UpperHalfPlane) : ℂ :=
  hyperbolicChartDirichlet (extendUpper (finiteCompactTensorPoincare N s T))
    (extendUpper (finiteCompactTensorPoincare N t U)) (z.re,z.im)

theorem compactEnergySeed_integrable (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    Integrable (compactEnergySeed N s T t U) (volume : Measure UpperHalfPlane) := by
  have hi := integrable_finsetSum s (fun i _ => tensorDirichlet_H_integrable
    (T i) (extendUpper (finiteCompactTensorPoincare N t U))
    (finiteCompactTensorPoincare_contDiffOn_chart N t U))
  convert hi using 1
  funext z
  simp only [compactEnergySeed, extendUpper_finiteCoreFunction,
    hyperbolicChartDirichlet, chartDirichlet_finite_seed_eq_sum, Finset.mul_sum]

/-- Actual local finite differentiation and actual Mobius covariance,
with no assumed derivative-series identity. -/
theorem poincareEnergyH_eq_trace (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (z : UpperHalfPlane) :
    poincareEnergyH N s T t U z = complexSeedTrace N (compactEnergySeed N s T t U) z :=
  actualPoincare_hyperbolicDirichlet_eq_complexSeedTrace N s T
    (finiteCompactTensorPoincare N t U)
    (finiteCompactTensorPoincare_contDiffOn_chart N t U)
    (finiteCompactTensorPoincare_gamma0_invariant N t U) z

theorem poincareEnergyH_gamma0_invariant (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    poincareEnergyH N s T t U (γ • z) = poincareEnergyH N s T t U z := by
  rw [poincareEnergyH_eq_trace, poincareEnergyH_eq_trace]
  exact compactSeedTrace_gamma0_invariant N _ γ z

/-- A genuine orbit lift of the actual gradient density, not a new
abstract energy field or a section-dependent gradient. -/
def quotientPoincareEnergy (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (poincareEnergyH N s T t U) (by
    intro z w hzw
    obtain ⟨γ,hγ⟩ := MulAction.orbitRel_apply.mp hzw
    rw [← hγ]
    exact poincareEnergyH_gamma0_invariant N s T t U γ w)

@[simp] theorem quotientPoincareEnergy_projection (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (z : UpperHalfPlane) :
    quotientPoincareEnergy N s T t U (orbitProjection N z) =
      poincareEnergyH N s T t U z := rfl

theorem quotientPoincareEnergy_ae_eq_complex (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    quotientPoincareEnergy N s T t U =ᵐ[carrierPushforward N]
      complexPoincare N (compactEnergySeed N s T t U) := by
  rw [← reducedProjection_map_measure N,
    (reducedProjection_measurableEmbedding N).ae_map_iff]
  apply Eventually.of_forall
  intro z
  rw [complexPoincare_projection]
  exact poincareEnergyH_eq_trace N s T t U z

/-- L1 for the actual quotient mixed gradient, proved from the compact
seed and true complex unfolding rather than supplied as an energy bound. -/
theorem quotientPoincareEnergy_integrable (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    Integrable (quotientPoincareEnergy N s T t U) (carrierPushforward N) :=
  (complexPoincare_integrable N _ (compactEnergySeed_integrable N s T t U)).congr
    (quotientPoincareEnergy_ae_eq_complex N s T t U).symm

theorem quotientPoincareEnergy_unfolding (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    (∫ q, quotientPoincareEnergy N s T t U q ∂carrierPushforward N) =
      ∫ z : UpperHalfPlane, compactEnergySeed N s T t U z := by
  calc
    _ = ∫ q, complexPoincare N (compactEnergySeed N s T t U) q ∂carrierPushforward N :=
      integral_congr_ae (quotientPoincareEnergy_ae_eq_complex N s T t U)
    _ = _ := complex_poincare_unfolding N _ (compactEnergySeed_integrable N s T t U)

/-- Actual Gamma0 quotient Dirichlet Green equality. The right side is
the literal orbit-descended y-squared coordinate gradient product. -/
theorem actual_quotient_poincare_energy (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (quotientTensorPoincareL2 N s T) (quotientTensorLaplacianPoincareL2 N t U) =
      ∫ q, quotientPoincareEnergy N s T t U q ∂carrierPushforward N := by
  rw [quotient_input_output_inner_eq_integral]
  calc
    _ = ∫ q, star (complexPoincare N (finiteCoreFunction s T) q) *
        complexPoincare N (finiteCoreLaplacian t U) q ∂carrierPushforward N := by
      apply integral_congr_ae
      filter_upwards [quotientTensorPoincare_ae_eq_complex N s T] with q hq
      rw [hq]
      rfl
    _ = ∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) *
        complexSeedTrace N (finiteCoreLaplacian t U) z :=
      compact_C0_pair_unfolding N _ _ (continuous_finiteCoreFunction s T)
        (finiteCoreLaplacian_continuous t U)
        (finiteCompactTensorSupportK_isCompact s T) (finiteCompactTensorSupportK_isCompact t U)
        (finiteCoreFunction_support_subset s T) (finiteCoreLaplacian_support_subset t U)
    _ = ∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) *
        upperMaass (finiteCompactTensorPoincare N t U) z := by
      rw [upperMaass_finiteCompactTensorPoincare_eq_trace]
    _ = ∫ z : UpperHalfPlane, compactEnergySeed N s T t U z :=
      upperMaass_one_compact_finite_seed_dirichlet s T
        (finiteCompactTensorPoincare N t U)
        (finiteCompactTensorPoincare_contDiffOn_chart N t U)
    _ = _ := (quotientPoincareEnergy_unfolding N s T t U).symm

/-- The diagonal contains the gradient of the WHOLE actual finite sum;
all cross terms are retained before taking its nonnegative square. -/
theorem quotientPoincareEnergy_self_re_nonneg (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (q : Gamma0OrbitSpace N) :
    0 ≤ (quotientPoincareEnergy N s T s T q).re := by
  refine Quotient.inductionOn q (fun z => ?_)
  exact hyperbolicChartDirichlet_self_re_nonneg
    (extendUpper (finiteCompactTensorPoincare N s T)) (z.re,z.im)

theorem actual_quotient_poincare_nonneg (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    0 ≤ (inner ℂ (quotientTensorPoincareL2 N s T)
      (quotientTensorLaplacianPoincareL2 N s T)).re := by
  rw [actual_quotient_poincare_energy]
  rw [← integral_re (quotientPoincareEnergy_integrable N s T s T)]
  exact integral_nonneg (quotientPoincareEnergy_self_re_nonneg N s T)

/-- Nonnegativity on the entire actual quotient smooth core follows
from a simultaneous finite-family input/output representation. It is
not inferred from nonnegativity only on individual generators. -/
theorem actualCoreLaplacian_nonneg (N : ℕ) [NeZero N] (u : smoothCore N) :
    0 ≤ (inner ℂ (u : QuotientL2 N) (actualCoreLaplacian N u)).re := by
  obtain ⟨n,T,hInput,hOutput⟩ := exists_finite_input_output_family N u
  rw [hInput,hOutput]
  exact actual_quotient_poincare_nonneg N Finset.univ (fun i => (T i).toCompactTensor)

end
end ImbalancedChen.Part3.ActualGamma0PoincareEnergy20261025a
