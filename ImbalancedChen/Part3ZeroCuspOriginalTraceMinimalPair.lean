import ImbalancedChen.Part3ZeroCuspEffectiveFrickePeriodization
import ImbalancedChen.Part3ZeroCuspActualMaassCovariance
import ImbalancedChen.Part3ZeroCuspActualCompactMinimalEnergy

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The ORIGINAL compact effective-Gamma0 trace, evaluated at literal zeroSL,
descends to the entire actual spatial quotient. Its L2 input and the
zeroSL pullback of its ORIGINAL seed differential output are constructed
without MemLp/domain premises. The derived effective Fricke permutation
and real zeroSL Maass chain identify these two original-trace quotient
objects with the previously constructed pulled-compact-seed native
minimal graph pair. Thus their actual minimal domain and completed
Dirichlet energy relation follow for the original objects themselves.
-/

noncomputable section

namespace ImbalancedChen.Part3.ZeroCuspOriginalTraceMinimalPair20261026b

open Set Filter MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.InfinityZeroActualQuotientGeometricAssembly20261026b
open ImbalancedChen.Part3.ZeroCuspActualSmoothCompactPullback20261026b
open ImbalancedChen.Part3.ZeroCuspActualMaassCovariance20261026b
open ImbalancedChen.Part3.ZeroCuspEffectiveFrickePeriodization20261026b
open ImbalancedChen.Part3.ZeroCuspActualCompactMinimalEnergy20261026b
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a

/-- Original H trace after the actual normalized zero-chart action,
genuinely descended to the full actual Gamma0 orbit quotient. -/
def originalZeroTraceQuotient (N : ℕ) (hN : 0 < N) (f : UpperHalfPlane → ℂ) :
    Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (fun z => complexSeedTrace N f (zeroSL N hN • z)) (by
    intro z w hrel
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hrel
    rw [← hg, zeroSL_intertwines]
    exact compactSeedTrace_gamma0_invariant N f (frickeGamma0 N g) (zeroSL N hN • w))

theorem originalZeroTraceQuotient_projection (N : ℕ) [NeZero N]
    (hN : 0 < N) (f : UpperHalfPlane → ℂ) (z : reducedCarrier N) :
    originalZeroTraceQuotient N hN f (reducedProjection N z) =
      complexSeedTrace N f (zeroSL N hN • z) := rfl

/-- The existing canonical reduced section is conull. The exact effective
Fricke permutation identifies the ORIGINAL zero trace with actual
periodization of the literal pulled seed on that actual quotient. -/
theorem originalZeroTraceQuotient_ae_pulledPoincare (N : ℕ) [NeZero N]
    (hN : 0 < N) (f : UpperHalfPlane → ℂ) :
    originalZeroTraceQuotient N hN f =ᵐ[carrierPushforward N]
      complexPoincare N (zeroSeedPullback N hN f) := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  rw [originalZeroTraceQuotient_projection, complexPoincare_projection,
    complexSeedTrace_zeroPullback]

theorem zeroCompactInput_ae_originalTrace (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    (zeroCompactInput N hN f hfc hf : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      originalZeroTraceQuotient N hN f :=
  (zeroCompactInput_ae N hN f hfc hf).trans
    (originalZeroTraceQuotient_ae_pulledPoincare N hN f).symm

/-- Genuine real differential covariance identifies the output with the
ORIGINAL seed differential trace at zeroSL, not an unspecified output. -/
theorem zeroCompactOutput_ae_originalTrace (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    (zeroCompactOutput N hN f hfc hf : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      originalZeroTraceQuotient N hN (upperMaass f) := by
  have hdiff : upperMaass (zeroSeedPullback N hN f) = zeroSeedPullback N hN (upperMaass f) :=
    funext (upperMaass_zeroSeedPullback N hN f (hf.of_le (by simp)))
  have hout := zeroCompactOutput_ae N hN f hfc hf
  rw [hdiff] at hout
  exact hout.trans (originalZeroTraceQuotient_ae_pulledPoincare N hN (upperMaass f)).symm

theorem originalZeroTraceQuotient_memLp_two (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    MemLp (originalZeroTraceQuotient N hN f) 2 (carrierPushforward N) :=
  (Lp.memLp (zeroCompactInput N hN f hfc hf)).congr (zeroCompactInput_ae_originalTrace N hN f hfc hf)

theorem originalZeroOutput_memLp_two (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    MemLp (originalZeroTraceQuotient N hN (upperMaass f)) 2 (carrierPushforward N) :=
  (Lp.memLp (zeroCompactOutput N hN f hfc hf)).congr (zeroCompactOutput_ae_originalTrace N hN f hfc hf)

def originalZeroInputL2 (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) : Lp ℂ 2 (carrierPushforward N) :=
  (originalZeroTraceQuotient_memLp_two N hN f hfc hf).toLp (originalZeroTraceQuotient N hN f)

def originalZeroOutputL2 (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) : Lp ℂ 2 (carrierPushforward N) :=
  (originalZeroOutput_memLp_two N hN f hfc hf).toLp (originalZeroTraceQuotient N hN (upperMaass f))

theorem originalZeroInputL2_eq_constructed (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    originalZeroInputL2 N hN f hfc hf = zeroCompactInput N hN f hfc hf :=
  Lp.ext ((originalZeroTraceQuotient_memLp_two N hN f hfc hf).coeFn_toLp.trans
    (zeroCompactInput_ae_originalTrace N hN f hfc hf).symm)

theorem originalZeroOutputL2_eq_constructed (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    originalZeroOutputL2 N hN f hfc hf = zeroCompactOutput N hN f hfc hf :=
  Lp.ext ((originalZeroOutput_memLp_two N hN f hfc hf).coeFn_toLp.trans
    (zeroCompactOutput_ae_originalTrace N hN f hfc hf).symm)

/-- Native MINIMAL differential graph for the original-trace objects.
No abstract graph membership or caller-supplied pairing is assumed. -/
theorem originalZero_pair_mem_minimalGraph (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    (originalZeroInputL2 N hN f hfc hf, originalZeroOutputL2 N hN f hfc hf) ∈
      (actualClosedGammaMaass N).graph := by
  rw [originalZeroInputL2_eq_constructed, originalZeroOutputL2_eq_constructed]
  exact zeroCompact_pair_mem_minimalGraph N hN f hfc hf

theorem originalZeroInput_mem_minimalDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    originalZeroInputL2 N hN f hfc hf ∈ (actualClosedGammaMaass N).domain :=
  LinearPMap.mem_domain_iff.mpr
    ⟨originalZeroOutputL2 N hN f hfc hf, originalZero_pair_mem_minimalGraph N hN f hfc hf⟩

/-- Actual completed Dirichlet relation for the original compact trace
and the zero-chart pullback of its original differential output. -/
theorem exists_originalZero_energy_lift (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ∃ e : EnergyCompletion N,
      physicalProjection N e = originalZeroInputL2 N hN f hfc hf ∧
      (∀ d : EnergyCompletion N, actualDirichletPair N d e =
        inner ℂ (physicalProjection N d) (originalZeroOutputL2 N hN f hfc hf)) ∧
      actualDirichletPair N e e =
        inner ℂ (originalZeroInputL2 N hN f hfc hf) (originalZeroOutputL2 N hN f hfc hf) := by
  rw [originalZeroInputL2_eq_constructed, originalZeroOutputL2_eq_constructed]
  exact exists_zeroCompact_energy_lift N hN f hfc hf

end ImbalancedChen.Part3.ZeroCuspOriginalTraceMinimalPair20261026b
