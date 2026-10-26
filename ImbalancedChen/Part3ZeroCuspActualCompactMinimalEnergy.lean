import ImbalancedChen.Part3ZeroCuspActualSmoothCompactPullback
import ImbalancedChen.Part3GammaFiniteTensorGraphCore

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

A genuinely constructed compact smooth zero-chart pullback seed has an
actual Gamma0 quotient input/output L2 pair, with output the existing
upperMaass of that pulled seed. The real zeroSL smoothness and support
theorems supply all transformed regularity and compactness. Constructive
finite-tensor graph closure proves native minimal-domain membership,
and genuine Friedrichs inclusion gives the actual completed Dirichlet
relation and energy identity. No domain/graph/form membership, prescribed
pairing, or sigma0 differential covariance is a caller premise.
-/

noncomputable section

namespace ImbalancedChen.Part3.ZeroCuspActualCompactMinimalEnergy20261026b

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.ZeroCuspActualSmoothCompactPullback20261026b
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.GammaCompactSeedGraphTransport20261026a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.GammaFiniteTensorGraphCore20261026a
open ImbalancedChen.Part3.Gamma0ActualMinimalFriedrichsInclusion20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a

/-- Explicit compact support container in the actual zero chart. -/
def zeroCompactSupport (N : ℕ) (hN : 0 < N) (f : UpperHalfPlane → ℂ) : Set UpperHalfPlane :=
  (fun z => zeroSL N hN • z) '' tsupport f

theorem zeroCompactSupport_isCompact (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f) :
    IsCompact (zeroCompactSupport N hN f) :=
  hfc.image (zeroSL_action_continuous N hN)

theorem zeroCompactSupport_contains_support (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) :
    Function.support (zeroSeedPullback N hN f) ⊆ zeroCompactSupport N hN f :=
  zeroSeedPullback_support_subset N hN f (tsupport f) (subset_tsupport f)

def zeroCompactInput (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) : Lp ℂ 2 (carrierPushforward N) :=
  compactInput N (zeroSeedPullback N hN f)
    ((zeroSeedPullback_nativeCinfty N hN f hf).of_le (by simp))
    (zeroCompactSupport N hN f) (zeroCompactSupport_isCompact N hN f hfc)
    (zeroCompactSupport_contains_support N hN f)

/-- The output is the actual native differential of the actual pulled
seed. No unproved commutation with sigma0 is used to change this seed. -/
def zeroCompactOutput (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) : Lp ℂ 2 (carrierPushforward N) :=
  compactOutput N (zeroSeedPullback N hN f)
    ((zeroSeedPullback_nativeCinfty N hN f hf).of_le (by simp))
    (zeroCompactSupport N hN f) (zeroCompactSupport_isCompact N hN f hfc)
    (zeroCompactSupport_contains_support N hN f)

theorem zeroCompactInput_ae (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    (zeroCompactInput N hN f hfc hf : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (zeroSeedPullback N hN f) :=
  compactInput_ae N (zeroSeedPullback N hN f) _ (zeroCompactSupport N hN f)
    (zeroCompactSupport_isCompact N hN f hfc) (zeroCompactSupport_contains_support N hN f)

theorem zeroCompactOutput_ae (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    (zeroCompactOutput N hN f hfc hf : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass (zeroSeedPullback N hN f)) :=
  compactOutput_ae N (zeroSeedPullback N hN f) _ (zeroCompactSupport N hN f)
    (zeroCompactSupport_isCompact N hN f hfc) (zeroCompactSupport_contains_support N hN f)

/-- Native minimal closed differential graph, supplied by true compact
smooth finite-tensor approximation after the real zero-chart construction. -/
theorem zeroCompact_pair_mem_minimalGraph (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    (zeroCompactInput N hN f hfc hf, zeroCompactOutput N hN f hfc hf) ∈
      (actualClosedGammaMaass N).graph :=
  compact_smooth_seed_ae_pair_mem_minimalGraph N (zeroSeedPullback N hN f)
    (zeroSeedPullback_hasCompactSupport N hN f hfc) (zeroSeedPullback_nativeCinfty N hN f hf)
    (zeroCompactInput N hN f hfc hf) (zeroCompactOutput N hN f hfc hf)
    (zeroCompactInput_ae N hN f hfc hf) (zeroCompactOutput_ae N hN f hfc hf)

theorem zeroCompactInput_mem_minimalDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    zeroCompactInput N hN f hfc hf ∈ (actualClosedGammaMaass N).domain :=
  LinearPMap.mem_domain_iff.mpr
    ⟨zeroCompactOutput N hN f hfc hf, zeroCompact_pair_mem_minimalGraph N hN f hfc hf⟩

theorem zeroCompact_pair_mem_friedrichsGraph (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    (zeroCompactInput N hN f hfc hf, zeroCompactOutput N hN f hfc hf) ∈
      (actualGammaFriedrichs N).graph := by
  have hg := zeroCompact_pair_mem_minimalGraph N hN f hfc hf
  rw [actualClosedGammaMaass_graph_eq] at hg
  exact closedGammaGraph_le_friedrichsGraph N hg

/-- Actual completed form membership and Dirichlet energy, with the
genuine quotient periodization and native differential output. -/
theorem exists_zeroCompact_energy_lift (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ∃ e : EnergyCompletion N,
      physicalProjection N e = zeroCompactInput N hN f hfc hf ∧
      (∀ d : EnergyCompletion N, actualDirichletPair N d e =
        inner ℂ (physicalProjection N d) (zeroCompactOutput N hN f hfc hf)) ∧
      actualDirichletPair N e e =
        inner ℂ (zeroCompactInput N hN f hfc hf) (zeroCompactOutput N hN f hfc hf) := by
  obtain ⟨e, he, ht⟩ := (actualGammaFriedrichs_mem_graph_iff_formPair N).mp
    (zeroCompact_pair_mem_friedrichsGraph N hN f hfc hf)
  refine ⟨e, he, ht, ?_⟩
  simpa only [he] using ht e

theorem zeroCompactInput_mem_actualFormDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    zeroCompactInput N hN f hfc hf ∈ actualEnergyFormDomain N := by
  obtain ⟨e, he, _ht, _he⟩ := exists_zeroCompact_energy_lift N hN f hfc hf
  exact ⟨e, he⟩

end ImbalancedChen.Part3.ZeroCuspActualCompactMinimalEnergy20261026b
